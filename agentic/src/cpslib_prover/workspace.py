"""Prepare sanitized Lean projects and record their trusted source snapshot."""

import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

from .dependencies import copy_sources, source_files, task_path
from .domain import BenchmarkError, Problem, Workspace
from .process import capture, checked, note

AGENTIC_ROOT = Path(__file__).resolve().parents[2]
REPO_ROOT = AGENTIC_ROOT.parent
PROJECT_FILES = (
    "CPSLib.lean",
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "AGENTS.md",
    ".gitignore",
    "benchmark-metadata.txt",
)


def load_problem(path: Path) -> Problem:
    if not path.is_dir():
        raise BenchmarkError(f"problem directory not found: {path}")
    for name in ("Challenge.lean", "config.json"):
        if not (path / name).is_file():
            raise BenchmarkError(f"missing {name} in {path}")
    return Problem(path)


def load_workspace(path: Path) -> Workspace:
    required = (
        ".agents/skills/cpslib-prover/SKILL.md",
        "AGENTS.md",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "CPSLib/Core",
        "CPSLib/Tactic",
        ".lake/packages",
    )
    for name in required:
        entry = path / name
        if not entry.exists() and not entry.is_symlink():
            raise BenchmarkError(
                f"not a prepared benchmark sandbox; missing {entry}"
            )
    metadata = dict(
        line.split("=", 1)
        for line in (path / "benchmark-metadata.txt").read_text().splitlines()
        if "=" in line
    )
    task = Path(metadata.get("task", ""))
    if (
        task.is_absolute()
        or ".." in task.parts
        or task.parts[:2] != ("CPSLib", "Examples")
    ):
        raise BenchmarkError("invalid workspace task path")
    workspace = Workspace(path, task)
    for entry in (workspace.solution, workspace.config):
        if not entry.is_file() or entry.resolve() != entry:
            raise BenchmarkError(f"missing or symlinked task file: {entry}")
    return workspace


def new_directory(path: Path) -> None:
    if path.exists() or path.is_symlink():
        raise BenchmarkError(f"output already exists: {path}")
    path.mkdir(parents=True)


def source_fingerprint(problem: Problem) -> str:
    paths = [
        str(path.relative_to(REPO_ROOT))
        for directory in ("CPSLib/Core", "CPSLib/Tactic")
        for path in (REPO_ROOT / directory).rglob("*.lean")
        if path.is_file() and not path.is_symlink()
    ]
    paths.extend(
        [
            "CPSLib.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
            "agentic/AGENTS.md",
            "agentic/skills/cpslib-prover/SKILL.md",
        ]
    )
    paths.extend(str(target) for _, target in source_files(problem, REPO_ROOT))
    fingerprint = hashlib.sha256()
    for name in sorted(set(paths), key=os.fsencode):
        digest = hashlib.sha256((REPO_ROOT / name).read_bytes()).hexdigest()
        escaped = name.replace("\\", "\\\\").replace("\n", "\\n")
        prefix = "\\" if escaped != name else ""
        fingerprint.update(os.fsencode(f"{prefix}{digest}  {escaped}\n"))
    return fingerprint.hexdigest()


def write_metadata(problem: Problem, destination: Path) -> None:
    metadata = (
        f"problem={problem.path}\n"
        f"task={task_path(problem, REPO_ROOT)}\n"
        f"source_fingerprint={source_fingerprint(problem)}\n"
        f"lean_toolchain={(REPO_ROOT / 'lean-toolchain').read_text().strip()}\n"
    )
    commit = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if commit.returncode == 0:
        dirty = bool(capture(["git", "status", "--porcelain"], REPO_ROOT))
        metadata += (
            f"git_commit={commit.stdout.strip()}\n"
            f"git_dirty={str(dirty).lower()}\n"
        )
    (destination / "benchmark-metadata.txt").write_text(metadata)


def init_agent_git(workspace: Workspace) -> None:
    if (workspace.path / ".git").exists():
        raise BenchmarkError(
            f"refusing to replace existing Git data in {workspace.path}"
        )
    checked(["git", "init", "-q"], workspace.path)
    checked(["git", "add", ".agents", "CPSLib", *PROJECT_FILES], workspace.path)
    checked(
        [
            "git",
            "-c",
            "user.name=CPSLib Benchmark",
            "-c",
            "user.email=benchmark@example.invalid",
            "commit",
            "-qm",
            "Initial sanitized benchmark",
        ],
        workspace.path,
    )


def create_project(
    problem: Problem, destination: Path, initialize_git: bool = False
) -> Workspace:
    packages = REPO_ROOT / ".lake/packages"
    if not (packages / "mathlib").is_dir():
        raise BenchmarkError(
            "missing trusted dependency cache; run "
            f"'lake update && lake exe cache get' in {REPO_ROOT}"
        )
    instructions = AGENTIC_ROOT / "AGENTS.md"
    skill = AGENTIC_ROOT / "skills/cpslib-prover"
    for required in (instructions, skill / "SKILL.md"):
        if not required.is_file():
            raise BenchmarkError(
                f"missing benchmark instructions or skill: {required}"
            )
    source_files(problem, REPO_ROOT)
    for name in ("Core", "Tactic"):
        for entry in (REPO_ROOT / "CPSLib" / name).rglob("*"):
            if entry.is_symlink():
                raise BenchmarkError(f"symlinked library source: {entry}")
    new_directory(destination)
    for name in ("Core", "Tactic"):
        shutil.copytree(
            REPO_ROOT / "CPSLib" / name,
            destination / "CPSLib" / name,
            symlinks=True,
        )
    for name in ("CPSLib.lean", "lean-toolchain", "lake-manifest.json"):
        shutil.copy2(REPO_ROOT / name, destination / name)
    copy_sources(problem, REPO_ROOT, destination)
    workspace = Workspace(destination, task_path(problem, REPO_ROOT))
    challenge = workspace.solution.with_name("Challenge.lean")
    shutil.copy2(challenge, workspace.solution)
    config = json.loads(workspace.config.read_text())
    module = ".".join(workspace.task.parts)
    if config.get("challenge_module") != f"{module}.Challenge":
        raise BenchmarkError("challenge_module must match the task path")
    config["solution_module"] = f"{module}.Solution"
    workspace.config.write_text(json.dumps(config, indent=4) + "\n")
    shutil.copy2(REPO_ROOT / "lakefile.toml", destination / "lakefile.toml")
    instructions_text = (
        instructions.read_text()
        .replace(
            "Solution.lean", str(workspace.solution.relative_to(destination))
        )
        .replace("Challenge.lean", str(workspace.task / "Challenge.lean"))
        .replace("`config.json`", f"`{workspace.task / 'config.json'}`")
    )
    instructions_text += (
        f"\nBuild this solution with `lake build {module}.Solution`.\n"
        "Only this task's Proof.lean is withheld; parent proofs are reusable.\n"
    )
    (destination / "AGENTS.md").write_text(instructions_text)
    shutil.copytree(
        skill, destination / ".agents/skills/cpslib-prover", symlinks=True
    )
    (destination / ".gitignore").write_text(
        "/.lake\n/.tmp\n/agent-output.jsonl\n/agent-stderr.log\n"
    )
    note("Linking the shared, trusted dependency package cache")
    (destination / ".lake").mkdir()
    (destination / ".lake/packages").symlink_to(
        packages, target_is_directory=True
    )
    write_metadata(problem, destination)
    note("Building the trusted challenge snapshot")
    checked(["lake", "build", f"{module}.Challenge"], destination)
    if initialize_git:
        init_agent_git(workspace)
    return workspace


def create_agent_project(source: Workspace, destination: Path) -> Workspace:
    new_directory(destination)
    for name in ("CPSLib", ".agents", ".lake/build"):
        shutil.copytree(source.path / name, destination / name, symlinks=True)
    for name in PROJECT_FILES:
        shutil.copy2(source.path / name, destination / name)
    (destination / ".lake/packages").mkdir()
    return Workspace(destination, source.task)
