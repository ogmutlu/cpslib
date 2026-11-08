"""Agent launch commands and the benchmark's filesystem and network policy."""

import json
import os
import sys
from pathlib import Path

from .domain import Agent, AgentOptions, BenchmarkError, Workspace
from .process import capture, logged, note, resolve_executable

PROMPT = """
    Complete the Lean proof task described in AGENTS.md. Edit the solution
    specified there, inspect the local CPSLib library, and build the solution
    module while developing the proof. Leave the completed proof in that file.
"""


def toml_table(values: dict[str, str]) -> str:
    entries = (
        f"{json.dumps(key)}={json.dumps(value)}"
        for key, value in values.items()
    )
    return "{" + ",".join(entries) + "}"


def codex_command(
    workspace: Workspace,
    packages: Path,
    toolchain_root: Path,
    options: AgentOptions,
) -> list[str]:
    return [
        sys.executable,
        "-m",
        "cpslib_prover.codex_runner",
        str(workspace.path),
        str(packages),
        str(toolchain_root),
        options.effective_model,
    ]


def run_agent(
    workspace: Workspace,
    packages: Path,
    agent: Agent,
    options: AgentOptions,
    stdout_file: Path,
    stderr_file: Path,
) -> int:
    packages = packages.resolve()
    if not packages.is_dir():
        raise BenchmarkError(
            f"missing dependency package directory: {packages}"
        )
    elan = resolve_executable(os.environ.get("ELAN_BIN", "elan"))
    toolchain_lake = Path(
        capture([str(elan), "which", "lake"], workspace.path)
    ).resolve()
    resolve_executable(str(toolchain_lake))
    toolchain_root = toolchain_lake.parent.parent
    timeout = resolve_executable("timeout")
    dependency_link = workspace.path / ".lake/packages"
    if dependency_link.is_symlink():
        dependency_link.unlink()
    elif dependency_link.is_dir():
        try:
            dependency_link.rmdir()
        except OSError as error:
            raise BenchmarkError(
                "refusing to replace nonempty dependency directory:"
                f"{dependency_link}"
            ) from error
    else:
        raise BenchmarkError(f"missing dependency link: {dependency_link}")
    dependency_link.symlink_to(packages, target_is_directory=True)
    temporary_directory = workspace.path / ".tmp"
    temporary_directory.mkdir(exist_ok=True)
    command = codex_command(workspace, packages, toolchain_root, options)
    note(f"Running {agent.value} in {workspace.path}")
    return logged(
        [
            str(timeout),
            "--signal=TERM",
            "--kill-after=30",
            str(options.timeout),
            *command,
        ],
        workspace.path,
        {**os.environ, "TMPDIR": str(temporary_directory)},
        stdout_file,
        stderr_file,
    )
