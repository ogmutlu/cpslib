"""Copy task and ancestor support files, preserving Lean module paths."""

import shutil
from pathlib import Path

from .domain import BenchmarkError, Problem


def task_path(problem: Problem, repo_root: Path) -> Path:
    try:
        relative = problem.path.relative_to(repo_root.resolve())
    except ValueError as error:
        raise BenchmarkError("task must be inside this checkout") from error
    if relative.parts[:2] != ("CPSLib", "Examples"):
        raise BenchmarkError("task must be under CPSLib/Examples")
    if problem.path.resolve() != problem.path:
        raise BenchmarkError("symlinked task directories are not allowed")
    return relative


def source_files(problem: Problem, repo_root: Path) -> list[tuple[Path, Path]]:
    """Include immediate files only; withhold exactly the task reference proof.

    Parent proofs are reusable library material. Existing Solution.lean files
    are omitted because the harness seeds its own solution from Challenge.
    """
    relative = task_path(problem, repo_root)
    files: list[tuple[Path, Path]] = []
    directory = repo_root / relative
    boundary = repo_root / "CPSLib"
    while True:
        for source in sorted(directory.iterdir()):
            if source.name.startswith(".") or source.name == "Solution.lean":
                continue
            if source == problem.path / "Proof.lean":
                continue
            if source.is_symlink():
                raise BenchmarkError(f"symlinked support file: {source}")
            if source.is_file():
                files.append((source, source.relative_to(repo_root)))
        if directory == boundary:
            return files
        directory = directory.parent


def copy_sources(problem: Problem, repo_root: Path, destination: Path) -> None:
    for source, target in source_files(problem, repo_root):
        output = destination / target
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, output)
