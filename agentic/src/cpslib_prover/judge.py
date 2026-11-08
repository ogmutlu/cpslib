"""Independent solution checking through the toolchain's Lean Comparator."""

import subprocess

from .domain import Workspace
from .process import note, shell_exit_code


def run_comparator(workspace: Workspace) -> int:
    config = workspace.config.relative_to(workspace.path)
    note(f"Judging {workspace.solution} with lake comparator")
    process = subprocess.run(
        ["lake", "comparator", f"--config={config}"],
        cwd=workspace.path,
        check=False,
    )
    return shell_exit_code(process.returncode)
