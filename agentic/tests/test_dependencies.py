"""Checks for reference-proof exclusion and native Comparator invocation."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from cpslib_prover.dependencies import copy_sources, source_files
from cpslib_prover.domain import BenchmarkError, Problem, Workspace
from cpslib_prover.judge import run_comparator
from cpslib_prover.workspace import (
    create_project,
    load_workspace,
    source_fingerprint,
)


class SnapshotTest(unittest.TestCase):
    def setUp(self) -> None:
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.task = Path("CPSLib/Examples/Base/Extra")
        self.problem = Problem(self.root / self.task)
        for name in (
            "CPSLib.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
            "agentic/AGENTS.md",
            "agentic/skills/cpslib-prover/SKILL.md",
            "CPSLib/Examples/Base/Proof.lean",
            "CPSLib/Examples/Base/Model.lean",
            "CPSLib/Examples/Base/Sibling/Model.lean",
            f"{self.task}/Proof.lean",
            f"{self.task}/Challenge.lean",
            f"{self.task}/Model.lean",
            f"{self.task}/config.json",
            f"{self.task}/Solution.lean",
            f"{self.task}/notes.md",
        ):
            file = self.root / name
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text(name)

    def test_copy_excludes_only_task_reference_and_generated_solution(self):
        destination = self.root / "snapshot"
        copy_sources(self.problem, self.root, destination)
        self.assertTrue(
            (destination / "CPSLib/Examples/Base/Proof.lean").is_file()
        )
        self.assertTrue((destination / self.task / "notes.md").is_file())
        self.assertFalse((destination / self.task / "Proof.lean").exists())
        self.assertFalse((destination / self.task / "Solution.lean").exists())
        self.assertFalse(
            (destination / "CPSLib/Examples/Base/Sibling").exists()
        )

    def test_fingerprint_tracks_parent_proof_but_not_task_proof(self):
        with patch("cpslib_prover.workspace.REPO_ROOT", self.root):
            before = source_fingerprint(self.problem)
            (self.problem.path / "Proof.lean").write_text("changed")
            self.assertEqual(before, source_fingerprint(self.problem))
            (self.root / "CPSLib/Examples/Base/Proof.lean").write_text("new")
            self.assertNotEqual(before, source_fingerprint(self.problem))

    def test_symlink_and_outside_task_rejected(self):
        (self.problem.path / "link.lean").symlink_to(self.root / "CPSLib.lean")
        with self.assertRaises(BenchmarkError):
            source_files(self.problem, self.root)
        with self.assertRaises(BenchmarkError):
            source_files(Problem(self.root), self.root)

    def test_preparation_preserves_modules_and_rewrites_only_snapshot(self):
        for name in (".lake/packages/mathlib", "CPSLib/Core", "CPSLib/Tactic"):
            (self.root / name).mkdir(parents=True, exist_ok=True)
        config = {
            "challenge_module": "CPSLib.Examples.Base.Extra.Challenge",
            "solution_module": "CPSLib.Examples.Base.Extra.Proof",
            "targets": ["safe"],
        }
        (self.problem.path / "config.json").write_text(json.dumps(config))
        destination = self.root / "prepared"
        with (
            patch("cpslib_prover.workspace.REPO_ROOT", self.root),
            patch(
                "cpslib_prover.workspace.AGENTIC_ROOT", self.root / "agentic"
            ),
            patch("cpslib_prover.workspace.checked") as checked,
        ):
            workspace = create_project(self.problem, destination)
            checked.assert_called_once_with(
                ["lake", "build", config["challenge_module"]], destination
            )
        self.assertEqual(load_workspace(destination), workspace)
        expected = dict(config)
        expected["solution_module"] = "CPSLib.Examples.Base.Extra.Solution"
        self.assertEqual(json.loads(workspace.config.read_text()), expected)
        self.assertEqual(
            json.loads((self.problem.path / "config.json").read_text()), config
        )
        self.assertEqual(
            workspace.solution.read_text(),
            (self.problem.path / "Challenge.lean").read_text(),
        )

    def test_native_comparator_uses_nested_config(self):
        workspace = Workspace(self.root, self.task)
        with patch("cpslib_prover.judge.subprocess.run") as run:
            run.return_value.returncode = 0
            self.assertEqual(run_comparator(workspace), 0)
            run.assert_called_once_with(
                ["lake", "comparator", f"--config={self.task}/config.json"],
                cwd=self.root,
                check=False,
            )


if __name__ == "__main__":
    unittest.main()
