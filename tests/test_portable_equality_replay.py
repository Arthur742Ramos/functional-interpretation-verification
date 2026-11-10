from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import verify_equality_skeleton_portable as replay


class PortableEqualityReplayTests(unittest.TestCase):
    def test_tree_pin_detects_a_modified_imported_library(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "bin").mkdir()
            (root / "lib").mkdir()
            (root / "bin" / "lean").write_bytes(b"compiler")
            library = root / "lib" / "Std.olean"
            library.write_bytes(b"original library")
            before, count = replay.distribution_digest(root)
            self.assertEqual(count, 2)
            library.write_bytes(b"changed library")
            after, _ = replay.distribution_digest(root)
            self.assertNotEqual(before, after)

    def test_duplicate_dependency_report_is_rejected(self):
        report = "'EqualitySkeleton.terminating' depends on axioms: [propext]\n"
        with self.assertRaisesRegex(ValueError, "Duplicate dependency report"):
            replay.parse_dependencies(report + report)

    def test_wrong_compiler_pin_fails_before_creating_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            lean = root / "lean"
            checker = root / "leanchecker"
            lean.write_bytes(b"not the pinned compiler")
            checker.write_bytes(b"not the pinned checker")
            output = root / "evidence"
            result = subprocess.run([
                sys.executable, str(ROOT / "verify_equality_skeleton_portable.py"),
                "--lean", str(lean), "--leanchecker", str(checker),
                "--output-dir", str(output),
            ], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("does not match", result.stderr)
            self.assertFalse(output.exists())

    def test_checker_from_another_distribution_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "compiler").mkdir()
            (root / "other").mkdir()
            lean = root / "compiler" / "lean"
            checker = root / "other" / "leanchecker"
            lean.write_bytes(b"compiler")
            checker.write_bytes(b"checker")
            output = root / "evidence"
            result = subprocess.run([
                sys.executable, str(ROOT / "verify_equality_skeleton_portable.py"),
                "--lean", str(lean), "--leanchecker", str(checker),
                "--output-dir", str(output),
            ], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("same pinned toolchain", result.stderr)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
