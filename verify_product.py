#!/usr/bin/env python3
"""Compile the raw product presentation with installed Lean 4.28.0 and audit its dependencies."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "root_size_decreases": [
        "propext",
        "Quot.sound"
    ],
    "step_size_decreases": [
        "propext",
        "Quot.sound"
    ],
    "step_wellFounded": [
        "propext",
        "Quot.sound"
    ],
    "Steps.single": [],
    "Steps.trans": [],
    "Steps.map": [],
    "Joinable.refl": [],
    "Joinable.symm": [],
    "Joinable.map": [],
    "eta_left_residual": [],
    "eta_right_residual": [],
    "root_step_join": [],
    "locally_confluent": [],
    "steps_size_le": [
        "propext",
        "Quot.sound"
    ],
    "confluent": [
        "propext",
        "Quot.sound"
    ],
    "normal_steps_eq": [],
    "reachable_normal_unique": [
        "propext",
        "Quot.sound"
    ],
    "exists_normal": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "exists_unique_normal": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "rootTargets_sound": [
        "propext"
    ],
    "rootTargets_complete": [
        "propext"
    ],
    "successors_sound": [
        "propext",
        "Quot.sound"
    ],
    "successors_complete": [
        "propext",
        "Quot.sound"
    ],
    "successors_iff": [
        "propext",
        "Quot.sound"
    ],
    "nf_reachable": [
        "propext",
        "Quot.sound"
    ],
    "nf_normal": [
        "propext",
        "Quot.sound"
    ],
    "steps_preserve_nf": [
        "propext",
        "Quot.sound"
    ],
    "step_equal": [],
    "steps_equal": [],
    "Joinable.trans": [
        "propext",
        "Quot.sound"
    ],
    "equal_joinable": [
        "propext",
        "Quot.sound"
    ],
    "equal_iff_nf": [
        "propext",
        "Quot.sound"
    ],
    "decideEqual_correct": [
        "propext",
        "Quot.sound"
    ],
    "normalise": [
        "propext",
        "Quot.sound"
    ],
    "nf": [
        "propext",
        "Quot.sound"
    ],
    "decideEqual": [
        "propext",
        "Quot.sound"
    ]
}

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Installed Lean 4.28.0 compiler")
    parser.add_argument("--output-dir", type=Path,
                        help="A new directory; existing directories are never reused")
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    build = (args.output_dir or ROOT / "build" / ("product-" + stamp)).resolve()
    build.mkdir(parents=True, exist_ok=False)
    source = ROOT / "ProductFragment.lean"
    verifier = Path(__file__).resolve()
    initial = source.read_bytes()
    verifier_bytes = verifier.read_bytes()
    (build / source.name).write_bytes(initial)
    (build / verifier.name).write_bytes(verifier_bytes)
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b")
    match = forbidden.search(initial.decode("utf-8-sig"))
    if match:
        raise SystemExit(f"Forbidden source token: {match.group(0)}")
    compiler = Path(shutil.which(args.lean) or args.lean).resolve()
    compiler_hash = sha256(compiler.read_bytes())
    version_run = subprocess.run([str(compiler), "--version"], cwd=ROOT, capture_output=True)
    (build / "version-stdout.log").write_bytes(version_run.stdout)
    (build / "version-stderr.log").write_bytes(version_run.stderr)
    version = version_run.stdout.decode("utf-8").strip()
    if version_run.returncode or not re.search(r"version 4\.28\.0(?:,|\))", version):
        raise SystemExit(f"Expected working Lean 4.28.0, received: {version}")
    obj = build / "ProductFragment.olean"
    command = [str(compiler), "-DwarningAsError=true", "-o", str(obj), str(source)]
    result = subprocess.run(command, cwd=ROOT, capture_output=True)
    (build / "lean-stdout.log").write_bytes(result.stdout)
    (build / "lean-stderr.log").write_bytes(result.stderr)
    output = (result.stdout + result.stderr).decode("utf-8")
    print(output, end="")
    if result.returncode:
        raise SystemExit(result.returncode)
    observed = {}
    for name, expected in EXPECTED.items():
        full = "ProductFragment." + name
        reports = re.findall(rf"'{re.escape(full)}' depends on axioms: \[([^\]]*)\]", output)
        empty_count = output.count(f"'{full}' does not depend on any axioms")
        if len(reports) + empty_count != 1:
            raise SystemExit(f"Missing or duplicate dependency report: {full}")
        actual = {x.strip() for x in reports[0].split(",") if x.strip()} if reports else set()
        if actual != set(expected):
            raise SystemExit(f"Unexpected dependencies for {full}: {sorted(actual)}")
        observed[full] = sorted(actual)
    reported = re.findall(r"'(ProductFragment\.[^']+)' (?:depends on axioms|does not depend on any axioms)", output)
    if set(reported) != set(observed) or len(reported) != len(observed):
        raise SystemExit("Unexpected or duplicate dependency declarations")
    if source.read_bytes() != initial or verifier.read_bytes() != verifier_bytes:
        raise SystemExit("Source or verifier changed during verification")
    if sha256(compiler.read_bytes()) != compiler_hash:
        raise SystemExit("Compiler changed during verification")
    if not obj.is_file() or not obj.stat().st_size:
        raise SystemExit("Compiler produced no nonempty object file")
    receipt = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": source.name,
        "source_sha256": sha256(initial),
        "verifier": verifier.name,
        "verifier_sha256": sha256(verifier_bytes),
        "compiler": version,
        "compiler_executable_sha256": compiler_hash,
        "command": command,
        "working_directory": str(ROOT),
        "exit_code": result.returncode,
        "axioms_by_declaration": observed,
        "stdout_sha256": sha256(result.stdout),
        "stderr_sha256": sha256(result.stderr),
        "version_stdout_sha256": sha256(version_run.stdout),
        "version_stderr_sha256": sha256(version_run.stderr),
        "object_sha256": sha256(obj.read_bytes()),
        "object_bytes": obj.stat().st_size,
        "source_unchanged_during_check": True,
        "verifier_unchanged_during_check": True,
        "compiler_unchanged_during_check": True,
        "scope": "All finite raw product terms over arbitrary atoms; three root rules and four context positions. Effective equality decision requires decidable atom equality. No larger-calculus claim."
    }
    receipt_path = build / "verification-receipt.json"
    receipt_bytes = (json.dumps(receipt, indent=2) + "\n").encode("utf-8")
    receipt_path.write_bytes(receipt_bytes)
    print(f"Verified source SHA-256: {sha256(initial)}")
    print(f"Receipt SHA-256: {sha256(receipt_bytes)}")
    print(f"Evidence directory: {build}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
