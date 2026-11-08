#!/usr/bin/env python3
"""Compile the pinned structural termination source and retain an axiom audit."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
DECLARATIONS = (
    "root_decreases",
    "step_decreases",
    "step_measure_decreases",
    "eight_terminating",
    "ten_terminating",
    "no_infinite_reduction",
)
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", default="lean", help="An already installed Lean 4.28.0 binary")
    args = parser.parse_args()
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    source = ROOT / "StructuralReasons.lean"
    source_bytes = source.read_bytes()
    digest = hashlib.sha256(source_bytes).hexdigest()
    # Reject source-level admissions or an alternate trusted execution boundary.
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b")
    found = forbidden.search(source_bytes.decode("utf-8-sig"))
    if found:
        raise SystemExit(f"Forbidden source token: {found.group(0)}")
    version_run = subprocess.run([args.lean, "--version"], cwd=ROOT, text=True,
                                 encoding="utf-8", capture_output=True, check=True)
    version = version_run.stdout.strip()
    if not re.search(r"version 4\.28\.0(?:,|\))", version):
        raise SystemExit(f"Expected Lean 4.28.0, received: {version}")
    command = [args.lean, "-DwarningAsError=true", "-o",
               str(build / "StructuralReasons.olean"), str(source)]
    result = subprocess.run(command, cwd=ROOT, text=True, encoding="utf-8",
                            capture_output=True)
    output = result.stdout + result.stderr
    (build / "lean-check.log").write_text(output, encoding="utf-8")
    if result.returncode:
        print(output, end="")
        raise SystemExit(result.returncode)
    for declaration in DECLARATIONS:
        pattern = rf"'StructuralReasons\.{declaration}' depends on axioms: \[([^\]]*)\]"
        match = re.search(pattern, output)
        if not match:
            raise SystemExit(f"Missing axiom audit for {declaration}")
        actual = {entry.strip() for entry in match.group(1).split(",") if entry.strip()}
        if actual != EXPECTED_AXIOMS:
            raise SystemExit(f"Unexpected axioms for {declaration}: {sorted(actual)}")
    if source.read_bytes() != source_bytes:
        raise SystemExit("Source changed during verification")
    receipt = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": source.name,
        "source_sha256": digest,
        "compiler": version,
        "command": command,
        "exit_code": result.returncode,
        "audited_declarations": ["StructuralReasons." + name for name in DECLARATIONS],
        "axioms": sorted(EXPECTED_AXIOMS),
        "source_unchanged_during_check": True,
    }
    (build / "verification-receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )
    print(output, end="")
    print(f"Verified source SHA-256: {digest}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

