#!/usr/bin/env python3
"""Verify the original Chapter 2 Hilbert reconstruction with installed Lean 4.28.0."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "eval_subst": {"propext"},
    "eval_repeat_positive": set(),
    "schema_valid": set(),
    "sound": {"propext"},
    "atom_not_derivable": {"propext"},
    "falsity_not_derivable": {"propext"},
    "basis_sound": {"propext"},
    "basis_atom_not_derivable": {"propext"},
    "selected_sound": {"propext"},
    "selected_atom_not_derivable": {"propext"},
}

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", default="lean", help="An installed Lean 4.28.0 binary")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "build" / "implication")
    args = parser.parse_args()
    build = args.output_dir.resolve()
    build.mkdir(parents=True, exist_ok=True)
    source = ROOT / "ImplicationSchemas.lean"
    initial = source.read_bytes()
    verifier_bytes = Path(__file__).read_bytes()
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b")
    match = forbidden.search(initial.decode("utf-8-sig"))
    if match:
        raise SystemExit(f"Forbidden source token: {match.group(0)}")
    version_run = subprocess.run([args.lean, "--version"], cwd=ROOT, capture_output=True, check=True)
    version = version_run.stdout.decode("utf-8").strip()
    if not re.search(r"version 4\.28\.0(?:,|\))", version):
        raise SystemExit(f"Expected Lean 4.28.0, received: {version}")
    command = [args.lean, "-DwarningAsError=true", "-o",
               str(build / "ImplicationSchemas.olean"), str(source)]
    result = subprocess.run(command, cwd=ROOT, capture_output=True)
    (build / "lean-stdout.log").write_bytes(result.stdout)
    (build / "lean-stderr.log").write_bytes(result.stderr)
    output = (result.stdout + result.stderr).decode("utf-8")
    print(output, end="")
    if result.returncode:
        raise SystemExit(result.returncode)
    observed = {}
    for name, expected in EXPECTED.items():
        full = "ImplicationSchemas." + name
        pattern = rf"'{re.escape(full)}' depends on axioms: \[([^\]]*)\]"
        report = re.search(pattern, output)
        if report:
            actual = {x.strip() for x in report.group(1).split(",") if x.strip()}
        elif f"'{full}' does not depend on any axioms" in output:
            actual = set()
        else:
            raise SystemExit(f"Missing dependency report: {full}")
        if actual != expected:
            raise SystemExit(f"Unexpected dependencies for {full}: {sorted(actual)}")
        observed[full] = sorted(actual)
    if source.read_bytes() != initial:
        raise SystemExit("Source changed during verification")
    obj = build / "ImplicationSchemas.olean"
    if not obj.is_file():
        raise SystemExit("Compiler produced no object file")
    receipt = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": source.name,
        "source_sha256": sha256(initial),
        "verifier": Path(__file__).name,
        "verifier_sha256": sha256(verifier_bytes),
        "compiler": version,
        "command": command,
        "working_directory": str(ROOT),
        "exit_code": result.returncode,
        "axioms_by_declaration": observed,
        "stdout_sha256": sha256(result.stdout),
        "stderr_sha256": sha256(result.stderr),
        "object_sha256": sha256(obj.read_bytes()),
        "source_unchanged_during_check": True,
        "scope": "Formula-level Boolean soundness and nontriviality; no label adequacy or operational claims.",
    }
    (build / "verification-receipt.json").write_bytes(
        (json.dumps(receipt, indent=2) + "\n").encode("utf-8"))
    print(f"Verified source SHA-256: {sha256(initial)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
