#!/usr/bin/env python3
"""Verify the exact raw equality skeleton with installed Lean 4.28.0."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
COMPILER_SHA256 = "6a66c4a5739fa17146b88ac81bab2bca1924806cac321ddad6b96006dde9c691"
EXPECTED = {
    "EqualitySkeleton.Reason": [],
    "EqualitySkeleton.W": [],
    "EqualitySkeleton.Q": [],
    "EqualitySkeleton.W_pos": [
        "propext",
        "Quot.sound"
    ],
    "EqualitySkeleton.Context": [],
    "EqualitySkeleton.Context.fill": [],
    "EqualitySkeleton.Context.coeff": [],
    "EqualitySkeleton.Context.offset": [],
    "EqualitySkeleton.Context.coeff_pos": [
        "propext"
    ],
    "EqualitySkeleton.Context.weight_affine": [
        "propext",
        "Quot.sound"
    ],
    "EqualitySkeleton.Context.weight_mono": [
        "propext",
        "Quot.sound"
    ],
    "EqualitySkeleton.Context.weight_strict": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "EqualitySkeleton.Context.weight_equal": [
        "propext",
        "Quot.sound"
    ],
    "EqualitySkeleton.Context.secondary_strict": [
        "propext",
        "Quot.sound"
    ],
    "EqualitySkeleton.Smaller": [],
    "EqualitySkeleton.context_decreases": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "EqualitySkeleton.Root": [],
    "EqualitySkeleton.root_decreases": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "EqualitySkeleton.Step": [],
    "EqualitySkeleton.step_decreases": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "EqualitySkeleton.rank": [],
    "EqualitySkeleton.RankLT": [],
    "EqualitySkeleton.rank_wellFounded": [],
    "EqualitySkeleton.step_rank_decreases": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "EqualitySkeleton.terminating": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "EqualitySkeleton.no_infinite_reduction": [
        "propext",
        "Classical.choice",
        "Quot.sound"
    ],
    "EqualitySkeleton.Context.comp": [],
    "EqualitySkeleton.Context.fill_comp": [
        "propext"
    ],
    "EqualitySkeleton.Step.root": [],
    "EqualitySkeleton.Step.context": [
        "propext"
    ],
    "EqualitySkeleton.Steps": [],
    "EqualitySkeleton.Normal": [],
    "EqualitySkeleton.no_root_below_rho": [
        "propext"
    ],
    "EqualitySkeleton.no_root_below_xi1_rho": [
        "propext"
    ],
    "EqualitySkeleton.rho_normal": [
        "propext"
    ],
    "EqualitySkeleton.xi1_rho_normal": [
        "propext"
    ],
    "EqualitySkeleton.normal_steps_eq": [],
    "EqualitySkeleton.peak": [],
    "EqualitySkeleton.peak_to_rho": [],
    "EqualitySkeleton.peak_to_xi1_rho": [],
    "EqualitySkeleton.Confluent": [],
    "EqualitySkeleton.not_confluent": [
        "propext"
    ]
}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, help="Installed native Lean 4.28.0 executable")
    parser.add_argument("--output-dir", type=Path, help="New evidence directory; never reused")
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    build = (args.output_dir or ROOT / "evidence" / "equality-skeleton" / ("run-" + stamp)).resolve()
    build.mkdir(parents=True, exist_ok=False)
    source = ROOT / "EqualitySkeleton.lean"
    verifier = Path(__file__).resolve()
    original = source.read_bytes()
    script = verifier.read_bytes()
    (build / source.name).write_bytes(original)
    (build / verifier.name).write_bytes(script)
    text = original.decode("utf-8-sig")
    prohibited = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b", text)
    if prohibited:
        raise SystemExit("Forbidden token: " + prohibited.group(0))
    requested = re.findall(r"^#print axioms (\S+)\s*$", text, re.MULTILINE)
    if sorted(requested) != sorted(EXPECTED):
        raise SystemExit("Missing, additional or duplicate dependency-audit request")
    compiler = Path(shutil.which(args.lean) or args.lean).resolve()
    compiler_before = digest(compiler.read_bytes())
    if compiler_before != COMPILER_SHA256:
        raise SystemExit("Compiler executable does not match the pinned native executable")
    version_run = subprocess.run([str(compiler), "--version"], cwd=ROOT, capture_output=True)
    (build / "version-stdout.log").write_bytes(version_run.stdout)
    (build / "version-stderr.log").write_bytes(version_run.stderr)
    version = version_run.stdout.decode("utf-8").strip()
    if version_run.returncode or not re.search(r"version 4\.28\.0(?:,|\))", version):
        raise SystemExit("Expected working Lean 4.28.0; received " + version)
    obj = build / "EqualitySkeleton.olean"
    command = [str(compiler), "-DwarningAsError=true", "-o", str(obj), str(source)]
    run = subprocess.run(command, cwd=ROOT, capture_output=True)
    (build / "lean-stdout.log").write_bytes(run.stdout)
    (build / "lean-stderr.log").write_bytes(run.stderr)
    output = (run.stdout + run.stderr).decode("utf-8")
    print(output, end="")
    if run.returncode:
        raise SystemExit(run.returncode)
    actual = {}
    for name, expected in EXPECTED.items():
        reports = re.findall(rf"'{re.escape(name)}' depends on axioms: \[([^\]]*)\]", output)
        empty_count = output.count(f"'{name}' does not depend on any axioms")
        if len(reports) + empty_count != 1:
            raise SystemExit("Missing or duplicate declaration report: " + name)
        deps = sorted({x.strip() for x in reports[0].split(",") if x.strip()}) if reports else []
        if deps != sorted(expected):
            raise SystemExit(f"Unexpected dependencies for {name}: {deps}")
        actual[name] = deps
    reported = re.findall(r"'(EqualitySkeleton\.[^']+)' (?:depends on axioms|does not depend on any axioms)", output)
    if sorted(reported) != sorted(EXPECTED):
        raise SystemExit("Unexpected or duplicate dependency declarations")
    if source.read_bytes() != original or verifier.read_bytes() != script:
        raise SystemExit("Source or verifier changed during verification")
    if digest(compiler.read_bytes()) != compiler_before:
        raise SystemExit("Compiler changed during verification")
    if not obj.is_file() or obj.stat().st_size == 0:
        raise SystemExit("No fresh nonempty compiled object")
    receipt = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": source.name, "source_sha256": digest(original),
        "verifier": verifier.name, "verifier_sha256": digest(script),
        "compiler": version, "compiler_executable_sha256": compiler_before,
        "command": command, "working_directory": str(ROOT), "exit_code": run.returncode,
        "axioms_by_declaration": actual,
        "stdout_sha256": digest(run.stdout), "stderr_sha256": digest(run.stderr),
        "version_stdout_sha256": digest(version_run.stdout),
        "version_stderr_sha256": digest(version_run.stderr),
        "object_sha256": digest(obj.read_bytes()), "object_bytes": obj.stat().st_size,
        "source_unchanged_during_check": True,
        "verifier_unchanged_during_check": True,
        "compiler_unchanged_during_check": True,
        "scope": "All finite freely generated raw trees over arbitrary atoms; exact 37 root rules; one-hole schema contexts and one-hole compatible closure; corrected RHS v in rule 37; no extensions. Strong normalisation and raw nonconfluence, not typed LND soundness or normalisation."
    }
    receipt_bytes = (json.dumps(receipt, indent=2) + "\n").encode("utf-8")
    (build / "verification-receipt.json").write_bytes(receipt_bytes)
    print("Verified source SHA-256: " + digest(original))
    print("Receipt SHA-256: " + digest(receipt_bytes))
    print("Evidence directory: " + str(build))

if __name__ == "__main__":
    main()
