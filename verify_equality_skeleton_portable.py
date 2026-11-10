#!/usr/bin/env python3
"""Replay the raw equality skeleton with a separately pinned Lean toolchain.

This is a new replay procedure, not the historical Windows verifier. It
compiles a fresh copy of the published source and runs Lean's fresh checker.
"""

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
SOURCE_SHA256 = "f097b93f6cb213f761469411f24550c9f46a030492f622bdc7edb2cfe35805ca"
HISTORICAL_VERIFIER_SHA256 = "f88ff077deb5966236fac268d28cc39375a18040f426b2d6f427ded9afe3d935"
LINUX_LEAN_SHA256 = "3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf"
LINUX_CHECKER_SHA256 = "cb6cee24e93aa1d72ad0314906c51918f7c96947e18790a0273c837c25e79025"
LINUX_TREE_SHA256 = "e8433dd0e8c0a676f4cae4033f4280feb92ee75dc5dede320b98acd77d4efbf6"
LEAN_COMMIT = "7e01a1bf5c70fc6167d49c345d3bf80596e9a79b"
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def distribution_digest(root):
    """Hash every regular file and symlink by relative name and content/target."""
    records = []
    for path in root.rglob("*"):
        name = path.relative_to(root).as_posix()
        if path.is_symlink():
            records.append((name, "l", str(path.readlink())))
        elif path.is_file():
            h = hashlib.sha256()
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    h.update(chunk)
            records.append((name, "f", h.hexdigest()))
    total = hashlib.sha256()
    for name, kind, value in sorted(records):
        total.update(f"{kind}\0{name}\0{value}\n".encode("utf-8"))
    return total.hexdigest(), len(records)


def expected_dependencies(verifier):
    tree = ast.parse(verifier.decode("utf-8"))
    values = [node.value for node in tree.body
              if isinstance(node, ast.Assign) and len(node.targets) == 1
              and isinstance(node.targets[0], ast.Name)
              and node.targets[0].id == "EXPECTED"]
    if len(values) != 1:
        raise ValueError("Historical verifier does not contain one EXPECTED mapping")
    result = ast.literal_eval(values[0])
    if not isinstance(result, dict) or not result:
        raise ValueError("Invalid expected dependency mapping")
    return {name: sorted(deps) for name, deps in result.items()}


def parse_dependencies(output):
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for name, raw in re.findall(pattern, output):
        if name in found:
            raise ValueError("Duplicate dependency report: " + name)
        found[name] = sorted(x.strip() for x in raw.split(",") if x.strip())
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, help="Path to the native Lean compiler")
    parser.add_argument("--leanchecker", help="Path to leanchecker; defaults to the compiler's sibling")
    parser.add_argument("--output-dir", type=Path, required=True, help="New evidence directory")
    parser.add_argument("--lean-sha256", default=LINUX_LEAN_SHA256,
                        help="Expected compiler hash; default is the official Linux x86-64 release")
    parser.add_argument("--checker-sha256", default=LINUX_CHECKER_SHA256,
                        help="Expected checker hash; default is the official Linux x86-64 release")
    parser.add_argument("--toolchain-tree-sha256", default=LINUX_TREE_SHA256,
                        help="Expected full distribution-tree hash; default is the official Linux release")
    args = parser.parse_args()

    lean = Path(shutil.which(args.lean) or args.lean).resolve(strict=True)
    checker_name = "leanchecker.exe" if lean.suffix.lower() == ".exe" else "leanchecker"
    checker = Path(args.leanchecker).resolve(strict=True) if args.leanchecker else lean.with_name(checker_name)
    checker = checker.resolve(strict=True)
    if checker.parent != lean.parent:
        raise ValueError("Compiler and checker must be in the same pinned toolchain bin directory")
    source_path = ROOT / "EqualitySkeleton.lean"
    historical_path = ROOT / "verify_equality_skeleton.py"
    verifier_path = Path(__file__).resolve()
    source, historical, verifier = (p.read_bytes() for p in (source_path, historical_path, verifier_path))
    compiler_hash, checker_hash = digest(lean.read_bytes()), digest(checker.read_bytes())
    if digest(source) != SOURCE_SHA256:
        raise ValueError("EqualitySkeleton.lean does not match the published source")
    if digest(historical) != HISTORICAL_VERIFIER_SHA256:
        raise ValueError("Historical verifier does not match the published dependency audit")
    if compiler_hash != args.lean_sha256.lower() or checker_hash != args.checker_sha256.lower():
        raise ValueError("Compiler or checker does not match its supplied SHA-256 pin")
    toolchain_root = lean.parent.parent
    tree_hash, tree_count = distribution_digest(toolchain_root)
    if tree_hash != args.toolchain_tree_sha256.lower():
        raise ValueError("The complete installed toolchain differs from its supplied tree pin")
    text = source.decode("utf-8-sig")
    match = FORBIDDEN.search(text)
    if match:
        raise ValueError("Forbidden source token: " + match.group(0))
    expected = expected_dependencies(historical)
    requested = re.findall(r"^#print axioms (\S+)\s*$", text, re.MULTILINE)
    if sorted(requested) != sorted(expected):
        raise ValueError("Source dependency-audit requests differ from the historical verifier")

    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    copied_source = output / source_path.name
    copied_source.write_bytes(source)
    (output / historical_path.name).write_bytes(historical)
    (output / verifier_path.name).write_bytes(verifier)
    env = os.environ.copy()
    for name in ("LEAN_SRC_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH", "LD_PRELOAD",
                 "LD_AUDIT", "DYLD_LIBRARY_PATH", "DYLD_INSERT_LIBRARIES",
                 "DYLD_FRAMEWORK_PATH", "DYLD_FALLBACK_LIBRARY_PATH",
                 "DYLD_FALLBACK_FRAMEWORK_PATH"):
        env.pop(name, None)
    env["LEAN_PATH"] = str(output)
    env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")

    log_hashes = {}

    def run(name, command):
        result = subprocess.run([str(arg) for arg in command], cwd=output, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (output / (name + "-stdout.log")).write_bytes(result.stdout)
        (output / (name + "-stderr.log")).write_bytes(result.stderr)
        log_hashes[name] = {"stdout_sha256": digest(result.stdout),
                            "stderr_sha256": digest(result.stderr)}
        if result.returncode:
            raise RuntimeError(f"{name} failed ({result.returncode}); see logs in {output}")
        return (result.stdout + result.stderr).decode("utf-8", errors="strict")

    version = run("version", [lean, "--version"]).strip()
    if "version 4.28.0," not in version or LEAN_COMMIT not in version:
        raise ValueError("Expected the pinned Lean 4.28.0 release commit: " + version)
    obj = output / "EqualitySkeleton.olean"
    compile_cmd = [lean, "-DwarningAsError=true", "-o", obj, copied_source]
    observed = parse_dependencies(run("compile", compile_cmd))
    if observed != expected:
        raise ValueError("Declaration dependencies differ from the historical audit")
    if not obj.is_file() or not obj.stat().st_size:
        raise ValueError("Compilation did not create a nonempty fresh object")
    checker_cmd = [checker, "--fresh", "--verbose", "EqualitySkeleton"]
    checker_output = run("fresh-check", checker_cmd)
    if "replaying EqualitySkeleton with --fresh" not in checker_output:
        raise ValueError("The fresh checker did not report replaying EqualitySkeleton")
    for path, original in ((source_path, source), (historical_path, historical), (verifier_path, verifier)):
        if path.read_bytes() != original:
            raise ValueError("Input changed during verification: " + path.name)
    if digest(lean.read_bytes()) != compiler_hash or digest(checker.read_bytes()) != checker_hash:
        raise ValueError("Compiler or checker changed during verification")
    if distribution_digest(toolchain_root) != (tree_hash, tree_count):
        raise ValueError("Toolchain files changed during verification")

    receipt = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "procedure": "separate portable replay; historical Windows verifier not executed",
        "source_sha256": digest(source),
        "historical_verifier_sha256": digest(historical),
        "portable_verifier_sha256": digest(verifier),
        "compiler_version": version,
        "compiler_sha256": compiler_hash,
        "checker_sha256": checker_hash,
        "toolchain_tree_sha256": tree_hash,
        "toolchain_tree_entries": tree_count,
        "platform": platform.platform(),
        "python_version": sys.version,
        "compile_command": [str(x) for x in compile_cmd],
        "fresh_checker_command": [str(x) for x in checker_cmd],
        "object_sha256": digest(obj.read_bytes()),
        "logs": log_hashes,
        "axioms_by_declaration": observed,
        "scope": "Exact raw 37-rule equality-reason skeleton, not the full typed labelled calculus.",
    }
    (output / "verification-receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("Compilation and fresh kernel replay passed for the raw equality skeleton.")
    print("Evidence:", output)


if __name__ == "__main__":
    main()
