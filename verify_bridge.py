#!/usr/bin/env python3
"""Replay the pinned word-normalisation bridge with an installed official toolchain."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
MODULES = ['StructuralReasons', 'ReducedWords', 'StructuralInvariant',
           'StructuralNormalForms', 'StructuralConfluence',
           'WordNormalisation', 'TypedWordBridge']
COMPILER_SHA = '3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf'
COMPILER_COMMIT = '7e01a1bf5c70fc6167d49c345d3bf80596e9a79b'
BASE_HASHES = {
    'StructuralReasons.lean': 'a717705e4bc91da75233929a153ff572c39815966d6257e5443da52d5ed9a3a8',
    'ReducedWords.lean': '9776aead48c3d575e86090f2af1e6f6726b5a4f266e3d5e3472b8ec9f4448bb2',
    'StructuralInvariant.lean': '8e8295ae01def72bc61d0800f1ec5860fbf468d1f819b7552059c4d75f71630d',
    'StructuralNormalForms.lean': '070d6df5a2d580bf6ac1057ebbb8bf261a0e237994739dd539a28521f49220a0',
    'StructuralConfluence.lean': '3aa9304c628d7d21ebd38c111eee81b7872a3fd82c0409e025a3bb6a880b97bf'}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|sorryAx)\b')
PRINT_DEFINITIONS = [
    'StructuralReasons.Words.Cancel', 'StructuralReasons.Words.Cancels',
    'StructuralReasons.Words.inverseWord', 'StructuralReasons.Words.wordAction',
    'StructuralReasons.expansion', 'StructuralReasons.letterSource',
    'StructuralReasons.letterTarget', 'StructuralReasons.Walk',
    'StructuralReasons.TypedWord', 'StructuralReasons.TypedWord.normalise',
    'StructuralReasons.TypedWord.Equiv']


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def inventory(sources):
    entries = []
    for source in sources:
        scope = []
        for number, line in enumerate(source.read_text(encoding='utf-8-sig').splitlines(), 1):
            ns = re.match(r'^namespace (\S+)\s*$', line)
            end = re.match(r'^end(?: \S+)?\s*$', line)
            if ns:
                scope.append(ns[1])
                continue
            if end:
                scope.pop()
                continue
            declaration = re.match(r'^\s*(?:@\[.*?\]\s*)?(?:noncomputable\s+)?'
                                   r'(def|abbrev|theorem|inductive|structure)\s+(\w+)', line)
            if declaration:
                entries.append({'name': '.'.join(scope + [declaration[2]]),
                                'kind': declaration[1], 'source': source.name, 'line': number})
    return entries


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', required=True, help='Installed official Lean 4.28.0 binary')
    parser.add_argument('--output', help='Fresh evidence directory; must not exist')
    parser.add_argument('--check-provenance', action='store_true',
                        help='Unsupported: historical private-path provenance is not distributed')
    args = parser.parse_args()
    if args.check_provenance:
        parser.error('--check-provenance is unavailable in this portable package; historical private inputs are not distributed')
    lean = Path(args.lean).resolve(strict=True)
    checker = lean.with_name('leanchecker').resolve(strict=True)
    if sha(lean) != COMPILER_SHA:
        raise SystemExit('Compiler binary differs from the pinned official release')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out = Path(args.output).resolve() if args.output else ROOT / 'evidence' / stamp
    out.mkdir(parents=True, exist_ok=False)
    checked = out / 'checked-source'
    checked.mkdir()
    sources = [ROOT / (m + '.lean') for m in MODULES]
    manifests = [ROOT / f for f in ['source-manifest.json', 'declaration-inventory.json']]
    tracked = sources + manifests + [Path(__file__).resolve(), lean, checker]
    before = {str(p): sha(p) for p in tracked}
    source_hashes = {p.name: sha(p) for p in sources}
    if source_hashes != json.loads((ROOT / 'source-manifest.json').read_text()):
        raise SystemExit('Source manifest mismatch')
    if any(source_hashes[name] != digest for name, digest in BASE_HASHES.items()):
        raise SystemExit('A reviewed base source changed')
    declarations = inventory(sources)
    if declarations != json.loads((ROOT / 'declaration-inventory.json').read_text()):
        raise SystemExit('Declaration inventory mismatch')
    names = [d['name'] for d in declarations]
    if len(set(names)) != len(names):
        raise SystemExit('Duplicate audited declaration')
    for p in sources:
        found = FORBIDDEN.search(p.read_text(encoding='utf-8-sig'))
        if found:
            raise SystemExit(f'Forbidden token in {p.name}: {found.group()}')
        shutil.copyfile(p, checked / p.name)
    for p in manifests + [Path(__file__).resolve()]:
        shutil.copyfile(p, out / p.name)
    audit = ('import TypedWordBridge\n\n' + '\n'.join('#print axioms ' + n for n in names)
             + '\n\n' + '\n'.join('#check @' + n for n in names) + '\n\n'
             + '\n'.join('#print ' + n for n in PRINT_DEFINITIONS) + '\n')
    (checked / 'Audit.lean').write_text(audit, encoding='utf-8')
    env = dict(os.environ)
    env['LEAN_PATH'] = str(checked)
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', '')
    commands = []

    def run(label, argv):
        result = subprocess.run(argv, cwd=checked, env=env, capture_output=True)
        (out / (label + '.stdout.log')).write_bytes(result.stdout)
        (out / (label + '.stderr.log')).write_bytes(result.stderr)
        commands.append({'label': label, 'argv': argv, 'cwd': str(checked),
                         'LEAN_PATH': env['LEAN_PATH'], 'PATH': env['PATH'],
                         'exit_code': result.returncode})
        (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        if result.returncode:
            sys.stdout.buffer.write(result.stdout)
            sys.stderr.buffer.write(result.stderr)
            raise SystemExit(label + ' failed; no successful receipt written')
        return result.stdout.decode('utf-8')

    version = run('version', [str(lean), '--version'])
    if 'version 4.28.0,' not in version or COMPILER_COMMIT not in version:
        raise SystemExit('Compiler version or commit mismatch')
    for module in MODULES + ['Audit']:
        run(module, [str(lean), '-DwarningAsError=true', '-o',
                     str(checked / (module + '.olean')), str(checked / (module + '.lean'))])
    transcript = (out / 'Audit.stdout.log').read_text()
    audits = {}
    for name in names:
        pattern = re.escape("'" + name + "'") + r' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)'
        match = re.search(pattern, transcript)
        if not match:
            raise SystemExit('Missing dependency report: ' + name)
        dependencies = {x.strip() for x in (match.group(1) or '').split(',') if x.strip()}
        if not dependencies <= ALLOWED_AXIOMS:
            raise SystemExit('Unapproved dependencies for ' + name + ': ' + repr(dependencies))
        audits[name] = sorted(dependencies)
    run('leanchecker-fresh', [str(checker), '--fresh', '--verbose', 'TypedWordBridge'])
    after = {str(p): sha(p) for p in tracked}
    if before != after:
        raise SystemExit('An input changed during verification')
    if any(sha(checked / p.name) != source_hashes[p.name] for p in sources):
        raise SystemExit('A checked-source snapshot changed')
    artifacts = {str(p.relative_to(out)): sha(p) for p in out.rglob('*') if p.is_file()}
    receipt = {
        'status': 'passed', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'independent_review': 'not performed by this verifier',
        'compiler_version': version.strip(), 'compiler_sha256': sha(lean),
        'leanchecker_sha256': sha(checker), 'verifier_sha256': sha(Path(__file__).resolve()),
        'source_sha256': source_hashes, 'audited_declaration_count': len(audits),
        'dependency_audit': audits, 'commands': commands,
        'fresh_kernel_replay': True, 'input_stability_checked': True,
        'original_provenance_paths_checked': False,
        'verifier_variant': 'portable-v1',
        'artifact_sha256': artifacts}
    (out / 'verification-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('Passed:', out)
    print('Audited declarations:', len(audits))
    print('Fresh kernel replay: passed')
    return 0


if __name__ == '__main__':
    sys.exit(main())
