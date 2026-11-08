#!/usr/bin/env python3
"""Fresh Lean 4.28.0 replay of the exact typed structural confluence package."""
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
           'StructuralNormalForms', 'StructuralConfluence']
BASE_SHA256 = 'a717705e4bc91da75233929a153ff572c39815966d6257e5443da52d5ed9a3a8'
DECLARATIONS = {
    'StructuralReasons': [
        'counts', 'Smaller', 'measure', 'root_decreases', 'step_decreases',
        'TripleLT', 'triple_wellFounded', 'step_measure_decreases', 'terminating',
        'eight_terminating', 'ten_terminating', 'no_infinite_reduction',
        'EdgeId', 'action', 'reducedExpansion', 'root_action', 'step_action',
        'Steps.single', 'Steps.trans', 'Steps.sigma', 'Steps.left', 'Steps.right',
        'steps_action', 'steps_reducedExpansion', 'Normal', 'normal_steps_eq',
        'exists_normal', 'normal_sigma_child', 'normal_left', 'normal_right',
        'normal_shape', 'edgeId_heq', 'shape_pos_head', 'shape_neg_head',
        'normal_shape_reduced', 'shape_action_word', 'shape_injective',
        'shape_root_normal', 'shape_normal', 'normal_iff_reduced_shape',
        'normal_expansion_injective', 'ten_confluent',
        'ten_reachable_normal_unique', 'ten_exists_unique_normal', 'ten_normal_form_word'],
    'StructuralReasons.Words': [
        'inv', 'inv_inv', 'inv_ne_self', 'Reduced', 'reduced_nil', 'reduced_tail',
        'push', 'push_nil', 'push_cancel', 'push_prepend', 'push_reduced',
        'push_inverse', 'RWord', 'prepend', 'prepend_inverse', 'Action.ext',
        'Action.one', 'Action.reverse', 'Action.mul', 'Action.reverse_one',
        'Action.reverse_reverse', 'Action.mul_one', 'Action.one_mul',
        'Action.mul_reverse', 'Action.reverse_mul_self', 'Action.reverse_mul',
        'Action.mul_assoc', 'Action.cancel_suffix', 'Action.cancel_inverse_suffix',
        'letterAction', 'letterAction_inv', 'empty', 'stack', 'stack_of_reduced']}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|sorryAx)\b')


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', required=True, help='Already installed Lean 4.28.0 executable')
    parser.add_argument('--output', help='New output directory; must not already exist')
    args = parser.parse_args()
    executable = Path(args.lean).resolve(strict=True)
    timestamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    output = Path(args.output).resolve() if args.output else ROOT / 'evidence' / timestamp
    output.mkdir(parents=True, exist_ok=False)
    checked = output / 'checked-source'
    checked.mkdir()
    sources = [ROOT / (module + '.lean') for module in MODULES]
    before = {source.name: sha(source) for source in sources}
    if before['StructuralReasons.lean'] != BASE_SHA256:
        raise SystemExit('Base relation source does not match the reviewed exact presentation')
    verifier_before = sha(Path(__file__).resolve())
    compiler_before = sha(executable)
    for source in sources:
        found = FORBIDDEN.search(source.read_text(encoding='utf-8-sig'))
        if found:
            raise SystemExit(f'Forbidden token in {source.name}: {found.group()}')
        shutil.copyfile(source, checked / source.name)
    shutil.copyfile(Path(__file__).resolve(), output / 'verify_confluence.py')
    names = [namespace + '.' + name for namespace, ds in DECLARATIONS.items() for name in ds]
    audit = checked / 'Audit.lean'
    audit.write_text('import StructuralConfluence\n\n' + '\n'.join('#print axioms ' + n for n in names) + '\n\n' + '\n'.join('#check @StructuralReasons.' + n for n in ['ten_confluent', 'ten_reachable_normal_unique', 'ten_exists_unique_normal', 'ten_normal_form_word', 'normal_iff_reduced_shape']) + '\n', encoding='utf-8')
    env = dict(os.environ)
    env['LEAN_PATH'] = str(checked)
    # This script never invokes elan, Lake, a downloader, or an installer.
    version = subprocess.run([str(executable), '--version'], cwd=checked,
                             env=env, capture_output=True, text=True, encoding='utf-8')
    (output / 'version.log').write_text(version.stdout + version.stderr, encoding='utf-8')
    if version.returncode or not re.search(r'version 4\.28\.0(?:,|\))', version.stdout):
        raise SystemExit('Compiler version check failed; see version.log')
    commands = []
    logs = []
    for module in MODULES + ['Audit']:
        command = [str(executable), '-DwarningAsError=true', '-o',
                   str(checked / (module + '.olean')), str(checked / (module + '.lean'))]
        result = subprocess.run(command, cwd=checked, env=env, capture_output=True,
                                text=True, encoding='utf-8')
        log = output / (module + '.log')
        log.write_text(result.stdout + result.stderr, encoding='utf-8')
        commands.append({'module': module, 'argv': command, 'cwd': str(checked),
                         'LEAN_PATH': str(checked), 'exit_code': result.returncode})
        logs.append(log)
        (output / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        if result.returncode:
            print(result.stdout + result.stderr, end='')
            raise SystemExit(f'{module} failed; no successful receipt written')
    transcript = (output / 'Audit.log').read_text(encoding='utf-8')
    audits = {}
    for name in names:
        match = re.search(re.escape("'" + name + "'") + r' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)', transcript)
        if not match:
            raise SystemExit('Missing dependency report: ' + name)
        axioms = set(x.strip() for x in (match.group(1) or '').split(',') if x.strip())
        if not axioms <= ALLOWED_AXIOMS:
            raise SystemExit('Unapproved dependency for ' + name + ': ' + str(axioms))
        audits[name] = sorted(axioms)
    after = {source.name: sha(source) for source in sources}
    if before != after or sha(executable) != compiler_before or sha(Path(__file__).resolve()) != verifier_before:
        raise SystemExit('Input source, verifier, or compiler changed during the replay')
    for source in sources:
        if sha(checked / source.name) != before[source.name]:
            raise SystemExit('Snapshot mismatch: ' + source.name)
    receipt = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'passed', 'independent_review': 'not performed by this verifier',
        'compiler_path': str(executable), 'compiler_version': version.stdout.strip(),
        'compiler_sha256': compiler_before, 'verifier_sha256': verifier_before,
        'source_sha256': before, 'dependency_audit': audits,
        'audited_declaration_count': len(audits), 'commands': commands,
        'input_stability_checked': True,
        'artifact_sha256': {str(f.relative_to(output)): sha(f)
                            for f in checked.iterdir() if f.is_file()},
        'log_sha256': {f.name: sha(f) for f in logs},
    }
    (output / 'verification-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print('Passed:', output)
    print('Audited declarations:', len(audits))
    for name in names:
        if name.startswith('StructuralReasons.ten_'):
            print(name + ': ' + ', '.join(audits[name]))
    return 0


if __name__ == '__main__':
    sys.exit(main())
