#!/usr/bin/env python3
"""Build the complete Lean library and audit its imported declarations."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

PROJECT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', help='Existing Lean 4.32.1 lake executable; defaults to PATH')
    parser.add_argument('--skip-build', action='store_true',
                        help='Inspect already-built modules; this does not certify a fresh build')
    args = parser.parse_args()
    lake = shutil.which(os.path.expanduser(args.lake or 'lake'))
    if not lake:
        parser.error('No lake executable found. Activate the existing Lean 4.32.1 toolchain or pass --lake.')
    lake = os.path.abspath(lake)
    env = os.environ.copy()
    env['PATH'] = str(Path(lake).parent) + os.pathsep + env.get('PATH', '')
    env['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
    output = PROJECT / 'verification'
    output.mkdir(exist_ok=True)
    version_result = subprocess.run([lake, 'env', 'lean', '--version'], cwd=PROJECT, env=env,
                                    capture_output=True, text=True, check=True)
    lean_version = version_result.stdout.strip()
    if not re.search(r'\bversion 4\.32\.1(?:[,\s]|$)', lean_version):
        raise SystemExit('Expected Lean 4.32.1; actual executable reported: ' + lean_version)
    manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    def local_dependency(name):
        package = packages[name]
        if package['type'] != 'path':
            raise SystemExit(f'Expected a configured local dependency: {name}')
        return (PROJECT / package['dir']).resolve()
    mathlib = local_dependency('mathlib')
    geometry = local_dependency('MorganTianLib').parents[1]
    for name, expected in [('DoCarmoLib', geometry / 'formalized-sources' / 'DoCarmo'),
                           ('Shared', geometry / 'shared')]:
        if local_dependency(name) != expected.resolve():
            raise SystemExit(f'Unexpected dependency layout for {name}; retain the pinned source layout.')
    fingerprint_command = [sys.executable, str(PROJECT / 'scripts' / 'fingerprint_dependencies.py'),
                           '--mathlib', str(mathlib), '--geometry', str(geometry), '--check']
    print('Checking dependency source fingerprints.', flush=True)
    with (output / 'dependency-check.log').open('w') as log:
        code = subprocess.run(fingerprint_command, cwd=PROJECT, env=env,
                              stdout=log, stderr=subprocess.STDOUT).returncode
    if code:
        raise SystemExit(f'Dependency fingerprint check failed: {output / "dependency-check.log"}')
    source_files = [PROJECT / 'CurveControl.lean', PROJECT / 'Audit.lean', PROJECT / 'BlueprintAudit.lean',
                    PROJECT / 'lakefile.lean', PROJECT / 'lake-manifest.json', PROJECT / 'lean-toolchain',
                    PROJECT / 'blueprint' / 'blueprint.json',
                    PROJECT / 'paper' / 'curve-estimates.tex', PROJECT / 'paper' / 'references.bib',
                    PROJECT / 'paper' / 'curve-estimates.pdf',
                    PROJECT / '.github' / 'workflows' / 'verify.yml',
                    output / 'dependency-fingerprints.json']
    source_files += sorted((PROJECT / 'CurveControl').rglob('*.lean'))
    source_files += sorted((PROJECT / 'scripts').glob('*.py'))
    source_files += sorted((PROJECT / 'scripts').glob('*.cjs'))
    source_files += sorted(p for p in (PROJECT / 'website-template').rglob('*') if p.is_file())
    source_files += sorted(p for p in (PROJECT / 'third_party').rglob('*') if p.is_file())
    def source_hashes():
        return {str(p.relative_to(PROJECT)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in source_files}
    sources_before = source_hashes()
    steps = []
    if not args.skip_build:
        steps.append(('full-build.log', [lake, 'build', 'CurveControl']))
    steps.append(('environment-axiom-audit.log', [lake, 'env', 'lean', 'Audit.lean']))
    steps.append(('blueprint-declarations.log', [lake, 'env', 'lean', 'BlueprintAudit.lean']))
    steps.append(('blueprint-check.log', [sys.executable, str(PROJECT / 'scripts' / 'check_blueprint.py')]))
    for logname, command in steps:
        print('Running:', ' '.join(command), flush=True)
        with (output / logname).open('w') as log:
            code = subprocess.run(command, cwd=PROJECT, env=env,
                                  stdout=log, stderr=subprocess.STDOUT).returncode
        if code:
            raise SystemExit(f'Failed with exit {code}: {output / logname}')
    audit = json.loads((output / 'reachable-axioms.json').read_text())
    if audit['extra_axioms'] or not audit['checked_declarations']:
        raise SystemExit('Axiom audit returned no declarations or unexpected axioms.')
    expected_modules = {'CurveControl'} | {
        '.'.join(p.relative_to(PROJECT).with_suffix('').parts)
        for p in (PROJECT / 'CurveControl').rglob('*.lean')}
    missing = expected_modules - set(audit['modules'])
    if missing:
        raise SystemExit('Source modules missing from the audited root: ' + ', '.join(sorted(missing)))
    sources = source_hashes()
    if sources != sources_before:
        raise SystemExit('Project source or configuration changed during verification; rerun with frozen sources.')
    result = {
        'checked_at': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'lean_executable_version': lean_version,
        'dependency_fingerprint_check_exit_code': 0,
        'source_unchanged_during_verification': True,
        'full_build_in_this_run': not args.skip_build,
        'build_exit_code': 0 if not args.skip_build else None,
        'axiom_audit_exit_code': 0,
        'blueprint_export_exit_code': 0,
        'blueprint_check_exit_code': 0,
        'checked_declarations': audit['checked_declarations'],
        'audited_modules': audit['modules'],
        'allowed_axioms': audit['allowed_axioms'],
        'extra_axioms': [],
        'source_sha256': sources,
        'semantic_review': 'Separate reports in docs; not implied by this mechanical check.'}
    (output / 'release-check.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'source_sha256'}, ensure_ascii=False))

if __name__ == '__main__':
    main()
