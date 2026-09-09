#!/usr/bin/env python3
"""Fingerprint dependency Lean sources without including caches or binaries."""
import argparse
import hashlib
import json
import os
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1]

def fingerprint(root):
    root = root.resolve()
    files = []
    for parent, dirs, names in os.walk(root):
        dirs[:] = sorted(d for d in dirs if not d.startswith('.'))
        for name in names:
            if name.endswith('.lean'):
                p = Path(parent) / name
                files.append((str(p.relative_to(root)), p))
    digest = hashlib.sha256()
    for name, path in sorted(files):
        digest.update(name.encode() + b'\0')
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return {'lean_source_files': len(files), 'lean_source_tree_sha256': digest.hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib', type=Path, required=True)
    parser.add_argument('--geometry', type=Path, required=True)
    parser.add_argument('--check', action='store_true', help='Compare with saved fingerprints')
    args = parser.parse_args()
    roots = {
        'mathlib': args.mathlib,
        'MorganTianLib': args.geometry / 'formalized-sources' / 'MorganTian',
        'DoCarmoLib': args.geometry / 'formalized-sources' / 'DoCarmo',
        'Shared': args.geometry / 'shared'}
    for root in roots.values():
        if not root.is_dir():
            parser.error(f'Missing source directory: {root}')
    data = {
        'lean_version': '4.32.1',
        'mathlib_commit': '520045ab14e26149ee970e2e617ca04b09bde5d6',
        'geometry_commit': 'bb91a091f0b968f8bbe8d861e025a88d82b161be',
        'algorithm': 'SHA256 of sorted UTF8 relative path, NUL, binary SHA256(file), for all nonhidden *.lean source files',
        'sources': {name: fingerprint(path) for name, path in roots.items()}}
    path = PROJECT / 'verification' / 'dependency-fingerprints.json'
    if args.check:
        if data != json.loads(path.read_text()):
            raise SystemExit('Dependency source fingerprints differ from the verified snapshot.')
        print('Dependency source fingerprints match.')
    else:
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps(data, ensure_ascii=False))

if __name__ == '__main__':
    main()
