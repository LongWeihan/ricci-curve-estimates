#!/usr/bin/env python3
"""Reuse pinned sources, or explicitly fetch missing ones, then configure Lake."""
import argparse
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

from fingerprint_dependencies import fingerprint

PROJECT = Path(__file__).resolve().parents[1]
PINS = {
    'mathlib': ('leanprover-community/mathlib4', '520045ab14e26149ee970e2e617ca04b09bde5d6'),
    'geometry': ('frenzymath/Poincare-Conjecture', 'bb91a091f0b968f8bbe8d861e025a88d82b161be'),
}
GEOMETRY_PACKAGES = {
    'MorganTianLib': 'formalized-sources/MorganTian',
    'DoCarmoLib': 'formalized-sources/DoCarmo',
    'Shared': 'shared',
}


def selected(name, kind):
    """Retain complete packages and repository attribution; no source rewriting."""
    if kind == 'mathlib':
        return True
    path = PurePosixPath(name)
    return any(name == p or name.startswith(p + '/') for p in GEOMETRY_PACKAGES.values()) or (
        len(path.parts) == 1 and path.name.upper().startswith(('LICENSE', 'COPYING', 'NOTICE', 'README')))


def extract_archive(archive, target, kind):
    """Extract regular files before internal symlinks; reject escaping paths."""
    _, revision = PINS[kind]
    links = []
    with tarfile.open(archive, 'r:gz') as source:
        for member in source:
            parts = PurePosixPath(member.name).parts
            if not parts or not parts[0].endswith('-' + revision):
                raise ValueError('Archive root does not identify the pinned commit')
            relative = PurePosixPath(*parts[1:])
            if not parts[1:]:
                continue
            if relative.is_absolute() or '..' in relative.parts:
                raise ValueError('Unsafe archive path: ' + member.name)
            if not selected(str(relative), kind):
                continue
            destination = target.joinpath(*relative.parts)
            if member.isdir():
                destination.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                destination.parent.mkdir(parents=True, exist_ok=True)
                with source.extractfile(member) as src, destination.open('xb') as dst:
                    shutil.copyfileobj(src, dst)
                destination.chmod(0o755 if member.mode & 0o111 else 0o644)
            elif member.issym():
                link = PurePosixPath(member.linkname)
                resolved = (destination.parent / member.linkname).resolve()
                if link.is_absolute() or target.resolve() not in resolved.parents:
                    raise ValueError('Unsafe archive symlink: ' + member.name)
                links.append((destination, member.linkname))
            else:
                raise ValueError('Unsupported archive entry: ' + member.name)
    for destination, link in links:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.symlink_to(link)


def check_source(path, kind, baseline):
    roots = {'mathlib': path} if kind == 'mathlib' else {
        name: path / rel for name, rel in GEOMETRY_PACKAGES.items()}
    for name, root in roots.items():
        if not root.is_dir() or fingerprint(root) != baseline['sources'][name]:
            raise ValueError(f'{name}: source fingerprint mismatch at {root}; nothing overwritten')
        toolchain = (root / 'lean-toolchain').read_text().strip()
        if toolchain != 'leanprover/lean4:v4.32.1':
            raise ValueError(f'{name}: expected Lean 4.32.1; got {toolchain}')


def ensure_source(path, kind, mode, archive, baseline):
    if path.exists():
        print(f'Reusing {kind}: {path}', flush=True)
        check_source(path, kind, baseline)
        return
    if mode != 'fetch':
        raise ValueError(f'Missing {kind}: {path}; supply existing sources or explicitly use --mode fetch')
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.prepare-', dir=path.parent) as temp:
        scratch = Path(temp)
        if archive is None:
            repo, revision = PINS[kind]
            url = f'https://codeload.github.com/{repo}/tar.gz/{revision}'
            print(f'Fetching missing {kind} from {url}', flush=True)
            archive = scratch / 'source.tar.gz'
            request = urllib.request.Request(url, headers={'User-Agent': 'CurveControl-reproduction'})
            with urllib.request.urlopen(request, timeout=120) as src, archive.open('wb') as dst:
                shutil.copyfileobj(src, dst)
        staged = scratch / 'source'
        staged.mkdir()
        extract_archive(archive, staged, kind)
        check_source(staged, kind, baseline)
        if kind == 'geometry' and not (staged / 'LICENSE').is_file():
            raise ValueError('Pinned geometry archive lacks its root LICENSE')
        if path.exists():
            raise ValueError(f'Destination appeared during preparation: {path}')
        staged.rename(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('reuse', 'fetch'), default='reuse',
                        help='Only fetch mode may obtain missing sources; existing paths are never replaced')
    parser.add_argument('--deps-dir', type=Path, default=PROJECT / '.dependencies')
    parser.add_argument('--mathlib', type=Path, help='Existing mathlib root, or explicit fetch destination')
    parser.add_argument('--geometry', type=Path, help='Geometry repository root, retaining its package layout')
    parser.add_argument('--mathlib-archive', type=Path, help='Reuse an existing fixed-revision tar.gz in fetch mode')
    parser.add_argument('--geometry-archive', type=Path, help='Reuse an existing fixed-revision tar.gz in fetch mode')
    parser.add_argument('--lake', default='lake', help='Existing Lean 4.32.1 lake executable')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--check-only', action='store_true', help='Check/prepare sources without writing Lake configuration')
    group.add_argument('--configure-only', action='store_true', help='Write configuration but defer lake update/toolchain use')
    args = parser.parse_args()
    baseline = json.loads((PROJECT / 'verification/dependency-fingerprints.json').read_text())
    mathlib = (args.mathlib or args.deps_dir / 'mathlib4').expanduser().resolve()
    geometry = (args.geometry or args.deps_dir / 'Poincare-Conjecture').expanduser().resolve()
    for kind, path, archive in [('mathlib', mathlib, args.mathlib_archive),
                                 ('geometry', geometry, args.geometry_archive)]:
        ensure_source(path, kind, args.mode,
                      archive.expanduser().resolve() if archive else None, baseline)
    if args.check_only:
        print('All four dependency source fingerprints match; configuration unchanged.')
        return
    env = os.environ.copy()
    env['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
    lake = None
    if not args.configure_only:
        lake = shutil.which(os.path.expanduser(args.lake))
        if lake is None:
            parser.error('Activate Lean 4.32.1 or pass --lake; use --configure-only to defer Lake')
        lake = str(Path(lake).absolute())
        env['PATH'] = str(Path(lake).parent) + os.pathsep + env.get('PATH', '')
        version = subprocess.run([lake, '--version'], capture_output=True, text=True, check=True, env=env)
        if not re.search(r'Lean version 4\.32\.1(?:[,\s)]|$)', version.stdout):
            parser.error('Expected lake from Lean 4.32.1: ' + version.stdout.strip())
    subprocess.run([sys.executable, str(PROJECT / 'scripts/configure.py'),
                    '--mathlib', str(mathlib), '--geometry', str(geometry)], check=True, cwd=PROJECT)
    if lake:
        subprocess.run([lake, 'update'], check=True, cwd=PROJECT, env=env)
    print('Prepared. Run python3 scripts/verify.py with the same Lean toolchain.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
