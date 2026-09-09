#!/usr/bin/env python3
"""Point this project at existing, pinned dependency checkouts. No downloads."""
import argparse
import json
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1]
TEMPLATE = '''import Lake
open Lake DSL

package CurveControl where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩]

require mathlib from {mathlib}
require MorganTianLib from {geometry}

@[default_target] lean_lib CurveControl
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib', type=Path, required=True,
                        help='Existing mathlib4 checkout at 520045ab14e26149ee970e2e617ca04b09bde5d6')
    parser.add_argument('--geometry', type=Path, required=True,
                        help='Existing frenzymath/Poincare-Conjecture snapshot at bb91a091f0b968f8bbe8d861e025a88d82b161be')
    parser.add_argument('--print-only', action='store_true', help='Print configuration without writing')
    args = parser.parse_args()
    mathlib = args.mathlib.resolve()
    geometry = args.geometry.resolve() / 'formalized-sources' / 'MorganTian'
    for directory, marker in [(mathlib, 'Mathlib'), (geometry, 'MorganTianLib')]:
        if not (directory / marker).is_dir():
            parser.error(f'Missing source directory: {directory / marker}')
        toolchain = (directory / 'lean-toolchain').read_text().strip()
        if toolchain != 'leanprover/lean4:v4.32.1':
            parser.error(f'Expected Lean 4.32.1 in {directory}; found {toolchain}')
    config = TEMPLATE.format(mathlib=json.dumps(str(mathlib)), geometry=json.dumps(str(geometry)))
    if args.print_only:
        print(config, end='')
    else:
        (PROJECT / 'lakefile.lean').write_text(config)
        print('Configured existing dependencies. Run lake update, then lake build CurveControl.')

if __name__ == '__main__':
    main()
