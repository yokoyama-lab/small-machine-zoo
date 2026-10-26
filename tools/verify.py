#!/usr/bin/env python3
"""Build the paper targets and check their axiom dependencies; fail closed."""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def run(argv, project, log):
    print(f"{project}: {' '.join(argv)}", flush=True)
    env = dict(os.environ)
    env.setdefault('LEAN_NUM_THREADS', '4')
    with log.open('w') as output:
        result = subprocess.run(argv, cwd=ROOT / project, env=env,
                                stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text()[-6000:])
        raise SystemExit(f"FAILED ({result.returncode}); see {log.relative_to(ROOT)}")
    print(f"PASS: {log.relative_to(ROOT)}", flush=True)

def check_copies():
    modern = ROOT / 'lean-univ/LeanUniv'
    legacy = ROOT / 'legacy/small-urtm/lean-meta/URTMMeta'
    if (modern/'Spec.lean').read_bytes() != (legacy/'Spec.lean').read_bytes():
        raise SystemExit('FAIL: Spec.lean copies differ')
    def without_imports(path):
        return '\n'.join(x for x in path.read_text().splitlines() if not x.startswith('import '))
    if without_imports(modern/'Strict.lean') != without_imports(legacy/'Strict.lean'):
        raise SystemExit('FAIL: Strict.lean copies differ beyond import paths')
    print('PASS: copied Spec and Strict definitions', flush=True)

def check_roots():
    manifest = json.loads((ROOT/'docs/source-manifest.json').read_text())
    for key, entry in [('existence_roots','lean-univ/LeanUniv.lean'),
                       ('nonexistence_roots','legacy/small-urtm/lean-meta/URTMMeta.lean'),
                       ('trace_roots','lean/PaperTraces.lean')]:
        imported = [x.split()[1] for x in (ROOT/entry).read_text().splitlines()
                    if x.startswith('import ')]
        if sorted(imported) != sorted(manifest[key]):
            raise SystemExit(f'FAIL: {entry} does not import exactly the {key} of the manifest')
    print('PASS: entry modules import exactly the manifest roots', flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', choices=['all','existence','nonexistence','traces'], default='all')
    args = parser.parse_args()
    logs = ROOT / 'out/verification'
    logs.mkdir(parents=True, exist_ok=True)
    check_copies()
    check_roots()
    for name, project, target in [
        ('existence','lean-univ','LeanUniv'),
        ('nonexistence','legacy/small-urtm/lean-meta','URTMMeta'),
        ('traces','lean','PaperTraces'),
    ]:
        if args.target not in ('all',name): continue
        run(['lake','build',target],project,logs/(name+'-build.log'))
        run(['lake','env','lean','tests/AxSweep.lean'],project,logs/(name+'-axioms.log'))
    print('All requested checks passed.', flush=True)

if __name__ == '__main__':
    main()
