"""Replay the two actual Hessian/convexity assemblies and record exact inputs."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    project = ROOT / 'formalization'
    if not (project / '.lake/packages/mathlib').exists():
        project = ROOT / '.test-tmp/prove2me/lean'
    toolchain = (ROOT / 'formalization/lean-toolchain').read_text().strip()
    native = Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan'))) / 'toolchains' / toolchain.replace('/', '--').replace(':', '---') / 'bin'
    lake = native / ('lake.exe' if os.name == 'nt' else 'lake')
    env = os.environ.copy()
    env['PATH'] = str(native) + os.pathsep + env.get('PATH', '')
    rev = subprocess.check_output(['git', '-C', str(project / '.lake/packages/mathlib'), 'rev-parse', 'HEAD'], text=True).strip()
    assert rev == '0df444a360eaa60ab8c11dca51a86af692955474'
    targets = [f'Hlawka21.GroupedNonneg.Group{i:02d}' for i in range(2)]
    sources = {}

    def visit(module):
        path = ROOT / 'formalization' / (module.replace('.', '/') + '.lean')
        key = path.relative_to(ROOT).as_posix()
        if key in sources:
            return
        sources[key] = sha(path)
        if module.startswith('Definitions.'):
            cached = project / (module.replace('.', '/') + '.lean')
            assert cached.exists() and sha(cached) == sources[key], f'Definition copy mismatch: {module}'
        for imported in re.findall(r'^import\s+(\S+)', path.read_text(encoding='utf-8'), re.M):
            if imported.startswith(('Hlawka21.', 'Definitions.')):
                visit(imported)
    for target in targets:
        visit(target)
    started = time.monotonic()
    result = subprocess.run([str(lake), 'build', *targets], cwd=project, env=env,
                            capture_output=True, text=True, encoding='utf-8')
    output = result.stdout + result.stderr
    log = ROOT / '.test-tmp/prove2me/geometry-replay.log'
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(output, encoding='utf-8')
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    checks = {name: sorted(x.strip() for x in values.split(',') if x.strip()) for name, values in matches}
    required = [f'HlawkaSchatten.DiagonalCutoff21.{kind}{i:02d}'
                for i in range(2) for kind in ['grouped_deficit_hessian', 'grouped_deficit_convex', 'grouped_deficit_nonneg']]
    required += ['HlawkaSchatten.DiagonalCutoff21.normDomain_deficit_nonneg_of_convex',
                 'HlawkaSchatten.DiagonalCutoff21.cyclicConstant_bounds_window']
    ok = result.returncode == 0 and all(name in checks for name in required)
    ok = ok and all(set(values) <= ALLOWED for values in checks.values())
    for path, digest in sources.items():
        assert sha(ROOT / path) == digest, f'Source changed during build: {path}'
    report = dict(status='PASS' if ok else 'FAIL', toolchain=toolchain, mathlib_rev=rev,
                  modules=targets, sources=sources, axiom_checks=checks,
                  elapsed_seconds=round(time.monotonic()-started, 2),
                  scope='Two grouped norm-capped domains have parameter ranges covering [21,32]. The actual cyclicConstant deficit is nonnegative on each domain, using actual scalar-milestone proofs, Hessian bounds, convexity and simultaneous permutation averaging. Placing all localized slabs in these domains, the arbitrary-real-three theorem and the original full cutoff21 goal are not assembled here.')
    (ROOT / 'results/lean-geometry-build.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(report['status'], len(sources), 'source hashes;', len(checks), 'axiom checks')
    if not ok:
        print('\n'.join(output.splitlines()[-30:]))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
