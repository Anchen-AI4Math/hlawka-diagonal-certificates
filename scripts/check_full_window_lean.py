"""Replay every new cutoff21 ingredient, with an explicit accepted-tail interface."""
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
    targets = ['Hlawka21.FullWindow']
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
            if imported.startswith(('Hlawka21.', 'Definitions.', 'Theorems.')):
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
    required = ['HlawkaSchatten.DiagonalCutoff21.'+name for name in [
        'real_three_window21','real_three_window26','complex_least_of_real_three','campaign_cutoff21_from_tail']]
    ok = result.returncode == 0 and all(name in checks for name in required)
    ok = ok and all(set(values) <= ALLOWED for values in checks.values())
    for path, digest in sources.items():
        assert sha(ROOT / path) == digest, f'Source changed during build: {path}'
    report = dict(status='PASS' if ok else 'FAIL', toolchain=toolchain, mathlib_rev=rev,
                  modules=targets, sources=sources, axiom_checks=checks,
                  elapsed_seconds=round(time.monotonic()-started, 2),
                  scope='Both unchanged unrestricted real-three window statements and the generic finite-complex-dimensional IsLeast transfer are proved with actual source imports, including dimension zero. The exact cutoff21 conclusion is locally proved conditional only on an explicit cutoff32 tail input. That tail is already Proved on Prove2Me but is not independently rebuilt here; the final server proof must close that dependency and all new components before the original full goal is complete.')
    (ROOT / 'results/lean-full-window-build.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(report['status'], len(sources), 'source hashes;', len(checks), 'axiom checks')
    if not ok:
        print('\n'.join(output.splitlines()[-30:]))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
