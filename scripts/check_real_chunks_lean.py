"""Kernel-check all sixteen localization-to-nonnegativity chunks."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, choices=[1,2,3,4], default=2)
    args = parser.parse_args()
    manifest = json.loads((ROOT/'formalization/real-chunks.json').read_text())
    assert len(manifest) == 16
    for cutoff, lo, hi, count in [(21, '21', '26', 160), (26, '26', '32', 96)]:
        rows = [r for r in manifest if r['cutoff'] == cutoff]
        assert rows[0]['a'] == lo and rows[-1]['b'] == hi
        assert rows[0]['start'] == 0 and rows[-1]['end'] == count
        for left,right in zip(rows,rows[1:]):
            assert left['b'] == right['a'] and left['end'] == right['start']
    for row in manifest:
        assert sha(ROOT/row['source']) == row['sha256']
    for report in ['lean-localization-build.json','lean-geometry-build.json']:
        assert json.loads((ROOT/'results'/report).read_text())['status'] == 'PASS'
    toolchain = (ROOT/'formalization/lean-toolchain').read_text().strip()
    native = Path(os.environ.get('ELAN_HOME', str(Path.home()/'.elan')))/'toolchains'/toolchain.replace('/','--').replace(':','---')/'bin'
    lake = native/('lake.exe' if os.name == 'nt' else 'lake')
    project = ROOT/'formalization'
    if not (project/'.lake/packages/mathlib').exists():
        project = ROOT/'.test-tmp/prove2me/lean'
    revision = subprocess.check_output(['git','-C',str(project/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
    assert revision == '0df444a360eaa60ab8c11dca51a86af692955474'
    env = os.environ.copy()
    env['PATH'] = str(native)+os.pathsep+env.get('PATH','')
    sources = {}

    def visit(module):
        path = ROOT/'formalization'/(module.replace('.','/')+'.lean')
        key = path.relative_to(ROOT).as_posix()
        if key in sources:
            return
        sources[key] = sha(path)
        if module.startswith('Definitions.'):
            assert sha(project/(module.replace('.','/')+'.lean')) == sources[key]
        for imported in re.findall(r'^import\s+(\S+)',path.read_text(encoding='utf-8'),re.M):
            if imported.startswith(('Hlawka21.','Definitions.','Theorems.')):
                visit(imported)
    for row in manifest:
        visit(row['module'])
    out = ROOT/'results/lean-real-chunks-build.json'
    report = dict(status='RUNNING',toolchain=toolchain,mathlib_rev=revision,sources=sources,
                  scope='Nonnegativity on every actual-norm localized coarse-box configuration for the two original real windows; arbitrary-counterexample reduction and the full cutoff21 goal are separate assemblies.',proofs=[])
    logs = ROOT/'.test-tmp/prove2me/real-chunk-logs'
    logs.mkdir(parents=True,exist_ok=True)

    def save():
        report['proofs'].sort(key=lambda r:r['module'])
        out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')

    def check(row):
        started = time.monotonic()
        result = subprocess.run([str(lake),'build',row['module']],cwd=project,env=env,
                                capture_output=True,text=True,encoding='utf-8')
        output = result.stdout+result.stderr
        (logs/(row['module']+'.log')).write_text(output,encoding='utf-8')
        matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S)
        checks = {name:{x.strip() for x in value.split(',') if x.strip()} for name,value in matches}
        target = 'HlawkaSchatten.DiagonalCutoff21.'+row['theorem']
        ok = result.returncode == 0 and target in checks and all(v <= {'propext','Classical.choice','Quot.sound'} for v in checks.values())
        return dict(module=row['module'],source=row['source'],sha256=row['sha256'],
                    status='PASS' if ok else 'FAIL',axioms=sorted(checks.get(target,set())),
                    elapsed_seconds=round(time.monotonic()-started,2),
                    errors=[line for line in output.splitlines() if line.startswith('error:')][:8])
    save()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(check,row) for row in manifest]
        for future in concurrent.futures.as_completed(futures):
            record = future.result()
            report['proofs'].append(record)
            save()
            print(len(report['proofs']),'/16',record['module'],record['status'],flush=True)
    assert all(sha(ROOT/path) == digest for path,digest in sources.items())
    report['status'] = 'PASS' if all(r['status']=='PASS' for r in report['proofs']) else 'FAIL'
    report.update(chunks=len(manifest),slabs=256)
    save()
    print(report['status'],flush=True)
    if report['status'] != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
