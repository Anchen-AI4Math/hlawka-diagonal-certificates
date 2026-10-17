"""Replay both published windows without third-party packages.

Run from the repository root: python -S scripts/replay_release.py
This checks finite obligations, not the analytic proof or the cited Lean tail.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    jobs = []
    for cutoff in (21, 26):
        for script, kind in [('verify.py', 'verification'), ('negative_controls.py', 'negative')]:
            output = f'results/release-{cutoff}-{kind}.json'
            command = [sys.executable, '-S', f'scripts/{script}', '--backend', 'rational',
                       '--profile', f'profiles/cutoff{cutoff}.json',
                       '--directory', f'certificates/cutoff{cutoff}', '--output', output]
            if script == 'verify.py':
                command += ['--precision', '256']
            print(f'Replaying cutoff {cutoff}: {kind}', flush=True)
            subprocess.run(command, cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
            jobs.append(output)
    provenance = json.loads((ROOT / 'sources/provenance.json').read_text(encoding='utf-8'))
    for name, expected in provenance['files'].items():
        actual = hashlib.sha256((ROOT / 'sources' / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f'Upstream source hash mismatch: {name}')
    inputs = sorted(set(ROOT.glob('scripts/*.py')) | set(ROOT.glob('profiles/*.json')) |
                    set(ROOT.glob('certificates/cutoff21/*.json')) |
                    set(ROOT.glob('certificates/cutoff26/*.json')))
    report = dict(status='PASS', python=sys.version, windows=[['21', '26'], ['26', '32']],
                  backend='standard-library dyadic rational intervals', precision_bits=256,
                  checks=jobs, upstream_source_hashes_checked=len(provenance['files']),
                  scope='Finite obligations and rejection controls; no Lean rebuild or independent analytic review.',
                  input_sha256={p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in inputs})
    (ROOT / 'results/release-replay.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print('PASS: both windows, rejection controls, and preserved source hashes.', flush=True)

if __name__ == '__main__':
    main()
