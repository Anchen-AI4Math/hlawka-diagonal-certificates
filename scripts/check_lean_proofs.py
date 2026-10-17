"""Compile the exact proof files prepared for Prove2Me and audit their axioms."""
import hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main():
    toolchain=(ROOT/'formalization/lean-toolchain').read_text().strip()
    native=Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))/'toolchains'/toolchain.replace('/','--').replace(':','---')/'bin'
    executable=native/('lake.exe' if os.name=='nt' else 'lake')
    env=os.environ.copy()
    if executable.exists():env['PATH']=str(native)+os.pathsep+env.get('PATH','')
    else:
        executable=shutil.which('lake')
        if not executable:raise RuntimeError('Install the pinned Lean toolchain first')
        env['ELAN_TOOLCHAIN']=toolchain
    project=ROOT/'formalization'
    if not (project/'.lake/packages/mathlib').exists():
        project=ROOT/'.test-tmp/prove2me/lean'
    if not (project/'.lake/packages/mathlib').exists():
        raise RuntimeError('Run lake update and lake exe cache get in formalization first')
    head=subprocess.check_output(['git','-C',str(project/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
    assert head=='0df444a360eaa60ab8c11dca51a86af692955474'
    payloads=json.loads((ROOT/'formalization/platform/payloads.json').read_text(encoding='utf-8'))
    records=[]
    for item in payloads:
        path=ROOT/item['solution_file']
        digest=hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest==item['solution_sha256']
        started=time.monotonic()
        result=subprocess.run([str(executable),'env','lean','-DautoImplicit=false',str(path)],cwd=project,env=env,capture_output=True,text=True,encoding='utf-8')
        print(item['key'],result.returncode,flush=True)
        if result.returncode or 'sorryAx' in result.stdout:
            print(result.stdout);print(result.stderr)
            raise RuntimeError('Proof compilation or axiom check failed: '+item['key'])
        matches=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',result.stdout,re.S)
        assert matches,'Missing axiom audit: '+item['key']
        axioms=set()
        for match in matches:axioms.update(x.strip() for x in match.split(','))
        assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
        records.append(dict(key=item['key'],status='PASS',solution_file=item['solution_file'],sha256=digest,axioms=sorted(axioms),elapsed_seconds=round(time.monotonic()-started,3)))
    report=dict(status='PASS',toolchain=toolchain,mathlib_rev=head,proofs=records,scope=f'{len(records)} auxiliary proofs only. The cutoff21 root remains unproved.')
    (ROOT/'results/lean-auxiliary-build.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('PASS: exact submitted proof files compile and use only standard axioms.',flush=True)

if __name__=='__main__':main()
