"""Compile the exact proof files prepared for Prove2Me and audit their axioms."""
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--reuse',action='store_true',help='Reuse prior successful checks of unchanged self-contained files in the identical toolchain and Mathlib revision')
    parser.add_argument('--jobs',type=int,choices=[1,2,3,4],default=1)
    parser.add_argument('--lean-threads',type=int,choices=[1,2,4,8],help='Bound threads within each Lean process')
    parser.add_argument('--manifest',default='formalization/platform/payloads.json')
    parser.add_argument('--keys',nargs='+',help='Check only these keys from the published manifest; the report explicitly records the selection')
    parser.add_argument('--output',default='results/lean-auxiliary-build.json')
    args=parser.parse_args()
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
    payloads=json.loads((ROOT/args.manifest).read_text(encoding='utf-8'))
    if args.keys:
        requested=set(args.keys)
        assert requested <= {item['key'] for item in payloads},'Unknown selected proof key'
        payloads=[item for item in payloads if item['key'] in requested]
    old_report=ROOT/args.output
    previous=json.loads(old_report.read_text(encoding='utf-8')) if args.reuse and old_report.exists() else {}
    if previous.get('toolchain')!=toolchain or previous.get('mathlib_rev')!=head:previous={}
    def check(item):
        path=ROOT/item['solution_file']
        digest=hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest==item['solution_sha256']
        old=next((r for r in previous.get('proofs',[]) if r['key']==item['key']),None)
        if old and old.get('status')=='PASS' and old.get('sha256')==digest and set(old.get('axioms',[])) <= {'propext','Classical.choice','Quot.sound'}:
            print(item['key'],'prior exact-file check retained',flush=True)
            return old
        started=time.monotonic()
        command=[str(executable),'env','lean','-DautoImplicit=false']
        if args.lean_threads:command.append('-j'+str(args.lean_threads))
        result=subprocess.run(command+[str(path)],cwd=project,env=env,capture_output=True,text=True,encoding='utf-8')
        print(item['key'],result.returncode,flush=True)
        if result.returncode or 'sorryAx' in result.stdout:
            print(result.stdout);print(result.stderr)
            raise RuntimeError('Proof compilation or axiom check failed: '+item['key'])
        matches=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',result.stdout,re.S)
        assert matches,'Missing axiom audit: '+item['key']
        axioms=set()
        for match in matches:axioms.update(x.strip() for x in match.split(','))
        assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
        return dict(key=item['key'],status='PASS',solution_file=item['solution_file'],sha256=digest,axioms=sorted(axioms),elapsed_seconds=round(time.monotonic()-started,3))
    records=[];failures=[]
    order={item['key']:i for i,item in enumerate(payloads)}
    def save(status):
        records.sort(key=lambda r:order[r['key']])
        report=dict(status=status,toolchain=toolchain,mathlib_rev=head,proofs=records,manifest=args.manifest,
            scope=f'{len(records)} proof files from this manifest only. The cutoff21 root remains unproved.')
        if args.lean_threads:report['lean_threads']=args.lean_threads
        if args.keys:report['selected_keys']=args.keys
        if failures:report['failures']=failures
        (ROOT/args.output).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures={pool.submit(check,p):p['key'] for p in payloads}
        for f in concurrent.futures.as_completed(futures):
            try:records.append(f.result())
            except Exception as error:failures.append(dict(key=futures[f],error=str(error)))
            save('RUNNING')
    save('FAIL' if failures else 'PASS')
    if failures:raise RuntimeError(failures)
    print('PASS: exact submitted proof files compile and use only standard axioms.',flush=True)

if __name__=='__main__':main()
