"""Generate and compile the complete original contraction schedules in Lean.

Runs at most four independent module builds. Exact source and dependency
hashes guard reuse of previously completed checks; every new source is
compiled by the pinned Lean toolchain and its printed axioms are audited.
"""
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,time
from pathlib import Path
from generate_contractor_lean import generate,ROOT

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--jobs',type=int,default=4,choices=[1,2,3,4])
    parser.add_argument('--limit',type=int)
    parser.add_argument('--reuse',action='store_true',help='Reuse previously completed checks; omit for a fresh local replay')
    args=parser.parse_args()
    toolchain=(ROOT/'formalization/lean-toolchain').read_text().strip()
    native=Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))/'toolchains'/toolchain.replace('/','--').replace(':','---')/'bin'
    lake=native/('lake.exe' if os.name=='nt' else 'lake')
    env=os.environ.copy();env['PATH']=str(native)+os.pathsep+env.get('PATH','')
    project=ROOT/'formalization'
    if not (project/'.lake/packages/mathlib').exists():project=ROOT/'.test-tmp/prove2me/lean'
    rev=subprocess.check_output(['git','-C',str(project/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
    assert rev=='0df444a360eaa60ab8c11dca51a86af692955474'
    report_path=ROOT/'results/lean-contraction-build.json'
    deps={p.relative_to(ROOT).as_posix():sha(p) for p in [ROOT/'formalization/Hlawka21/ContractionCore.lean',ROOT/'formalization/Hlawka21/ContractionRounds.lean']}
    report=dict(status='RUNNING',toolchain=toolchain,mathlib_rev=rev,dependencies=deps,
        scope='Conditional contraction from Facts and initial lower bound; not the cutoff21 root proof.',proofs=[])
    if args.reuse and report_path.exists():
        old=json.loads(report_path.read_text(encoding='utf-8'))
        if old.get('dependencies')==deps:report['proofs']=old['proofs']
    logs=ROOT/'.test-tmp/prove2me/contraction-logs';logs.mkdir(parents=True,exist_ok=True)
    tasks=[]
    for cutoff in [21,26]:
        profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
        slabs=json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text())
        from fractions import Fraction
        cursor=Fraction(profile['p_min'])
        for slab in slabs:
            assert Fraction(slab['a'])==cursor<Fraction(slab['b'])
            cursor=Fraction(slab['b'])
        assert cursor==Fraction(profile['p_max'])
        for index,slab in enumerate(slabs[:args.limit]):
            path,count=generate(cutoff,index,slab,profile)
            module=f'Hlawka21.Window{cutoff}.Slab{index:03d}'
            tasks.append((module,path,count))
        print('Generated window',cutoff,len(slabs[:args.limit]),'slabs',flush=True)
    active={t[0] for t in tasks}
    report['proofs']=[r for r in report['proofs'] if r['module'] in active]
    def save():
        report['proofs'].sort(key=lambda r:r['module'])
        report_path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    def check(task):
        module,path,count=task
        digest=sha(path)
        old=next((r for r in report['proofs'] if r['module']==module),None)
        if old and old.get('status')=='PASS' and old.get('sha256')==digest:return old
        started=time.monotonic()
        process=subprocess.run([str(lake),'build',module],cwd=project,env=env,capture_output=True,text=True,encoding='utf-8')
        output=process.stdout+process.stderr
        (logs/(module+'.log')).write_text(output,encoding='utf-8')
        matches=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',output,re.S)
        axioms={x.strip() for m in matches for x in m.split(',')}
        ok=process.returncode==0 and bool(matches) and axioms <= {'propext','Classical.choice','Quot.sound'}
        record=dict(module=module,status='PASS' if ok else 'FAIL',source=path.relative_to(ROOT).as_posix(),
            sha256=digest,power_comparisons=count,axioms=sorted(axioms),elapsed_seconds=round(time.monotonic()-started,2))
        if not ok:record['errors']=[line for line in output.splitlines() if line.startswith('error:')][:5]
        return record
    save()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures={pool.submit(check,t):t for t in tasks}
        for completed,future in enumerate(concurrent.futures.as_completed(futures),1):
            result=future.result()
            report['proofs']=[r for r in report['proofs'] if r['module']!=result['module']]+[result]
            save()
            print(f"{completed}/{len(tasks)} {result['module']} {result['status']} {result['elapsed_seconds']}s",flush=True)
            if result['status']!='PASS':
                for f in futures:f.cancel()
                report['status']='FAIL';save()
                raise RuntimeError(result.get('errors'))
    report['status']='PASS';report['slabs']=len(tasks)
    report['complete_original_schedules']=len(tasks)==256
    save()
    print('PASS:',len(tasks),'conditional slab proofs',flush=True)

if __name__=='__main__':main()
