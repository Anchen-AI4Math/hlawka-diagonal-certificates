"""Kernel-check every actual-norm localization slab and its retained floors."""
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,time
from fractions import Fraction as F
from pathlib import Path
from generate_localization_lean import generate,ROOT

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--jobs',type=int,choices=[1,2,3,4],default=2)
    parser.add_argument('--limit',type=int)
    parser.add_argument('--reuse',action='store_true',help='Reuse exact prior checks; omit for a fresh local replay')
    args=parser.parse_args()
    toolchain=(ROOT/'formalization/lean-toolchain').read_text().strip()
    native=Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))/'toolchains'/toolchain.replace('/','--').replace(':','---')/'bin'
    lake=native/('lake.exe' if os.name=='nt' else 'lake')
    env=os.environ.copy();env['PATH']=str(native)+os.pathsep+env.get('PATH','')
    project=ROOT/'formalization'
    if not (project/'.lake/packages/mathlib').exists():project=ROOT/'.test-tmp/prove2me/lean'
    rev=subprocess.check_output(['git','-C',str(project/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
    assert rev=='0df444a360eaa60ab8c11dca51a86af692955474'
    deps={f'formalization/Hlawka21/{name}.lean':sha(ROOT/f'formalization/Hlawka21/{name}.lean')
        for name in ['ContractionCore','ContractionRounds','ContractionFacts','NormBasic','NormGeometry',
            'Budget','Tail','RefinedTail','LinearFloors']}
    report_path=ROOT/'results/lean-localization-build.json'
    report=dict(status='RUNNING',toolchain=toolchain,mathlib_rev=rev,dependencies=deps,
        scope='Actual lpNorm data in the coarse box imply singleton caps, contracted coordinates and linear pair/offsum floors. Hessian positivity, averaging and the cutoff21 root are not proved here.',proofs=[])
    if args.reuse and report_path.exists():
        old=json.loads(report_path.read_text(encoding='utf-8'))
        if old.get('dependencies')==deps:report['proofs']=old['proofs']
    tasks=[]
    for cutoff in [21,26]:
        profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text(encoding='utf-8'))
        slabs=json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text(encoding='utf-8'))
        cursor=F(profile['p_min'])
        for slab in slabs:
            assert F(slab['a'])==cursor<F(slab['b']);cursor=F(slab['b'])
        assert cursor==F(profile['p_max'])
        for index,slab in enumerate(slabs[:args.limit]):
            path=generate(cutoff,index,slab,profile)
            dependency=ROOT/f'formalization/Hlawka21/Window{cutoff}/Slab{index:03d}.lean'
            tasks.append((f'Hlawka21.Localized{cutoff}.Slab{index:03d}',path,dependency))
        print('Generated actual-norm window',cutoff,len(slabs[:args.limit]),'slabs',flush=True)
    active={t[0] for t in tasks};report['proofs']=[r for r in report['proofs'] if r['module'] in active]
    logs=ROOT/'.test-tmp/prove2me/localization-logs';logs.mkdir(parents=True,exist_ok=True)
    def save():
        report['proofs'].sort(key=lambda r:r['module'])
        report_path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    def check(task):
        module,path,dependency=task;digest=sha(path);dependency_hash=sha(dependency)
        old=next((r for r in report['proofs'] if r['module']==module),None)
        if old and old.get('status')=='PASS' and old.get('sha256')==digest and old.get('schedule_sha256')==dependency_hash:return old
        started=time.monotonic()
        p=subprocess.run([str(lake),'build',module],cwd=project,env=env,capture_output=True,text=True,encoding='utf-8')
        output=p.stdout+p.stderr;(logs/(module+'.log')).write_text(output,encoding='utf-8')
        matches=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',output,re.S)
        axioms={x.strip() for match in matches for x in match.split(',')}
        ok=p.returncode==0 and bool(matches) and axioms <= {'propext','Classical.choice','Quot.sound'}
        record=dict(module=module,source=path.relative_to(ROOT).as_posix(),sha256=digest,
            schedule=dependency.relative_to(ROOT).as_posix(),schedule_sha256=dependency_hash,
            status='PASS' if ok else 'FAIL',root_certificates=3,axioms=sorted(axioms),
            elapsed_seconds=round(time.monotonic()-started,2))
        if not ok:record['errors']=[s for s in output.splitlines() if s.startswith('error:')][:8]
        return record
    save()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures=[pool.submit(check,t) for t in tasks]
        for count,future in enumerate(concurrent.futures.as_completed(futures),1):
            r=future.result();report['proofs']=[p for p in report['proofs'] if p['module']!=r['module']]+[r];save()
            print(f"{count}/{len(tasks)} {r['module']} {r['status']} {r['elapsed_seconds']}s",flush=True)
            if r['status']!='PASS':
                for f in futures:f.cancel()
                report['status']='FAIL';save();raise RuntimeError(r.get('errors'))
    report.update(status='PASS',slabs=len(tasks),root_certificates=3*len(tasks),complete_original_schedules=len(tasks)==256)
    save();print('PASS:',len(tasks),'actual-norm localization slabs',flush=True)

if __name__=='__main__':main()
