"""Generate and kernel-check both complete scalar lower-bound windows."""
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,time
from pathlib import Path
from fractions import Fraction as F
from generate_scalar_lower_lean import generate,data,ROOT,CHUNK

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--jobs',type=int,choices=[1,2,3,4],default=2)
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
    deps={f'formalization/Hlawka21/{name}.lean':sha(ROOT/f'formalization/Hlawka21/{name}.lean')
        for name in ['FixedWitness','CyclicUpper','ContractionCore','Tail']}
    defs=ROOT/'formalization/Definitions/Def_HlawkaSchatten_DiagonalConstruction_Cyclic.lean'
    deps[defs.relative_to(ROOT).as_posix()]=sha(defs)
    report_path=ROOT/'results/lean-scalar-build.json'
    report=dict(status='RUNNING',toolchain=toolchain,mathlib_rev=rev,dependencies=deps,
        scope='The two scalar lower-bound windows only; full cutoff21 root remains open.',proofs=[])
    if args.reuse and report_path.exists():
        old=json.loads(report_path.read_text(encoding='utf-8'))
        if old.get('dependencies')==deps:report['proofs']=old['proofs']
    tasks=[]
    for cutoff in [21,26]:
        profile_path=ROOT/f'profiles/cutoff{cutoff}.json';schedule_path=ROOT/f'certificates/cutoff{cutoff}/contractor.json'
        profile=json.loads(profile_path.read_text());slabs=json.loads(schedule_path.read_text())
        cursor=F(profile['p_min'])
        for s in slabs:
            assert F(s['a'])==cursor<F(s['b']);cursor=F(s['b'])
        assert cursor==F(profile['p_max'])
        rows=[{k:str(v) for k,v in data(cutoff,s,profile).items()} for s in slabs]
        cert=dict(cutoff=cutoff,scope='Three exact endpoint root inequalities per slab, with a fixed rational cyclic witness.',
            profile_sha256=sha(profile_path),schedule_sha256=sha(schedule_path),slabs=rows)
        (ROOT/f'certificates/lean-scalar-cutoff{cutoff}.json').write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8')
        for chunk in range((len(slabs)+CHUNK-1)//CHUNK):
            path,records=generate(cutoff,chunk,slabs,profile)
            tasks.append((f'Hlawka21.Scalar{cutoff}.Chunk{chunk:02d}',path,len(records)))
        print('Generated scalar window',cutoff,len(slabs),'slabs',flush=True)
    logs=ROOT/'.test-tmp/prove2me/scalar-logs';logs.mkdir(parents=True,exist_ok=True)
    def save():
        report['proofs'].sort(key=lambda r:r['module'])
        report_path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    def check(task):
        module,path,slabs=task;digest=sha(path)
        old=next((r for r in report['proofs'] if r['module']==module),None)
        if old and old.get('status')=='PASS' and old.get('sha256')==digest:return old
        start=time.monotonic()
        p=subprocess.run([str(lake),'build',module],cwd=project,env=env,capture_output=True,text=True,encoding='utf-8')
        output=p.stdout+p.stderr;(logs/(module+'.log')).write_text(output,encoding='utf-8')
        matches=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',output,re.S)
        axioms={x.strip() for match in matches for x in match.split(',')}
        ok=p.returncode==0 and bool(matches) and axioms<={'propext','Classical.choice','Quot.sound'}
        record=dict(module=module,source=path.relative_to(ROOT).as_posix(),sha256=digest,status='PASS' if ok else 'FAIL',
            slabs=slabs,integer_power_certificates=3*slabs,axioms=sorted(axioms),elapsed_seconds=round(time.monotonic()-start,2))
        if not ok:record['errors']=[s for s in output.splitlines() if s.startswith('error:')][:5]
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
    report.update(status='PASS',chunks=len(tasks),slabs=sum(r['slabs'] for r in report['proofs']),
        integer_power_certificates=sum(r['integer_power_certificates'] for r in report['proofs']),complete_scalar_windows=True)
    save();print('PASS: both complete scalar lower-bound windows',flush=True)

if __name__=='__main__':main()
