"""Build local platform-name mirrors sequentially from actual proved modules.

No sorry declarations or external theorem axioms are introduced. Sequential
dispatch avoids excessive simultaneous Lean file mappings on Windows.
"""
import argparse,json,os,subprocess
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--manifest',help='Build only the theorem_name mirrors listed in this public manifest')
    parser.add_argument('--keys',nargs='+',help='Build a fixed selection of keys from the manifest')
    args=parser.parse_args()
    toolchain=(ROOT/'formalization/lean-toolchain').read_text().strip()
    native=Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))/'toolchains'/toolchain.replace('/','--').replace(':','---')/'bin'
    lake=native/('lake.exe' if os.name=='nt' else 'lake')
    env=os.environ.copy();env['PATH']=str(native)+os.pathsep+env.get('PATH','')
    project=ROOT/'formalization'
    if not (project/'.lake/packages/mathlib').exists():project=ROOT/'.test-tmp/prove2me/lean'
    files=sorted((ROOT/'formalization/Theorems').glob('Thm_*.lean'))
    if args.manifest:
        entries=json.loads((ROOT/args.manifest).read_text(encoding='utf-8'))
        if args.keys:
            assert set(args.keys)<={item['key'] for item in entries},'Unknown selected mirror key'
            entries=[item for item in entries if item['key'] in args.keys]
        names={'Thm_'+item['theorem_name'].replace('.','_') for item in entries}
        files=[path for path in files if path.stem in names]
        assert {path.stem for path in files}==names,'Missing actual-proof theorem mirrors'
    elif args.keys:
        parser.error('--keys requires --manifest')
    if not files:raise RuntimeError('Generate the scalar platform proofs first')
    for i,path in enumerate(files,1):
        module='Theorems.'+path.stem
        result=subprocess.run([str(lake),'build',module],cwd=project,env=env,capture_output=True,text=True,encoding='utf-8')
        print(f'{i}/{len(files)} {module} {result.returncode}',flush=True)
        if result.returncode:
            print(result.stdout);print(result.stderr)
            raise RuntimeError('Local theorem mirror build failed: '+module)
    print('PASS: all local theorem mirrors import actual proofs.',flush=True)

if __name__=='__main__':main()
