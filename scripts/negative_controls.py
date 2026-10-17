"""Check that damaged coverage, witnesses, round order and LP duals are rejected."""
import copy,json,tempfile
from pathlib import Path
from verify import verify

def run(backend='arb',directory=Path('certificates'),profile=None,output=None):
    source={p.name:json.loads(p.read_text()) for p in directory.glob('*.json')}
    def gap(d): d['scalar.json'][0]['a']='3175001/100000'
    def witness(d): d['scalar.json'][0]['t']='1/2'
    def chain(d): d['contractor.json'][0]['rounds'][1]['n']='1'
    def dual(d): d['coarse.json']['stages'][0][0]['dual_ineq'][0]='1'
    def missing(d): d['cyclic-upper.json'][0]['t_cells'].pop()
    def final_box(d): d['contractor.json'][0]['final']['box']['diag_max']='1/10'
    results=[]
    mutations=[gap,witness,chain,dual,missing]+([final_box] if profile else [])
    for mutate in mutations:
        data=copy.deepcopy(source); mutate(data)
        workspace=Path(__file__).resolve().parents[1]
        scratch=workspace/'.test-tmp'; scratch.mkdir(exist_ok=True)
        temp=tempfile.TemporaryDirectory(prefix='hlawka-control-',dir=scratch)
        Path(temp.name).resolve().relative_to(workspace)
        with temp as folder:
            root=Path(folder)
            for name,value in data.items(): (root/name).write_text(json.dumps(value))
            try: verify(root,256,backend,profile)
            except ValueError as exc: results.append(dict(control=mutate.__name__,backend=backend,status='REJECTED',reason=str(exc)))
            else: raise RuntimeError('Corrupted certificate accepted: '+mutate.__name__)
    if profile:
        bad_profile=copy.deepcopy(profile); bad_profile['young_epsilon_1']='1000000'
        try: verify(directory,256,backend,bad_profile)
        except ValueError as exc: results.append(dict(control='curvature',backend=backend,status='REJECTED',reason=str(exc)))
        else: raise RuntimeError('Invalid geometry accepted')
    filename='negative-controls.json' if backend=='arb' else 'negative-controls-rational.json'
    destination=output or Path('results',filename)
    destination.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(); parser.add_argument('--backend',choices=['arb','rational'],default='arb'); parser.add_argument('--directory',type=Path,default=Path('certificates')); parser.add_argument('--profile',type=Path); parser.add_argument('--output',type=Path)
    args=parser.parse_args(); profile=json.loads(args.profile.read_text()) if args.profile else None
    run(args.backend,args.directory,profile,args.output)
