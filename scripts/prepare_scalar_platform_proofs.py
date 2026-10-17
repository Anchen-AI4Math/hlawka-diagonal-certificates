"""Export the fixed-witness lower bounds and reconnect the original milestones."""
import hashlib,json
from pathlib import Path
from fractions import Fraction as F
from generate_contractor_lean import ROOT,rat

OUT=ROOT/'formalization/platform'
SOURCE='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . '
report=json.loads((ROOT/'results/lean-scalar-build.json').read_text(encoding='utf-8'))
assert report['status']=='PASS' and report['complete_scalar_windows'] and report['slabs']==256

def bundle(names):
    imports=[];bodies=[]
    for name in names:
        code=(ROOT/f'formalization/Hlawka21/{name}.lean').read_text(encoding='utf-8')
        for line in code.splitlines():
            if line.startswith(('import Mathlib.','import Definitions.')) and line not in imports:imports.append(line)
        bodies.append('\n'.join(l for l in code.splitlines() if not l.startswith(('import ','#print axioms '))))
    preamble='\n'.join(imports)+'\nopen HlawkaSchatten.DiagonalConstruction\n'
    return preamble,preamble+'\n'+'\n'.join(bodies)+'\n'

def partition_tree(lines,cutoff,indices,bounds,lo,hi,indent='    ',prefix='h'):
    if len(indices)==1:
        lines.append(indent+f'exact HlawkaSchatten.DiagonalCutoff21.lower{cutoff}_chunk{indices[0]:02d} p {lo} {hi}')
        return
    n=len(indices)//2;mid=bounds[indices[n]][0];hl,hr=prefix+'l',prefix+'r'
    lines.append(indent+f'rcases le_total p {rat(mid)} with {hl} | {hr}')
    lines.append(indent+'·');partition_tree(lines,cutoff,indices[:n],bounds,lo,hl,indent+'  ',prefix+'a')
    lines.append(indent+'·');partition_tree(lines,cutoff,indices[n:],bounds,hr,hi,indent+'  ',prefix+'b')

payloads=json.loads((OUT/'payloads.json').read_text(encoding='utf-8'))
payloads=[p for p in payloads if not p['key'].startswith('scalar_lower_')]
theorems=ROOT/'formalization/Theorems';theorems.mkdir(exist_ok=True)
wrappers=[];missions=[]
for cutoff in [21,26]:
    profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
    lo,hi,c=map(F,(profile[k] for k in ['p_min','p_max','c']))
    q=F(profile['q']);chunk_bounds={};chunk_names=[]
    chunks=sorted((ROOT/f'formalization/Hlawka21/Scalar{cutoff}').glob('Chunk*.lean'))
    for index,path in enumerate(chunks):
        name=f'HlawkaSchatten.DiagonalCutoff21.lower{cutoff}_chunk{index:02d}'
        code=path.read_text(encoding='utf-8');start=code.index(f'theorem lower{cutoff}_chunk{index:02d}')
        signature=code[start:code.index(' := by',start)]
        statement=signature.replace(f'theorem lower{cutoff}_chunk{index:02d}','theorem '+name)+' := by sorry'
        source_slabs=json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text())[index*16:(index+1)*16]
        a,b=F(source_slabs[0]['a']),F(source_slabs[-1]['b']);chunk_bounds[index]=(a,b)
        preamble,solution=bundle(['Tail','CyclicUpper','ContractionCore','FixedWitness',f'Scalar{cutoff}/Chunk{index:02d}'])
        solution+=statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',' := by\n  exact '+name+' p hpa hpb')+'\n\n#print axioms solution\n'
        file=f'Sol_scalar_lower_{cutoff}_{index:02d}.lean';(OUT/file).write_text(solution,encoding='utf-8')
        t='17/20' if cutoff==21 else '87/100'
        payloads.append(dict(key=f'scalar_lower_{cutoff}_{index:02d}',theorem_name=name,
            theorem_title=f'Fixed cyclic witness: Kp > ({c})p for real p in [{a},{b}]',
            formal_statement=statement,preamble=preamble,
            natural_language_statement=rf'''For every real $p\in[{a},{b}]$, the cyclic Hlawka constant satisfies $({c})p<K_p$. Here $K_p$ is the source paper's supremum of the cyclic ratio over $1/2\le t\le2$. The same fixed rational witness $t={t}$ works on the entire interval, which contains sixteen adjacent closed subintervals. This is a lower-bound component of the scalar-window target, with no numerical-check predicate as a hypothesis.''',
            source=SOURCE+f'Section 2, equation (7), linear lower-bound component. Fixed-witness Bernoulli proof and exact certificates: certificates/lean-scalar-cutoff{cutoff}.json, slabs {index*16} through {index*16+15}.',
            tags=['hlawka-schatten','real-analysis','exact-arithmetic'],solution_file='formalization/platform/'+file,
            explanation='At each left endpoint alpha, three rational integer-power comparisons bound t^alpha, (2+t^alpha)^(1/alpha), and 3^(1/alpha) from above. Bernoulli transports the two root bounds to every real p>=alpha. The cyclic pair norm is at least two. Substitution into the cyclic ratio reduces the desired strict lower bound to a single rational inequality, whose worst reciprocal p occurs at the right endpoint beta. A balanced finite case split covers all sixteen real subintervals. Finally the already-proved upper bound makes the cyclic-ratio image bounded, so the witness ratio is at most its supremum Kp. All arithmetic and helper proofs are included.'))
        wrapper='Thm_'+name.replace('.','_')
        (theorems/(wrapper+'.lean')).write_text(f'import Hlawka21.Scalar{cutoff}.Chunk{index:02d}\n',encoding='utf-8')
        wrappers.append('Theorems.'+wrapper);chunk_names.append('Theorems.'+wrapper)
    for name,module in [(f'HlawkaSchatten.DiagonalCutoff21.envelope_linear{cutoff}','Envelope'),
        ('HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21','CyclicUpper')]:
        wrapper='Thm_'+name.replace('.','_')
        (theorems/(wrapper+'.lean')).write_text('import Hlawka21.'+module+'\n',encoding='utf-8')
        wrappers.append('Theorems.'+wrapper);chunk_names.append('Theorems.'+wrapper)
    original=(ROOT/f'platform/proposal/scalar{cutoff}.lean').read_text(encoding='utf-8')
    begin=original.index('theorem ');original=original[begin:]
    target=f'HlawkaSchatten.DiagonalCutoff21.scalar_window{cutoff}'
    lines=['import '+n for n in chunk_names]+['','open HlawkaSchatten.DiagonalConstruction','',
        original.replace('theorem '+target,'theorem solution').replace(' := by sorry',' := by').strip(),
        '  intro p hp hpmax',f'  have hlower : {rat(c)}*p < cyclicConstant p := by']
    partition_tree(lines,cutoff,list(range(len(chunks))),chunk_bounds,'hp','hpmax')
    lines.extend(['  refine ⟨hlower, ?_, ?_⟩',
        '  · exact HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21 (by linarith) (by linarith)',
        f'  · exact (HlawkaSchatten.DiagonalCutoff21.envelope_linear{cutoff} hp).trans hlower',
        '', '#print axioms solution',''])
    file=f'Sol_scalar_window{cutoff}.lean';(OUT/file).write_text('\n'.join(lines),encoding='utf-8')
    missions.append(dict(key=f'scalar_window{cutoff}',theorem_id='2b5def5c-82ab-4480-bbcb-1d11f05b7cbe' if cutoff==21 else 'bfa2ef01-7ed9-4ac2-93ec-ace2d0624fda',
        theorem_name=target,solution_file='formalization/platform/'+file,
        explanation='The fixed rational cyclic witness gives cp<Kp on a finite covering of the full real window. Bernoulli scaling transports exact endpoint root certificates across each closed subinterval. The analytic cyclic upper bound yields Kp<=p/2. A separate endpoint certificate and Bernoulli scaling yield Ep(q)<cp, hence Ep(q)<Kp. The imported lower-bound chunks, upper bound and envelope comparison together prove all three original scalar-window conclusions, with no added assumptions.'))

for records in [payloads,missions]:
    for item in records:
        data=(ROOT/item['solution_file']).read_bytes();assert b'sorry' not in data
        item['solution_sha256']=hashlib.sha256(data).hexdigest()
(OUT/'payloads.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
(OUT/'mission-proofs.json').write_text(json.dumps(missions,indent=2)+'\n',encoding='utf-8')
(ROOT/'formalization/Theorems.lean').write_text('\n'.join('import '+w for w in dict.fromkeys(wrappers))+'\n',encoding='utf-8')
print('Prepared',len(payloads),'auxiliary proof files and two original milestone proofs.')
