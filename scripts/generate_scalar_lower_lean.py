"""Fixed rational cyclic witnesses: three endpoint root certificates per slab.

Bernoulli transports these bounds across the full real slab. Candidates are
rounded with Decimal, then screened as exact Fractions and checked in Lean.
Sixteen slabs share one module to avoid repeated library-loading overhead.
"""
import argparse,json
from decimal import Decimal,localcontext,ROUND_CEILING
from fractions import Fraction as F
from pathlib import Path
from generate_contractor_lean import rat,ROOT

CHUNK=16
def dec(x):return Decimal(x.numerator)/Decimal(x.denominator)
def up(x):return F(int((x*10**10).to_integral_value(rounding=ROUND_CEILING)),10**10)

def data(cutoff,slab,profile):
    a,b=F(slab['a']),F(slab['b']);c=F(profile['c'])
    t=F(17,20) if cutoff==21 else F(87,100)
    with localcontext() as ctx:
        ctx.prec=90
        Z=up(dec(t)**dec(a))
        A=up((2+dec(Z))**(1/dec(a)))
        aa=up(Decimal(3)**(1/dec(a)))
    assert t**a.numerator<=Z**a.denominator
    assert (2+Z)**a.denominator<=A**a.numerator
    assert F(3)**a.denominator<=aa**a.numerator
    H=3*(A-1)-(2-t)*(aa-1)
    margin=3-(2-t)+a/b*H-6*c*a*(A-1)
    assert H>=0 and margin>0
    return dict(a=a,b=b,c=c,t=t,Z=Z,A=A,aa=aa,margin=margin)

def tree(lines,cutoff,records,ids,lo,hi,indent='  ',prefix='h'):
    if len(ids)==1:
        i=ids[0]
        lines.append(indent+f'exact lower{cutoff}_scalar{i:03d} p {lo} {hi}')
        return
    split=len(ids)//2
    mid=records[ids[split]]['a']
    hl,hr=prefix+'l',prefix+'r'
    lines.append(indent+f'rcases le_total p {rat(mid)} with {hl} | {hr}')
    lines.append(indent+'·')
    tree(lines,cutoff,records,ids[:split],lo,hl,indent+'  ',prefix+'a')
    lines.append(indent+'·')
    tree(lines,cutoff,records,ids[split:],hr,hi,indent+'  ',prefix+'b')

def generate(cutoff,chunk,slabs,profile,leaf_limit=None):
    records={i:data(cutoff,s,profile) for i,s in enumerate(slabs)}
    ids=list(range(chunk*CHUNK,min((chunk+1)*CHUNK,len(slabs))))
    if leaf_limit:ids=ids[:leaf_limit]
    assert ids
    lines=['import Hlawka21.FixedWitness','',
        '/- Fixed rational cyclic witnesses on the original real-exponent slabs.',
        '   Every endpoint root bound is reduced to a rational integer-power',
        '   inequality. The conclusion holds throughout each real interval. -/',
        'set_option autoImplicit false','set_option exponentiation.threshold 2048',
        'set_option maxHeartbeats 200000000','',
        'namespace HlawkaSchatten.DiagonalCutoff21',
        'open HlawkaSchatten.DiagonalConstruction','']
    for i in ids:
        d=records[i];a,b,c,t,Z,A,aa=[d[k] for k in ['a','b','c','t','Z','A','aa']]
        lines.extend([f'theorem lower{cutoff}_scalar{i:03d} (p : ℝ) (hpa : {rat(a)} ≤ p) (hpb : p ≤ {rat(b)}) :',
            f'    {rat(c)}*p < cyclicConstant p := by',
            f'  have ht : {rat(t)}^{rat(a)} ≤ {rat(Z)} := by',
            f'    have h := rpow_le_of_pow_le (x := {rat(t)}) (X := {rat(Z)}) (by norm_num) (by norm_num) {a.numerator} {a.denominator} (by norm_num) (by norm_num)',
            '    convert h using 1 <;> norm_num',
            f'  have hA : {rat(2+Z)} ≤ {rat(A)}^{rat(a)} := by',
            f'    have h := le_rpow_of_pow_le (x := {rat(A)}) (X := {rat(2+Z)}) (by norm_num) {a.numerator} {a.denominator} (by norm_num) (by norm_num)',
            '    convert h using 1 <;> norm_num',
            f'  have ha : (3 : ℝ) ≤ {rat(aa)}^{rat(a)} := by',
            f'    have h := le_rpow_of_pow_le (x := {rat(aa)}) (X := (3 : ℝ)) (by norm_num) {a.numerator} {a.denominator} (by norm_num) (by norm_num)',
            '    convert h using 1 <;> norm_num',
            f'  apply cyclicConstant_lower_endpoint (alpha := {rat(a)}) (beta := {rat(b)})',
            f'    (t := {rat(t)}) (Aup := {rat(A)}) (aup := {rat(aa)})',
            '    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)',
            '    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            '  · linarith only [ht, hA]',
            '  · exact ha',
            '  · norm_num',
            '  · norm_num',''])
    name=f'lower{cutoff}_chunk{chunk:02d}'
    a,b,c=records[ids[0]]['a'],records[ids[-1]]['b'],F(profile['c'])
    lines.extend([f'theorem {name} (p : ℝ) (hpa : {rat(a)} ≤ p) (hpb : p ≤ {rat(b)}) :',
        f'    {rat(c)}*p < cyclicConstant p := by'])
    tree(lines,cutoff,records,ids,'hpa','hpb')
    lines.extend(['','end HlawkaSchatten.DiagonalCutoff21','',
        f'#print axioms HlawkaSchatten.DiagonalCutoff21.{name}',''])
    path=ROOT/f'formalization/Hlawka21/Scalar{cutoff}/Chunk{chunk:02d}.lean'
    path.parent.mkdir(exist_ok=True)
    code='\n'.join(lines)
    assert 'sorry' not in code and 'axiom ' not in code
    path.write_text(code,encoding='utf-8')
    return path,[{k:str(v) for k,v in records[i].items()} for i in ids]

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--cutoff',type=int,choices=[21,26],default=21)
    parser.add_argument('--chunk',type=int,default=0);parser.add_argument('--leaf-limit',type=int)
    args=parser.parse_args()
    profile=json.loads((ROOT/f'profiles/cutoff{args.cutoff}.json').read_text())
    slabs=json.loads((ROOT/f'certificates/cutoff{args.cutoff}/contractor.json').read_text())
    path,records=generate(args.cutoff,args.chunk,slabs,profile,args.leaf_limit)
    print(path.relative_to(ROOT),len(records),'slabs, minimum exact margin',min(F(r['margin']) for r in records),flush=True)
