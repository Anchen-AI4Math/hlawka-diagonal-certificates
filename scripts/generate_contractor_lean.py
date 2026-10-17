"""Emit kernel-checked contraction schedules from the original rational data.

Decimal is used only to propose root witnesses. Exact Fraction inequalities
screen each witness, and Lean checks the final integer-power inequalities.
"""
import argparse,json
from decimal import Decimal,localcontext,ROUND_FLOOR
from fractions import Fraction as F
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def rat(x):
    x=F(x)
    return f'({x.numerator} : ℝ)' if x.denominator==1 else f'({x.numerator}/{x.denominator} : ℝ)'

def witness(x,b):
    x,b=F(x),F(b)
    with localcontext() as ctx:
        ctx.prec=90
        y=(Decimal(x.numerator)/Decimal(x.denominator))**(Decimal(b.numerator)/Decimal(b.denominator))
        for digits in [14,18,24,32]:
            scale=10**digits
            w=F(int((y*scale).to_integral_value(rounding=ROUND_FLOOR)),scale)
            if w**b.denominator<=x**b.numerator:return w
    raise ValueError('Cannot find a lower root witness')

def generate(cutoff,index,slab,profile):
    a,b,tlo,thib,D,delta,h,q=map(F,(slab[k] for k in ['a','b','tlo','thib','D','delta','h','q']))
    A=3*q
    n0=F(profile['coarse_box']['off_min'])
    final=slab['final'];n,U,Af=map(F,(final[k] for k in ['n','U','Af']))
    box=final['box'];ell,u,v,w=map(F,(box[k] for k in ['diag_min','diag_max','off_min','off_max']))
    name=f'contract{cutoff}_slab{index:03d}'
    lines=['import Hlawka21.ContractionRounds','',
        '/- Generated from the original ten-round rational contractor schedule.',
        f'   cutoff{cutoff}/contractor.json, slab {index}, paper Section 4.',
        '   Every integer-power comparison below is checked by Lean. -/',
        'set_option autoImplicit false','set_option maxHeartbeats 200000000',
        'set_option exponentiation.threshold 2048','',
        'namespace HlawkaSchatten.DiagonalCutoff21','',
        f'theorem {name} (p : ℝ) (hpa : {rat(a)} ≤ p) (hpb : p ≤ {rat(b)})',
        '    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)',
        f'    (F : Facts p (cp p) {rat(D)} {rat(delta)} {rat(h)} {rat(A)} {rat(2*thib)} {rat(tlo)} X N)',
        f'    (hn0 : ∀ i, {rat(n0)} ≤ N i) :',
        f'    (∀ i, N i ≤ {rat(U)}) ∧',
        f'    (∀ j i, if j = i then -{rat(u)} ≤ X j i ∧ X j i ≤ -{rat(ell)}',
        f'      else {rat(v)} ≤ X j i ∧ X j i ≤ {rat(w)}) := by',
        '  have hp0 : 0 ≤ p := by linarith',
        f'  have hD0 : (0 : ℝ) ≤ {rat(D)} := by norm_num',
        f'  have hd0 : (0 : ℝ) ≤ {rat(delta)} := by norm_num']
    pcs={}
    def power(x,y):
        x,y=F(x),F(y)
        key=(x,y)
        if key in pcs:return pcs[key]
        assert 0<=x<=1 and 0<=y<=1
        Xw,Yw=witness(x,b),witness(y,b)
        assert Xw+Yw>1,(cutoff,index,x,y,Xw+Yw)
        label=f'pc{len(pcs)}';pcs[key]=label
        lines.extend([f'  have {label} : 1 < {rat(x)} ^ p + {rat(y)} ^ p := by',
            f'    exact cert_lt (x := {rat(x)}) (y := {rat(y)}) (X := {rat(Xw)}) (Y := {rat(Yw)}) {b.numerator} {b.denominator}',
            '      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            '      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)'])
        return label
    def pc_arg(label,strict=True):
        return f'(by norm_num; exact {label}{"" if strict else ".le"})'
    def ratio(r,hn,label):
        nr,s,tau,sigma=map(F,(r[k] for k in ['n','s','tau','sigma']))
        lp,up=power(tau,s-tau),power(sigma,s-sigma)
        lines.extend([f'  have {label} := ratio_round F {hn} (by norm_num) hD0',
            f'    (s := {rat(s)}) (τ := {rat(tau)}) (σ := {rat(sigma)})',
            '    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            f'    {pc_arg(lp)} {pc_arg(up)}'])
        return tau,sigma
    current=n0;hn='hn0'
    for ri,r in enumerate(slab['rounds']):
        assert F(r['n'])==current
        tau,_=ratio(r,hn,f'R{ri}')
        nn,Ab=map(F,(r[k] for k in ['next_n','Ab']))
        pc=power(Ab/nn,1-delta/nn)
        lines.extend([f'  have L{ri} := lower_round F {hn} (by norm_num) hd0',
            f'    (τ := {rat(tau)}) (n\' := {rat(nn)}) (Ab := {rat(Ab)}) (by norm_num)',
            f'    (fun i j k a b c ↦ (R{ri} i j k a b c).1) (by norm_num) (by norm_num)',
            f'    {pc_arg(pc,False)} (by norm_num)'])
        current=nn;hn=f'L{ri}'
    assert current==n
    tau,sigma=ratio(final,hn,'Rf')
    B=F(final['B'])
    pcb=power(B/(3-U),1-delta/(3-U))
    pcf=power(Af/U,1-delta/U)
    lines.extend([f'  have V := upper_round F {hn} (by norm_num) hd0',
        f'    (σ := {rat(sigma)}) (U := {rat(U)}) (Ab := {rat(B)}) (by norm_num)',
        '    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)',
        f'    {pc_arg(pcb,False)} (by norm_num)',
        '  refine ⟨V, ?_⟩',
        f'  exact final_round F {hn} V (by norm_num) hd0',
        f'    (τ := {rat(tau)}) (σ := {rat(sigma)}) (Ab := {rat(Af)})',
        '    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)',
        f'    {pc_arg(pcf,False)} (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
        '', 'end HlawkaSchatten.DiagonalCutoff21','',
        f'#print axioms HlawkaSchatten.DiagonalCutoff21.{name}',''])
    out=ROOT/f'formalization/Hlawka21/Window{cutoff}'
    out.mkdir(exist_ok=True)
    path=out/f'Slab{index:03d}.lean'
    code='\n'.join(lines)
    assert 'sorry' not in code and 'axiom ' not in code
    path.write_text(code,encoding='utf-8')
    return path,len(pcs)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--cutoff',type=int,choices=[21,26],default=21)
    parser.add_argument('--start',type=int,default=0)
    parser.add_argument('--limit',type=int,default=1)
    args=parser.parse_args()
    profile=json.loads((ROOT/f'profiles/cutoff{args.cutoff}.json').read_text())
    slabs=json.loads((ROOT/f'certificates/cutoff{args.cutoff}/contractor.json').read_text())
    for index in range(args.start,min(len(slabs),args.start+args.limit)):
        path,count=generate(args.cutoff,index,slabs[index],profile)
        print(path.relative_to(ROOT),count,'power comparisons',flush=True)
