"""Find exact uniform geometry groups and emit their real-exponent checks.

All decisions use Fraction arithmetic. These prove the numeric inequalities
only; the geometric/Hessian connection remains a separate Lean obligation.
"""
import hashlib,json
from fractions import Fraction as F
from pathlib import Path
from geometry import pair_cap_constants
from generate_contractor_lean import ROOT,rat

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def group_data(rows):
    box={k:str((min if k.endswith('min') else max)(F(f['box'][k]) for _,_,s,p,f in rows)) for k in rows[0][4]['box']}
    U=max(F(f['U']) for _,_,s,p,f in rows);A=max(3*F(s['q']) for _,_,s,p,f in rows)
    J=min(3-F(f['U'])-2/(F(p['c'])*F(s['a']))-F(p['coarse_tail']) for _,_,s,p,f in rows)
    W=min(6-F(s['h']) for _,_,s,p,f in rows)
    lo=F(rows[0][2]['a']);hi=F(rows[-1][2]['b']);n=lo.numerator//lo.denominator
    c=min(F(p['c']) for _,_,s,p,f in rows)
    try:g=pair_cap_constants(box,A,U,F(1),F(1,4),J,W)
    except ValueError:return None
    mt=1-hi/2*g['gT']*g['rT_factor']*g['rT_base']**(n-2)
    mc=2*c-F(1,n)-g['gC']/2*g['rC_factor']*g['rC_base']**(n-2)
    if not (mt>0 and mc>0 and 0<g['rT_base']<=1 and 0<g['rC_base']<=1):return None
    return dict(a=str(lo),b=str(hi),n=n,c=str(c),box=box,U=str(U),A=str(A),J=str(J),W=str(W),
        epsilon1='1',epsilon2='1/4',geometry={k:str(v) for k,v in g.items()},
        margins={'total':str(mt),'column':str(mc)},members=[dict(cutoff=r[0],index=r[1]) for r in rows])

def emit(index,g):
    a,b,c=map(F,(g[k] for k in ['a','b','c']));n=g['n'];power=n-2
    geom=g['geometry'];rt,rc=map(F,(geom[k] for k in ['rT_base','rC_base']))
    CT=F(geom['gT'])*F(geom['rT_factor'])/2
    CC=F(geom['gC'])*F(geom['rC_factor'])/2
    name=f'grouped_curvature_numeric{index:02d}'
    lines=['import Hlawka21.ContractionCore','',
        '/- Exact grouped numeric margins for all real p in this interval.',
        '   The geometric/Hessian implication is a separate proof obligation. -/',
        'set_option autoImplicit false','set_option maxHeartbeats 200000000','',
        'namespace HlawkaSchatten.DiagonalCutoff21','',
        f'theorem {name} (p : ℝ) (hpa : {rat(a)} ≤ p) (hpb : p ≤ {rat(b)}) :',
        f'    p * {rat(CT)} * {rat(rt)} ^ (p - 2) < 1 ∧',
        f'    {rat(CC)} * {rat(rc)} ^ (p - 2) < 2 * {rat(c)} - 1/p := by',
        f'  have hpn : {n} ≤ p := by linarith',
        '  have hp0 : 0 < p := by linarith',
        f'  have hrt : {rat(rt)} ^ (p - 2) ≤ {rat(rt)} ^ ({power} : ℕ) := by',
        f'    have hh := Real.rpow_le_rpow_of_exponent_ge\' (x := {rat(rt)})',
        f'      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ {power}) (by linarith : ({power} : ℝ) ≤ p - 2)',
        f'    calc _ ≤ {rat(rt)} ^ (({power} : ℕ) : ℝ) := hh',
        '         _ = _ := Real.rpow_natCast _ _',
        f'  have hrc : {rat(rc)} ^ (p - 2) ≤ {rat(rc)} ^ ({power} : ℕ) := by',
        f'    have hh := Real.rpow_le_rpow_of_exponent_ge\' (x := {rat(rc)})',
        f'      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ {power}) (by linarith : ({power} : ℝ) ≤ p - 2)',
        f'    calc _ ≤ {rat(rc)} ^ (({power} : ℕ) : ℝ) := hh',
        '         _ = _ := Real.rpow_natCast _ _',
        '  constructor',
        f'  · have h1 := mul_le_mul_of_nonneg_left hrt (show 0 ≤ p * {rat(CT)} by positivity)',
        f'    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ {rat(CT)} * {rat(rt)} ^ ({power} : ℕ) by norm_num)',
        f'    have hend : {rat(b)} * {rat(CT)} * {rat(rt)} ^ ({power} : ℕ) < 1 := by norm_num',
        '    nlinarith only [h1, h2, hend]',
        f'  · have h1 := mul_le_mul_of_nonneg_left hrc (show 0 ≤ {rat(CC)} by norm_num)',
        f'    have hinv : 1/p ≤ 1/({n} : ℝ) := one_div_le_one_div_of_le (by norm_num) hpn',
        f'    have hend : {rat(CC)} * {rat(rc)} ^ ({power} : ℕ) < 2 * {rat(c)} - 1/({n} : ℝ) := by norm_num',
        '    linarith only [h1, hinv, hend]','',
        'end HlawkaSchatten.DiagonalCutoff21','',
        f'#print axioms HlawkaSchatten.DiagonalCutoff21.{name}','']
    path=ROOT/f'formalization/Hlawka21/GroupedGeometry/Group{index:02d}.lean'
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    return path

def main():
    rows=[];inputs={}
    for cutoff in [21,26]:
        pp=ROOT/f'profiles/cutoff{cutoff}.json';sp=ROOT/f'certificates/cutoff{cutoff}/contractor.json'
        inputs[pp.relative_to(ROOT).as_posix()]=sha(pp);inputs[sp.relative_to(ROOT).as_posix()]=sha(sp)
        p=json.loads(pp.read_text(encoding='utf-8'));slabs=json.loads(sp.read_text(encoding='utf-8'))
        for index,s in enumerate(slabs):rows.append((cutoff,index,s,p,s['final']))
    cursor=F(21)
    for _,_,s,_,_ in rows:assert F(s['a'])==cursor<F(s['b']);cursor=F(s['b'])
    assert cursor==32 and len(rows)==256
    start=0;groups=[]
    while start<len(rows):
        best=group_data(rows[start:start+1]);assert best,(start,'single slab fails')
        stop=start+1
        while stop<len(rows):
            d=group_data(rows[start:stop+1])
            if d is None:break
            best=d;stop+=1
        groups.append(best);start=stop
    for index,g in enumerate(groups):
        path=emit(index,g);g.update(lean_source=path.relative_to(ROOT).as_posix(),lean_sha256=sha(path))
        print('Group',index,g['a'],g['b'],len(g['members']),'slabs; positive exact margins',flush=True)
    cert=dict(scope='Exact aggregate geometry and numeric margins only; full geometric Hessian and averaging proof still required.',inputs=inputs,groups=groups)
    (ROOT/'certificates/lean-grouped-geometry.json').write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8')

if __name__=='__main__':main()
