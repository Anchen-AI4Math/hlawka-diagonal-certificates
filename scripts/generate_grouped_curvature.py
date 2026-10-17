"""Assemble the grouped numeric certificates with the actual deficit Hessian."""
import hashlib,json
from fractions import Fraction as F
from generate_contractor_lean import ROOT,rat

def main():
    certificate=json.loads((ROOT/'certificates/lean-grouped-geometry.json').read_text(encoding='utf-8'))
    for file,digest in certificate['inputs'].items():
        assert hashlib.sha256((ROOT/file).read_bytes()).hexdigest()==digest
    for index,g in enumerate(certificate['groups']):
        assert hashlib.sha256((ROOT/g['lean_source']).read_bytes()).hexdigest()==g['lean_sha256']
        a,b,c,U,A,J,W=map(F,(g[k] for k in ['a','b','c','U','A','J','W']))
        geom=g['geometry'];m,M,L,s,t,eta=map(F,(geom[k] for k in ['m','M','large','vmin','vmax','tail']))
        rt,rc=map(F,(geom[k] for k in ['rT_base','rC_base']))
        CT=F(geom['gT'])*F(geom['rT_factor'])/2
        CC=F(geom['gC'])*F(geom['rC_factor'])/2
        ell,u,v,w=map(F,(g['box'][k] for k in ['diag_min','diag_max','off_min','off_max']))
        e1,e2=map(F,(g[k] for k in ['epsilon1','epsilon2']))
        GT=f'pairTotalFactor {rat(m)} {rat(M)} {rat(s)} {rat(t)} {rat(e1)} {rat(e2)}'
        GC=f'pairColumnFactor {rat(m)} {rat(M)} {rat(s)} {rat(t)} {rat(eta)} {rat(L)} {rat(e1)} {rat(e2)}'
        name=f'grouped_deficit_hessian{index:02d}'
        lines=['import Hlawka21.CurvatureComparison',f'import Hlawka21.GroupedGeometry.Group{index:02d}','',
            '/- The actual original deficit Hessian is nonnegative on this',
            '   norm-capped convex domain for every real p in the group. -/',
            'set_option autoImplicit false','set_option maxHeartbeats 200000000','',
            'namespace HlawkaSchatten.DiagonalCutoff21','open HlawkaSchatten.DiagonalConstruction','',
            f'theorem {name} (p K : ℝ) (hpa : {rat(a)} ≤ p) (hpb : p ≤ {rat(b)})',
            f'    (hKlo : {rat(c)}*p ≤ K) (hKhi : K ≤ p/2) :',
            f'    ∀ X : Triple, X ∈ normCappedDomain p {rat(ell)} {rat(u)} {rat(v)} {rat(w)}',
            f'      {rat(U)} {rat(A)} {rat(J)} {rat(W)} →',
            '    ∀ Z : Triple, 0 ≤ deficitHessian p K X Z := by',
            f'  let GT : ℝ := {GT}',f'  let GC : ℝ := {GC}',
            f'  have hmarg := grouped_curvature_numeric{index:02d} p hpa hpb',
            f'  have hNT : (p/2) * GT * ({rat(A)}/{rat(L)}) *',
            f'      (({rat(eta)}*{rat(A)})/({rat(L)}*{rat(s)})) ^ (p-2) ≤ 1 := by',
            f'    have hbase : (({rat(eta)}*{rat(A)})/({rat(L)}*{rat(s)})) = {rat(rt)} := by norm_num',
            f'    have hconst : GT * ({rat(A)}/{rat(L)}) / 2 = {rat(CT)} := by',
            '      norm_num [GT, pairTotalFactor, shapeFactor]',
            f'    have hprod : (p/2) * GT * ({rat(A)}/{rat(L)}) = p * {rat(CT)} := by',
            '      calc _ = p * (GT * ('+rat(A)+'/'+rat(L)+') / 2) := by ring',
            '           _ = _ := by rw [hconst]',
            '    rw [hbase, hprod]','    exact hmarg.1.le',
            f'  have hNC : (GC/2) * ({rat(U)}/{rat(L)}) *',
            f'      (({rat(eta)}*{rat(U)})/({rat(L)}*{rat(m)})) ^ (p-2) ≤ 2*{rat(c)}-1/p := by',
            f'    have hbase : (({rat(eta)}*{rat(U)})/({rat(L)}*{rat(m)})) = {rat(rc)} := by norm_num',
            f'    have hconst : (GC/2) * ({rat(U)}/{rat(L)}) = {rat(CC)} := by',
            '      norm_num [GC, pairColumnFactor, shapeFactor]',
            '    rw [hbase, hconst]','    exact hmarg.2.le',
            f'  have hcoef := curvature_coefficients_from_ratios (p := p) (K := K) (c := {rat(c)})',
            f'    (m := {rat(m)}) (s := {rat(s)}) (U := {rat(U)}) (A := {rat(A)})',
            f'    (eta := {rat(eta)}) (L := {rat(L)}) (gT := GT) (gC := GC)',
            '    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            '    (by norm_num) (by norm_num)',
            '    (by norm_num [GT, pairTotalFactor, shapeFactor])',
            '    (by norm_num [GC, pairColumnFactor, shapeFactor])',
            '    hKlo hKhi hNT hNC',
            '  intro X hX Z',
            f'  exact deficit_hessian_domain_nonneg (m := {rat(m)}) (M := {rat(M)})',
            f'    (L := {rat(L)}) (s := {rat(s)}) (t := {rat(t)}) (eta := {rat(eta)})',
            f'    (eps1 := {rat(e1)}) (eps2 := {rat(e2)})',
            '    (by linarith) (by nlinarith [hKlo]) (by norm_num) (by norm_num)',
            '    (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            '    (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            '    (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            '    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
            '    hcoef.1 hcoef.2 X hX Z','',
            'end HlawkaSchatten.DiagonalCutoff21','',
            f'#print axioms HlawkaSchatten.DiagonalCutoff21.{name}','']
        path=ROOT/f'formalization/Hlawka21/GroupedCurvature/Group{index:02d}.lean'
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
        print(path.relative_to(ROOT),flush=True)

if __name__=='__main__':main()
