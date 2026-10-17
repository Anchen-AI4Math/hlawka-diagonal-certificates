"""Factor shared convexity/averaging out of finite certificate submissions."""
import hashlib
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat
from prepare_real_chunk_platform_proofs import bundle, HELPER


def main():
    groups=json.loads((ROOT/'certificates/lean-grouped-geometry.json').read_text(encoding='utf-8'))['groups']
    payloads=[]
    for i,g in enumerate(groups):
        a,b,U,A,J,W=[rat(F(g[k])) for k in ['a','b','U','A','J','W']]
        ell,u,v,w=[rat(F(g['box'][k])) for k in ['diag_min','diag_max','off_min','off_max']]
        key=f'domain_nonneg_group{i:02d}'
        name='HlawkaSchatten.DiagonalCutoff21.'+key
        statement=f'''theorem {name} :
    ∀ p : ℝ, {a} ≤ p → p ≤ {b} → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ j, -{u} ≤ X j j ∧ X j j ≤ -{ell}) →
      (∀ j i, j ≠ i → {v} ≤ X j i ∧ X j i ≤ {w}) →
      (∀ j, lpNorm p (X j) ≤ {U}) →
      lpNorm p (X 0 + X 1 + X 2) ≤ {A} →
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → {J} ≤ X j i + X k i) →
      {W} ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry'''
        def proof(ns):
            return f''' := by
  intro p hp hpmax X hd ho hN hT hJ hW
  have hB : {ns}.coordinateBox {ell} {u} {v} {w} X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [{ns}.coordinateBox] using hd i
    · simpa [{ns}.coordinateBox, hji] using ho j i hji
  exact {ns}.grouped_deficit_nonneg{i:02d} p hp hpmax X ⟨hB,hN,hT,hJ,hW⟩
'''
        preamble,code=bundle(f'Hlawka21.GroupedNonneg.Group{i:02d}')
        minimal='\n'.join(line for line in preamble.splitlines() if line.startswith('import Definitions.') or line.startswith('open '))+'\n'
        path=ROOT/f'formalization/platform/Sol_{key}.lean'
        source=code+statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',proof(HELPER))+'\n#print axioms solution\n'
        path.write_text(source,encoding='utf-8',newline='\n')
        local=ROOT/f'formalization/Hlawka21/GroupApi/Group{i:02d}.lean'
        local.parent.mkdir(parents=True,exist_ok=True)
        local.write_text(f'import Hlawka21.GroupedNonneg.Group{i:02d}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n\n'+statement.replace(' := by sorry',proof('HlawkaSchatten.DiagonalCutoff21'))+f'\n#print axioms {name}\n',encoding='utf-8',newline='\n')
        (ROOT/'formalization/Theorems'/('Thm_'+name.replace('.','_')+'.lean')).write_text(f'import Hlawka21.GroupApi.Group{i:02d}\n',encoding='utf-8')
        payloads.append(dict(key=key,theorem_name=name,theorem_title=f'Cyclic deficit nonnegative on norm-capped group {i}',
            formal_statement=statement,preamble=minimal,
            natural_language_statement=f'For every real p in [{g["a"]},{g["b"]}], a real three-coordinate triple satisfying the displayed diagonal and off-diagonal coordinate intervals, actual singleton norm caps, actual total norm cap, linear complementary-pair coordinate floors and linear off-diagonal-sum floor has nonnegative original Hlawka deficit for the unchanged cyclic constant. No equality of singleton norms is assumed. Pointwise seven-norm Hessian estimates imply convexity on this invariant domain, and permutation averaging reduces the assertion to the defining cyclic supremum.',
            source='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 5-7, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic norm/averaging framework by Ezzeri Esa, Apache-2.0; original notices retained.',
            tags=['hlawka-schatten','convexity','real-analysis'],solution_file=path.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            explanation='All generic norm-Hessian, coefficient, radial-spread, six-pair matrix, domain convexity, line derivative and permutation averaging proofs are embedded. Exact rational grouped geometry and real-exponent numeric margins prove Hessian nonnegativity. The two already Proved original scalar milestones fix the actual cyclicConstant coefficient. This extracts the shared analytic theorem, so finite contraction certificates can import it without recompiling the full analytic argument.'))
        print(key,len(source.encode('utf-8')),'bytes',flush=True)
    (ROOT/'formalization/platform/group-domain-proofs.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
