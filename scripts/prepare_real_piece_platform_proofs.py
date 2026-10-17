"""Export small finite certificates importing the proved analytic groups."""
import hashlib
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat
from prepare_real_chunk_platform_proofs import bundle, HELPER


def main():
    rows=json.loads((ROOT/'formalization/real-pieces.json').read_text())
    payloads=[]
    for row in rows:
        cutoff,index=row['cutoff'],row['index']
        profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
        b=profile['coarse_box'];A=rat(3*F(profile['q']));c=rat(F(profile['c']))
        key=f'certified_piece{cutoff}_{index:02d}'
        name='HlawkaSchatten.DiagonalCutoff21.'+key
        statement=f'''theorem {name} :
    ∀ p : ℝ, {rat(F(row['a']))} ≤ p → p ≤ {rat(F(row['b']))} →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -({b['diag_max']} : ℝ) ≤ X i i ∧ X i i ≤ -({b['diag_min']} : ℝ)) →
      (∀ j i, j ≠ i → ({b['off_min']} : ℝ) ≤ X j i ∧ X j i ≤ ({b['off_max']} : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < {A} →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ({c}*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry'''
        def proof(ns):
            return f''' := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : {ns}.coordinateBox ({b['diag_min']} : ℝ) ({b['diag_max']} : ℝ)
      ({b['off_min']} : ℝ) ({b['off_max']} : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [{ns}.coordinateBox] using hd i
    · simpa [{ns}.coordinateBox, hji] using ho j i hji
  exact {ns}.{row['theorem']} p hp hpmax X hB hS hT hG
'''
        preamble,body=bundle(row['module'])
        minimal='\n'.join(line for line in preamble.splitlines() if line.startswith(('import Definitions.','import Theorems.','open ')))+'\n'
        source=body+statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',proof(HELPER))+'\n#print axioms solution\n'
        assert 'sorry' not in source
        path=ROOT/f'formalization/platform/Sol_{key}.lean'
        path.write_text(source,encoding='utf-8',newline='\n')
        mirror=f'import {row["module"]}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n\n'+statement.replace(' := by sorry',proof('HlawkaSchatten.DiagonalCutoff21'))+f'\n#print axioms {name}\n'
        (ROOT/'formalization/Theorems'/('Thm_'+name.replace('.','_')+'.lean')).write_text(mirror,encoding='utf-8',newline='\n')
        payloads.append(dict(key=key,theorem_name=name,theorem_title=f'Finite contraction certificate [{row["a"]},{row["b"]}]',
            formal_statement=statement,preamble=minimal,
            natural_language_statement=f'For all real p in [{row["a"]},{row["b"]}], an original real triple satisfying the explicit coarse coordinate box, singleton norm sum three, total norm bound {3*F(profile["q"])}, and original pair-gap bound has nonnegative original cyclic-constant deficit. This piece covers {len(row["indices"])} consecutive parameter slabs. Root bounds, budgets, all ten contraction rounds and the linear pair/offsum floors are proved here; the shared norm-domain nonnegativity theorem is imported. Unequal singleton norms are allowed.',
            source='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-7, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Contraction framework adapted from @bwdaugherty, Apache-2.0; source notices retained.',
            tags=['hlawka-schatten','exact-arithmetic','real-analysis'],solution_file=path.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            explanation='The only theorem import is the appropriate shared analytic domain-nonnegativity result. The exact root comparisons, actual original p-norm-to-contraction bridge and complete ten-round contraction schedules for at most eight slabs are embedded. Explicit rational box inclusions and norm/pair/offsum bounds imply every displayed hypothesis of the imported analytic theorem. Balanced interval decisions cover the entire real exponent interval with no floating-point or external validity predicate. This factoring avoids repeating the shared Hessian and averaging proof in every certificate file.'))
        print(key,len(source.encode('utf-8')),'bytes',flush=True)
    (ROOT/'formalization/platform/real-piece-proofs.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
