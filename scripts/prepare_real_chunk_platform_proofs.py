"""Export sixteen self-contained proofs with only the two proved scalar imports.

Public statements use explicit coordinate bounds, not private helper predicates.
Local theorem mirrors import the actual modular proofs instead of sorry stubs.
"""
import hashlib
import json
from pathlib import Path
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat

HELPER = 'HlawkaSchatten.DiagonalRealBundle'
OUT = ROOT/'formalization/platform'


def bundle(module):
    seen, imports, bodies = set(), [], []

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        code = (ROOT/'formalization'/(name.replace('.','/')+'.lean')).read_text(encoding='utf-8')
        for line in code.splitlines():
            if not line.startswith('import '):
                continue
            dependency = line[len('import '):]
            if dependency.startswith('Hlawka21.'):
                visit(dependency)
            elif line not in imports:
                imports.append(line)
        body = '\n'.join(line for line in code.splitlines() if not line.startswith(('import ','#print axioms ')))
        bodies.append(body.replace('HlawkaSchatten.DiagonalCutoff21',HELPER))
    visit(module)
    preamble = '\n'.join(imports)+'\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n'
    return preamble, preamble+'open HlawkaSchatten.DiagonalCutoff21\n\n'+'\n\n'.join(bodies)+'\n'


def main():
    chunks = json.loads((ROOT/'formalization/real-chunks.json').read_text())
    payloads = []
    for row in chunks:
        cutoff = row['cutoff']
        profile = json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
        box = profile['coarse_box']
        c, A = rat(F(profile['c'])), rat(3*F(profile['q']))
        chunk = row['start']//16
        key = f'certified_nonneg{cutoff}_chunk{chunk:02d}'
        name = 'HlawkaSchatten.DiagonalCutoff21.'+key
        statement = f'''theorem {name} :
    ∀ p : ℝ, {rat(F(row['a']))} ≤ p → p ≤ {rat(F(row['b']))} →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -({box['diag_max']} : ℝ) ≤ X i i ∧ X i i ≤ -({box['diag_min']} : ℝ)) →
      (∀ j i, j ≠ i → ({box['off_min']} : ℝ) ≤ X j i ∧ X j i ≤ ({box['off_max']} : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < {A} →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ({c}*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry'''
        def proof(namespace):
            return f''' := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : {namespace}.coordinateBox ({box['diag_min']} : ℝ) ({box['diag_max']} : ℝ)
      ({box['off_min']} : ℝ) ({box['off_max']} : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [{namespace}.coordinateBox] using hd i
    · simpa [{namespace}.coordinateBox, hji] using ho j i hji
  exact {namespace}.{row['theorem']} p hp hpmax X hB hS hT hG
'''
        preamble, code = bundle(row['module'])
        solution = code+statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',proof(HELPER))+'\n#print axioms solution\n'
        assert 'sorry' not in solution
        file = OUT/f'Sol_{key}.lean'
        file.write_text(solution,encoding='utf-8',newline='\n')
        wrapper = ROOT/'formalization/Theorems'/('Thm_'+name.replace('.','_')+'.lean')
        mirror = f'import {row["module"]}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n\n'+statement.replace(' := by sorry',proof('HlawkaSchatten.DiagonalCutoff21'))+f'\n#print axioms {name}\n'
        wrapper.write_text(mirror,encoding='utf-8',newline='\n')
        payloads.append(dict(key=key,theorem_name=name,
            theorem_title=f'Actual-norm localized nonnegativity [{row["a"]},{row["b"]}]',
            formal_statement=statement,preamble=preamble,
            natural_language_statement=f'For every real p in [{row["a"]},{row["b"]}], any real three-by-three triple in the stated coarse coordinate box, whose singleton norms sum to three, total norm is below {3*F(profile["q"])}, and original pair-gap sum is below 2/(({profile["c"]})p), has nonnegative original Hlawka deficit for the unchanged cyclic constant. Unequal singleton norms are allowed. The proof internally checks sixteen complete contraction schedules, all root and budget premises, the actual norm-Hessian estimates, convexity and simultaneous permutation averaging. This is the localization-to-nonnegativity step, not the original unrestricted real-three theorem.',
            source='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 4-7, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic norm and averaging proofs by Ezzeri Esa; contraction framework adapted from @bwdaugherty; Apache-2.0 notices retained.',
            tags=['hlawka-schatten','real-analysis','convexity'],
            solution_file=file.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(file.read_bytes()).hexdigest(),
            explanation='The two original scalar milestones are the only theorem imports. The complete helper proofs, sixteen actual-norm localization slabs and their ten-round contraction schedules are embedded. Exact rational comparisons put each contracted configuration in one of two norm-capped convex domains. The actual seven norm Hessians obey the proved coefficient comparisons. Along-line derivatives and continuity yield convexity; simultaneous row-and-coordinate permutation averaging preserves the domain and does not increase the deficit. Linear offsum and total-norm bounds force the averaged cyclic parameter into [1/2,2], where the defining supremum gives nonnegativity. A finite balanced interval split covers every real exponent in this chunk.'))
        print(key,len(solution.encode('utf-8')),'bytes',flush=True)
    (OUT/'real-chunk-proofs.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')


if __name__ == '__main__':
    main()
