"""Export the generic complex leastness bridge with actual local mirrors."""
import hashlib
import json
from generate_contractor_lean import ROOT

HELPER='HlawkaSchatten.DiagonalComplexBundle'
DC='HlawkaSchatten.DiagonalConstruction'


def main():
    imports=['import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three']
    bodies=[]
    for name in ['Basic','Cyclic','CyclicWitness','CircleProjection','ComplexTransfer']:
        code=(ROOT/f'formalization/Hlawka21/Foundation/{name}.lean').read_text(encoding='utf-8')
        for line in code.splitlines():
            if line.startswith(('import Mathlib.','import Definitions.')) and line not in imports:
                imports.append(line)
        body='\n'.join(line for line in code.splitlines() if not line.startswith(('import ','#print axioms ')))
        body=body.replace('namespace '+DC,'namespace '+HELPER).replace('end '+DC,'end '+HELPER)
        body=body.replace('unfold lpNorm','unfold _root_.'+DC+'.lpNorm')
        bodies.append(body)
    preamble='\n'.join(imports)+'\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n'
    name='HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three'
    statement=f'''theorem {name} :
    ∀ p : ℝ, 1 < p →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) →
      IsLeast {{C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}} (cyclicConstant p) := by sorry'''
    proof=f''' := by
  intro p hp hreal
  exact {HELPER}.isLeast_of_real_three_bound hp hreal
'''
    code=preamble+'\n'+'\n\n'.join(bodies)+'\n'+statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',proof)+'\n#print axioms solution\n'
    assert 'sorry' not in code
    path=ROOT/'formalization/platform/Sol_complex_least_of_real_three.lean'
    path.write_text(code,encoding='utf-8',newline='\n')
    payload=dict(key='complex_least_of_real_three',theorem_name=name,
                 theorem_title='A real three-coordinate bound gives the uniform least complex constant',
                 formal_statement=statement,preamble=preamble,
                 natural_language_statement='For every real p>1, if the unchanged cyclic constant satisfies the original Hlawka inequality for all real three-coordinate triples, it is the least constant valid in every finite complex coordinate dimension, including dimension zero. Finite nonnegative mixtures of real circle projections preserve all seven norm powers up to a common positive circle moment; continuity passes the bound to the circle integral. The existing three-coordinate cyclic obstruction gives leastness. No equal-norm or nonzero-vector premise is used.',
                 source='Ezzeri Esa, Hlawka-Schatten construction (Apache-2.0), and @bwdaugherty, accepted cutoff32 submission 2d248eb1-4938-4dee-8392-df24d2c70f2f, https://prove2.me/theorems/6e8430ce-7c32-4b82-9a1b-d7fcd67fdeb3 . Generic transfer isolated and rebuilt for the cutoff21 proof by Yuxuan Xu. Original notices retained.',
                 tags=['hlawka-schatten','complex-analysis','sharp-constant'],
                 solution_file=path.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                 explanation='The sole theorem import is the already Proved arbitrary-dimensional real reduction real_bound_of_fin_three. All other needed norm laws, positivity and compactness of the cyclic supremum, cyclic lower obstruction, Haar-circle projection identities, finite projection norm formula, convex-hull/closure argument, and the positive common moment cancellation are fully proved in the file under a separate helper namespace. The conclusion quantifies over every natural dimension, including zero, and proves IsLeast, not only admissibility.')
    (ROOT/'formalization/platform/transfer-proofs.json').write_text(json.dumps([payload],indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    (ROOT/'formalization/Theorems/Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three.lean').write_text('import Hlawka21.Foundation.DimensionReduction\n',encoding='utf-8')
    (ROOT/'formalization/Theorems/Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three.lean').write_text('import Hlawka21.ComplexBridge\n',encoding='utf-8')
    print('Prepared generic transfer:',len(code.encode('utf-8')),'bytes')


if __name__=='__main__':
    main()
