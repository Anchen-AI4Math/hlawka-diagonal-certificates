"""Export arbitrary-counterexample localization for the two original windows.

The original proved scalar milestone is the sole theorem import. All norm,
normalization, weighted convexity, orientation and LP helper proofs are
included with their source notices. A separate helper namespace avoids
clashing with the actual proofs used by local platform-name mirrors.
"""
import hashlib,json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'formalization/platform'
HELPER='HlawkaSchatten.DiagonalFailureBundle'

def bundle(cutoff):
    names=['Foundation/Basic','Foundation/Normalization','Foundation/WeightedConvex',
        'Foundation/ScalarConvexity','Foundation/ScalarBounds','Foundation/ScalarEnvelope',
        'Foundation/Failure','ContractionCore','NormBasic','NormGeometry','Tail',
        f'Coarse{cutoff}',f'CoarseConnection{cutoff}','Orientation',f'CoarseFailure{cutoff}']
    imports=[];bodies=[]
    for name in names:
        code=(ROOT/f'formalization/Hlawka21/{name}.lean').read_text(encoding='utf-8')
        for line in code.splitlines():
            if line.startswith(('import Mathlib.','import Definitions.')) and line not in imports:imports.append(line)
        body='\n'.join(line for line in code.splitlines() if not line.startswith(('import ','#print axioms ')))
        bodies.append(body.replace('HlawkaSchatten.DiagonalCutoff21',HELPER))
    imports.append(f'import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window{cutoff}')
    preamble='\n'.join(imports)+'\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n'
    extra=f'''namespace {HELPER}
def coordinateBox (ell u v w : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w
end {HELPER}
'''
    return preamble,preamble+'\n'+extra+'\n'+'\n'.join(bodies)+'\n'

def main():
    payloads=[]
    for cutoff in [21,26]:
        profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text(encoding='utf-8'))
        upper=26 if cutoff==21 else 32
        c,q=profile['c'],profile['q'];b=profile['coarse_box']
        name=f'HlawkaSchatten.DiagonalCutoff21.coarse_failure_window{cutoff}'
        statement=f'''theorem {name} :
    ∀ p : ℝ, {cutoff} ≤ p → p ≤ {upper} →
    ∀ x y z : Fin 3 → ℝ, hlawkaDeficit p (cyclicConstant p) x y z < 0 →
    ∃ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -({b['diag_max']} : ℝ) ≤ X i i ∧ X i i ≤ -({b['diag_min']} : ℝ)) ∧
      (∀ j i, j ≠ i → ({b['off_min']} : ℝ) ≤ X j i ∧ X j i ≤ ({b['off_max']} : ℝ)) ∧
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
      lpNorm p (X 0 + X 1 + X 2) < 3 * ({q} : ℝ) ∧
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / (({c} : ℝ) * p) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by sorry'''
        proof=f''' := by
  intro p hp hpmax x y z hf
  have hs := HlawkaSchatten.DiagonalCutoff21.scalar_window{cutoff} p hp hpmax
  obtain ⟨X, hbox, hS, hT, hG, hfail⟩ := {HELPER}.coarse_failure{cutoff}
    hp hs.1 (by norm_num) (by norm_num) hs.2.2 x y z hf
  refine ⟨X, ?_, ?_, hS, hT, hG, hfail⟩
  · intro i
    simpa [{HELPER}.coordinateBox] using hbox i i
  · intro j i hji
    simpa [{HELPER}.coordinateBox, hji] using hbox j i
'''
        preamble,solution=bundle(cutoff)
        solution+=statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',proof)
        solution+='\n#print axioms solution\n'
        file=f'Sol_coarse_failure_window{cutoff}.lean'
        path=OUT/file;path.write_text(solution,encoding='utf-8',newline='\n')
        assert 'sorry' not in solution
        payloads.append(dict(key=f'coarse_failure_window{cutoff}',theorem_name=name,
            theorem_title=f'Every real-three failure on [{cutoff},{upper}] localizes to the coarse box',
            formal_statement=statement,preamble=preamble,
            natural_language_statement=rf'''For every real $p\in[{cutoff},{upper}]$, suppose arbitrary vectors $x,y,z\in\mathbb R^3$ strictly violate the Hlawka inequality with the unchanged cyclic constant $K_p$.

Then another strictly violating triple $X=(X_0,X_1,X_2)$ exists with singleton norms summing to $3$, total norm less than $3({q})$, pair-gap sum less than $2/(({c})p)$, diagonal entries in $[-{b['diag_max']},-{b['diag_min']}]$, and off-diagonal entries in $[{b['off_min']},{b['off_max']}]$.

The input vectors are unrestricted: no equal-norm, nonzero, sign, coordinate, normalization or localization premise is imposed. Reflection, rescaling and simultaneous signed coordinate permutation are conclusions of the proof. This is a counterexample reduction, not an assertion that the final real-three Hlawka inequality is already proved.''',
            source='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Section 3, equations (10)-(11), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic normalization by Ezzeri Esa and cutoff-32 orientation by @bwdaugherty, Apache-2.0, adapted with the new constants.',
            tags=['hlawka-schatten','localization','real-analysis'],solution_file='formalization/platform/'+file,
            solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            explanation='Use the already proved original scalar-window milestone. The total-largest reflection preserves strict failure for K>=1; positive rescaling makes singleton norms sum to three. Weighted scalar convexity and the antitone scalar envelope confine the total norm below 3q. The maximum coordinate estimate with log(3)<1.099 supplies signed pair coordinates within the prescribed loss. A parameterized signed-conflict lemma proves the three coordinates are distinct. A simultaneous signed permutation orients them, preserving all seven original norms and the deficit. The two exact rational LP stages, with the actual p-norm half-tail estimate between them, imply the displayed coarse box. Every helper is proved in the submitted file with original attribution; only the already Proved original scalar milestone is imported.'))
    (OUT/'failure-proofs.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print('Prepared two complete arbitrary-failure localization proofs.')

if __name__=='__main__':main()
