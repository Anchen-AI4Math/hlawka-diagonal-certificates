"""Extract generic proved lemmas from the attributed cutoff-32 reference.

The reference is preserved byte-for-byte. The new namespace is cutoff21;
no hardcoded cutoff-32 numerical statement is copied as a new-window result.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
source=(ROOT/'sources/contract32.lean').read_text(encoding='utf-8')
start=source.index('/-- Increments of')
end=source.index('/-! ## Monotonicity')
header='''import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/- Adapted from @bwdaugherty's accepted cutoff-32 contribution,
   submission d75400b0-5a0e-4167-8192-7fd299469c2e (2026-10-16),
   https://prove2.me/theorems/4e05427b-74d9-4e61-8d14-a52384a5ca10 .
   Public Prove2Me contribution under Apache-2.0; see sources/NOTICE.md.
   These generic lemmas do not assume p >= 32. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff21

'''
code=header+source[start:end]+'\nend HlawkaSchatten.DiagonalCutoff21\n'
assert 'sorry' not in code and 'axiom ' not in code
(ROOT/'formalization/Hlawka21/ContractionCore.lean').write_text(code,encoding='utf-8')
print('Extracted generic rpow, diagonal, Minkowski and ratio certificates.')

# Separate the algebraic rounds from the norm implementation. Later the bridge
# instantiates N i with the original lpNorm; no replacement norm is introduced.
import re
facts=source[source.index('structure Facts '):source.index('\ntheorem facts_of')]
facts=facts.replace('(X : Triple)', '(X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)')
facts=facts.replace('  hp :', '  Nnonneg : ∀ i, 0 ≤ N i\n  hp :',1)
facts=facts.replace('79/100 ≤ X i j','0 ≤ X i j')
rounds=source[source.index('section Rounds'):source.index('/-! ## The generic slab theorem')]
ratio_start=rounds.index('theorem ratio_round')
ratio_end=rounds.index('theorem lower_round')
rounds=rounds[:ratio_start]+re.sub(r'\bN\b','Ni',rounds[ratio_start:ratio_end])+rounds[ratio_end:]
rounds=rounds.replace('{X : Triple}', '{X : Fin 3 → Fin 3 → ℝ} {N : Fin 3 → ℝ}')
rounds=rounds.replace('Facts p c D δ h A cmax tlo X','Facts p c D δ h A cmax tlo X N')
rounds=rounds.replace('(lpNorm_nonneg3 p _) (lpNorm_nonneg3 p _)','(F.Nnonneg j) (F.Nnonneg k)')
rounds=rounds.replace('{n U τ σ Ab : ℝ}', '{n U τ σ Ab ell u v w : ℝ}')
rounds=rounds.replace('849/1000 ≤','v ≤').replace('≤ 1121/1000','≤ w').replace('≤ 1065/1000','≤ u').replace('625/1000 ≤','ell ≤')
rounds=rounds.replace(': finalBox X :=', ': (∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell\n      else v ≤ X j i ∧ X j i ≤ w) :=')
for i in ['i','j','k','l']:
    facts=facts.replace(f'lpNorm p (X {i})',f'N {i}')
    rounds=rounds.replace(f'lpNorm p (X {i})',f'N {i}')
assert 'lpNorm' not in facts+rounds
start=source.index('theorem others ')
end=source.index('\ntheorem offperm')
combinatorics=source[start:end]
header2='''import Hlawka21.ContractionCore
import Mathlib.Tactic.FinCases

/- The contraction rounds of @bwdaugherty's cutoff-32 proof, generalized
   to arbitrary nonnegative singleton sizes and rational output boxes.
   Source: submission d75400b0-5a0e-4167-8192-7fd299469c2e, Apache-2.0.
   Paper Section 4: diagonal/ratio bounds, lower update, upper update,
   and final box. N will be instantiated with the original lpNorm. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff21

'''
code=header2+combinatorics+'\n'+facts+'\n'+rounds+'\nend HlawkaSchatten.DiagonalCutoff21\n'
code+='\n#print axioms HlawkaSchatten.DiagonalCutoff21.final_round\n'
assert 'sorry' not in code
(ROOT/'formalization/Hlawka21/ContractionRounds.lean').write_text(code,encoding='utf-8')
print('Generalized the contraction rounds and the final coordinate box.')

definitions=ROOT/'formalization/Definitions'
definitions.mkdir(exist_ok=True)
for name in ['Basic','GapComparison']:
    file='Def_HlawkaSchatten_'+('DiagonalConstruction_Basic' if name=='Basic' else name)+'.lean'
    cached=ROOT/'.test-tmp/prove2me/lean/Definitions'/file
    # Preserve the platform definition bytes and their original notices.
    if cached.exists():
        (definitions/file).write_bytes(cached.read_bytes())
    elif not (definitions/file).exists():
        raise FileNotFoundError('Missing pinned public definition: '+file)

geometry=source[source.index('theorem sum3 '):source.index('\ntheorem others ')]
geometry+='\n'+source[source.index('theorem offperm '):source.index('/-! ## The facts used')]
header3='''import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Hlawka21.ContractionRounds

/- Coordinate lemmas adapted from the attributed cutoff-32 implementation;
   original lpNorm definition by Ezzeri Esa, Apache-2.0. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction
abbrev Triple := Fin 3 → Fin 3 → ℝ

'''
code=header3+geometry+'\nend HlawkaSchatten.DiagonalCutoff21\n'
(ROOT/'formalization/Hlawka21/NormGeometry.lean').write_text(code,encoding='utf-8')

body=source[source.index('theorem facts_of '):source.index('/-! ## Contraction rounds')]
body=body[body.index(' := by')+len(' := by'):]
body=re.sub(r'\bv\b','vtotal',body)
body=re.sub(r'\bhv\b','hvtotal',body)
body=body.replace('(vtotal :=','(v :=')
tail_start=body.index('  have htail :')
tail_end=body.index('  have hoffsum0 :')
body=body[:tail_start]+body[tail_end:]
for old,new in [('1158/1000','u'),('555/1000','ell'),('79/100','v'),
    ('2000 / (448 * p)','2 / (c * p)'),('2000 / (448 * α)','2 / (c * α)'),
    ('3 / 10^10','3 * eps'),('1/10^10','eps'),('3 * q','A'),
    ('2 / ((448/1000) * p)','2 / (c * p)'),
    ('mono_t hα hαp','mono_deficit hc0 hα hαp hcrit')]:
    body=body.replace(old,new)
body=body.replace('X i j ≤ u :=','X i j ≤ w :=')
body=body.replace('    have e : 2 / (c * p) = 2 / (c * p) := by field_simp; norm_num\n    rw [e] at hG\n','')
body=body.replace('div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)',
    'div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hαp hc0.le)')
body=body.replace('have hp : 1 ≤ p := by linarith','have hp : 1 ≤ p := hp1')
body=body.replace('refine ⟨hp, hcpos','refine ⟨fun i ↦ lpNorm_nonneg3 p (X i), hp, hcpos')
body=body.replace('fun i j h ↦ (hoff i j h).1','fun i j h ↦ hv.le.trans (hoff i j h).1')
header4='''import Definitions.Def_HlawkaSchatten_GapComparison
import Hlawka21.NormGeometry
import Hlawka21.Budget

/- Normalized norm data imply every premise used by the contraction rounds.
   Adapted from @bwdaugherty's cutoff-32 facts_of; all cutoff, box, gap and
   tail constants are parameters, with the original lpNorm unchanged. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

def coordinateBox (ell u v w : ℝ) (X : Triple) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w

theorem facts_of {p α β tlo thia thib D δ h A c eps ell u v w : ℝ} {X : Triple}
    (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β) (hp1 : 1 ≤ p)
    (hc0 : 0 < c) (hcrit : 6 * Real.log 2 ≤ 2 / c)
    (hell : 0 < ell) (hv : 0 < v) (hA : 0 < A)
    (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthia : (1/2 : ℝ) ^ (1/α) ≤ thia) (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : 2 / (c * α) + 3 * eps - 6 * (1 - thia) ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : 2 / (c * α) + 3 * eps ≤ h)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < A)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / (c * p))
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ (X j i + X k i) + eps) :
    Facts p (cp p) D δ h A (2 * thib) tlo X (fun i ↦ lpNorm p (X i)) := by'''
code=header4+body+'\nend HlawkaSchatten.DiagonalCutoff21\n\n#print axioms HlawkaSchatten.DiagonalCutoff21.facts_of\n'
assert 'sorry' not in code and '32 ≤' not in code
(ROOT/'formalization/Hlawka21/ContractionFacts.lean').write_text(code,encoding='utf-8')
print('Connected normalized original norms to the generalized contraction facts.')

coarse_source=(ROOT/'sources/coarse32.lean').read_text(encoding='utf-8')
basics=coarse_source[coarse_source.index('section Basic'):coarse_source.index('\nsection Deficit')]
basic_header='''import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Norm laws from @bwdaugherty's accepted cutoff-32 coarse localization,
   submission d5944a03-85b4-4962-b146-4e6c7e7e50c7, Apache-2.0,
   based on Ezzeri Esa's original coordinate lpNorm definition. -/
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

'''
(ROOT/'formalization/Hlawka21/NormBasic.lean').write_text(basic_header+basics+'\nend HlawkaSchatten.DiagonalCutoff21\n',encoding='utf-8')
