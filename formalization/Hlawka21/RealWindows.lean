import Hlawka21.CoarseFailure21
import Hlawka21.CoarseFailure26
import Hlawka21.Real21.Chunk00
import Hlawka21.Real21.Chunk01
import Hlawka21.Real21.Chunk02
import Hlawka21.Real21.Chunk03
import Hlawka21.Real21.Chunk04
import Hlawka21.Real21.Chunk05
import Hlawka21.Real21.Chunk06
import Hlawka21.Real21.Chunk07
import Hlawka21.Real21.Chunk08
import Hlawka21.Real21.Chunk09
import Hlawka21.Real26.Chunk00
import Hlawka21.Real26.Chunk01
import Hlawka21.Real26.Chunk02
import Hlawka21.Real26.Chunk03
import Hlawka21.Real26.Chunk04
import Hlawka21.Real26.Chunk05

/- Arbitrary original failures reduce to the already checked localized chunks.
   The input triples have no norm, sign, nonzero or coordinate restrictions. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem real_three_window21 :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp hpmax x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    exact sub_neg.mpr (lt_of_not_ge hn)
  have hs := scalar_window21 p hp hpmax
  obtain ⟨X, hB, hS, hT, hG, hfail⟩ := coarse_failure21
    hp hs.1 (by norm_num) (by norm_num) hs.2.2 x y z hf
  norm_num at hT
  have hnonneg : 0 ≤ tripleDeficit p (cyclicConstant p) X := by
    rcases le_total p (47/2 : ℝ) with hl | hr
    ·
      rcases le_total p (22 : ℝ) with hll | hlr
      ·
        rcases le_total p (43/2 : ℝ) with hlll | hllr
        ·
          exact localized_nonneg21_chunk00 p (by linarith) (by linarith) X hB hS hT hG
        ·
          exact localized_nonneg21_chunk01 p (by linarith) (by linarith) X hB hS hT hG
      ·
        rcases le_total p (45/2 : ℝ) with hlrl | hlrr
        ·
          exact localized_nonneg21_chunk02 p (by linarith) (by linarith) X hB hS hT hG
        ·
          rcases le_total p (23 : ℝ) with hlrrl | hlrrr
          ·
            exact localized_nonneg21_chunk03 p (by linarith) (by linarith) X hB hS hT hG
          ·
            exact localized_nonneg21_chunk04 p (by linarith) (by linarith) X hB hS hT hG
    ·
      rcases le_total p (49/2 : ℝ) with hrl | hrr
      ·
        rcases le_total p (24 : ℝ) with hrll | hrlr
        ·
          exact localized_nonneg21_chunk05 p (by linarith) (by linarith) X hB hS hT hG
        ·
          exact localized_nonneg21_chunk06 p (by linarith) (by linarith) X hB hS hT hG
      ·
        rcases le_total p (25 : ℝ) with hrrl | hrrr
        ·
          exact localized_nonneg21_chunk07 p (by linarith) (by linarith) X hB hS hT hG
        ·
          rcases le_total p (51/2 : ℝ) with hrrrl | hrrrr
          ·
            exact localized_nonneg21_chunk08 p (by linarith) (by linarith) X hB hS hT hG
          ·
            exact localized_nonneg21_chunk09 p (by linarith) (by linarith) X hB hS hT hG
  exact (not_lt_of_ge hnonneg) hfail

theorem real_three_window26 :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp hpmax x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    exact sub_neg.mpr (lt_of_not_ge hn)
  have hs := scalar_window26 p hp hpmax
  obtain ⟨X, hB, hS, hT, hG, hfail⟩ := coarse_failure26
    hp hs.1 (by norm_num) (by norm_num) hs.2.2 x y z hf
  norm_num at hT
  have hnonneg : 0 ≤ tripleDeficit p (cyclicConstant p) X := by
    rcases le_total p (29 : ℝ) with hl | hr
    ·
      rcases le_total p (27 : ℝ) with hll | hlr
      ·
        exact localized_nonneg26_chunk00 p (by linarith) (by linarith) X hB hS hT hG
      ·
        rcases le_total p (28 : ℝ) with hlrl | hlrr
        ·
          exact localized_nonneg26_chunk01 p (by linarith) (by linarith) X hB hS hT hG
        ·
          exact localized_nonneg26_chunk02 p (by linarith) (by linarith) X hB hS hT hG
    ·
      rcases le_total p (30 : ℝ) with hrl | hrr
      ·
        exact localized_nonneg26_chunk03 p (by linarith) (by linarith) X hB hS hT hG
      ·
        rcases le_total p (31 : ℝ) with hrrl | hrrr
        ·
          exact localized_nonneg26_chunk04 p (by linarith) (by linarith) X hB hS hT hG
        ·
          exact localized_nonneg26_chunk05 p (by linarith) (by linarith) X hB hS hT hG
  exact (not_lt_of_ge hnonneg) hfail

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.real_three_window21
#print axioms HlawkaSchatten.DiagonalCutoff21.real_three_window26
