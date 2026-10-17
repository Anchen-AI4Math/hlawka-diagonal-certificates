import Hlawka21.CoarseFailure21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.coarse_failure_window21 :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
    ∀ x y z : Fin 3 → ℝ, hlawkaDeficit p (cyclicConstant p) x y z < 0 →
    ∃ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) ∧
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) ∧
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
      lpNorm p (X 0 + X 1 + X 2) < 3 * (1011/2500 : ℝ) ∧
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  intro p hp hpmax x y z hf
  have hs := HlawkaSchatten.DiagonalCutoff21.scalar_window21 p hp hpmax
  obtain ⟨X, hbox, hS, hT, hG, hfail⟩ := HlawkaSchatten.DiagonalCutoff21.coarse_failure21
    hp hs.1 (by norm_num) (by norm_num) hs.2.2 x y z hf
  refine ⟨X, ?_, ?_, hS, hT, hG, hfail⟩
  · intro i
    simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using hbox i i
  · intro j i hji
    simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using hbox j i

#print axioms HlawkaSchatten.DiagonalCutoff21.coarse_failure_window21
