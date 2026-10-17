import Hlawka21.CoarseFailure26
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window26
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.coarse_failure_window26 :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
    ∀ x y z : Fin 3 → ℝ, hlawkaDeficit p (cyclicConstant p) x y z < 0 →
    ∃ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3/4 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) ∧
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
      lpNorm p (X 0 + X 1 + X 2) < 3 * (197/500 : ℝ) ∧
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  intro p hp hpmax x y z hf
  have hs := HlawkaSchatten.DiagonalCutoff21.scalar_window26 p hp hpmax
  obtain ⟨X, hbox, hS, hT, hG, hfail⟩ := HlawkaSchatten.DiagonalCutoff21.coarse_failure26
    hp hs.1 (by norm_num) (by norm_num) hs.2.2 x y z hf
  refine ⟨X, ?_, ?_, hS, hT, hG, hfail⟩
  · intro i
    simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using hbox i i
  · intro j i hji
    simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using hbox j i

#print axioms HlawkaSchatten.DiagonalCutoff21.coarse_failure_window26
