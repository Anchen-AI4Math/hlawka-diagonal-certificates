import Hlawka21.Real21.Chunk09
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.certified_nonneg21_chunk09 :
    ∀ p : ℝ, (51/2 : ℝ) ≤ p → p ≤ (26 : ℝ) →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : HlawkaSchatten.DiagonalCutoff21.coordinateBox (189/500 : ℝ) (607/500 : ℝ)
      (349/500 : ℝ) (607/500 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using ho j i hji
  exact HlawkaSchatten.DiagonalCutoff21.localized_nonneg21_chunk09 p hp hpmax X hB hS hT hG

#print axioms HlawkaSchatten.DiagonalCutoff21.certified_nonneg21_chunk09
