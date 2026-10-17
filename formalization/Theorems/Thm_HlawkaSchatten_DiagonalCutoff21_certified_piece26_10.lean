import Hlawka21.Pieces26.Piece10
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.certified_piece26_10 :
    ∀ p : ℝ, (31 : ℝ) ≤ p → p ≤ (63/2 : ℝ) →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ)) →
      (∀ j i, j ≠ i → (3/4 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : HlawkaSchatten.DiagonalCutoff21.coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ)
      (3/4 : ℝ) (1183/1000 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using ho j i hji
  exact HlawkaSchatten.DiagonalCutoff21.nonneg_piece26_10 p hp hpmax X hB hS hT hG

#print axioms HlawkaSchatten.DiagonalCutoff21.certified_piece26_10
