import Hlawka21.Localized21.Slab000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.actual_localize21_slab000 :
    ∀ p : ℝ, (21 : ℝ) ≤ p → p ≤ (673/32 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ i, lpNorm p (X i) ≤ (596197839/500000000 : ℝ)) ∧
      (∀ i, -(689/625 : ℝ) ≤ X i i ∧ X i i ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : HlawkaSchatten.DiagonalCutoff21.coordinateBox (189/500 : ℝ) (607/500 : ℝ)
      (349/500 : ℝ) (607/500 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using ho j i hji
  have hh := HlawkaSchatten.DiagonalCutoff21.localize21_slab000 p hp hpmax X hB hS hT hG
  refine ⟨hh.1, ?_, ?_, hh.2.2.1, hh.2.2.2⟩
  · intro i
    simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using hh.2.1 i i
  · intro j i hji
    simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using hh.2.1 j i

#print axioms HlawkaSchatten.DiagonalCutoff21.actual_localize21_slab000
