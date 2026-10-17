import Hlawka21.GroupedNonneg.Group00
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 :
    ∀ p : ℝ, (21 : ℝ) ≤ p → p ≤ (377/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) →
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) →
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) →
      lpNorm p (X 0 + X 1 + X 2) ≤ (3033/2500 : ℝ) →
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) →
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by
  intro p hp hpmax X hd ho hN hT hJ hW
  have hB : HlawkaSchatten.DiagonalCutoff21.coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using ho j i hji
  exact HlawkaSchatten.DiagonalCutoff21.grouped_deficit_nonneg00 p hp hpmax X ⟨hB,hN,hT,hJ,hW⟩

#print axioms HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00
