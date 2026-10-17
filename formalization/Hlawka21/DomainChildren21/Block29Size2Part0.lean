import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab114
import Hlawka21.Localized21.Slab115

set_option autoImplicit false
set_option maxHeartbeats 200000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem bounds_localized_domain2_21_29_part0 (p : ℝ) (hpa : (393/16 : ℝ) ≤ p)
    (hpb : p ≤ (197/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  rcases le_total p (787/32 : ℝ) with hl | hr
  ·
    have hh := localize21_slab114 p (by linarith) (by linarith) X hB hS hT hG
    have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
      coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      simpa [coordinateBox] using hBx j j
    · intro j i hji
      simpa [coordinateBox, hji] using hBx j i
    · intro j
      exact (hh.1 j).trans (by norm_num)
    · intro i j k hij hik hjk
      exact (show (82967765642843/51460500000000 : ℝ) ≤ (173783016314251/107289000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
    · exact (show (59752599691237/10292100000000 : ℝ) ≤ (62373399678133/10728900000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    have hh := localize21_slab115 p (by linarith) (by linarith) X hB hS hT hG
    have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
      coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      simpa [coordinateBox] using hBx j j
    · intro j i hji
      simpa [coordinateBox, hji] using hBx j i
    · intro j
      exact (hh.1 j).trans (by norm_num)
    · intro i j k hij hik hjk
      exact (show (82967765642843/51460500000000 : ℝ) ≤ (43507048419193/26856375000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
    · exact (show (59752599691237/10292100000000 : ℝ) ≤ (124910599355447/21485100000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
