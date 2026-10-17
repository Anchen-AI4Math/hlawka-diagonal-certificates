import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab080
import Hlawka21.Localized21.Slab081

set_option autoImplicit false
set_option maxHeartbeats 200000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem bounds_localized_domain4_21_20 (p : ℝ) (hpa : (47/2 : ℝ) ≤ p)
    (hpb : p ≤ (377/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  rcases le_total p (753/32 : ℝ) with hl | hr
  ·
    have hh := localize21_slab080 p (by linarith) (by linarith) X hB hS hT hG
    have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
      coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      simpa [coordinateBox] using hBx j j
    · intro j i hji
      simpa [coordinateBox, hji] using hBx j i
    · intro j
      exact (hh.1 j).trans (by norm_num)
    · intro i j k hij hik hjk
      exact (show (1139124440087/716625000000 : ℝ) ≤ (10340309008369/6415500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
    · exact (show (3314799982801/573300000000 : ℝ) ≤ (7448599961507/1283100000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    have hh := localize21_slab081 p (by linarith) (by linarith) X hB hS hT hG
    have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
      coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      simpa [coordinateBox] using hBx j j
    · intro j i hji
      simpa [coordinateBox, hji] using hBx j i
    · intro j
      exact (hh.1 j).trans (by norm_num)
    · intro i j k hij hik hjk
      exact (show (1139124440087/716625000000 : ℝ) ≤ (331380479096627/205569000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
    · exact (show (3314799982801/573300000000 : ℝ) ≤ (119341399383293/20556900000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
