import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab064
import Hlawka21.Localized21.Slab065
import Hlawka21.Localized21.Slab066
import Hlawka21.Localized21.Slab067
import Hlawka21.Localized21.Slab068
import Hlawka21.Localized21.Slab069
import Hlawka21.Localized21.Slab070
import Hlawka21.Localized21.Slab071

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece21_08 (p : ℝ) (hpa : (23 : ℝ) ≤ p)
    (hpb : p ≤ (93/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (185/8 : ℝ) with hl | hr
  ·
    rcases le_total p (369/16 : ℝ) with hll | hlr
    ·
      rcases le_total p (737/32 : ℝ) with hlll | hllr
      ·
        have hh := localize21_slab064 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (10094981332321/6279000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (3642399981163/627900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab065 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (161765057643169/100600500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (116720599396397/20120100000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (739/32 : ℝ) with hlrl | hlrr
      ·
        have hh := localize21_slab066 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (162010409505379/100737000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (58442199697789/10073700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab067 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (162255758917141/100873500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (117048199394759/20174700000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (371/16 : ℝ) with hrl | hrr
    ·
      rcases le_total p (741/32 : ℝ) with hrll | hrlr
      ·
        have hh := localize21_slab068 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (1625011033573/1010100000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (5860599969697/1010100000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab069 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (81373222067309/50573250000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (117375799393121/20229300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (743/32 : ℝ) with hrrl | hrrr
      ·
        have hh := localize21_slab070 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (162991781146993/101283000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (58769799696151/10128300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab071 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group00 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (1139124440087/716625000000 : ℝ) ≤ (326474230814783/202839000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (117703399391483/20283900000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece21_08
