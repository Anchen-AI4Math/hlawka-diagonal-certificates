import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Hlawka21.PieceTools
import Hlawka21.Localized26.Slab064
import Hlawka21.Localized26.Slab065
import Hlawka21.Localized26.Slab066
import Hlawka21.Localized26.Slab067
import Hlawka21.Localized26.Slab068
import Hlawka21.Localized26.Slab069
import Hlawka21.Localized26.Slab070
import Hlawka21.Localized26.Slab071

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece26_08 (p : ℝ) (hpa : (30 : ℝ) ≤ p)
    (hpb : p ≤ (61/2 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (121/4 : ℝ) with hl | hr
  ·
    rcases le_total p (241/8 : ℝ) with hll | hlr
    ·
      rcases le_total p (481/16 : ℝ) with hlll | hllr
      ·
        have hh := localize26_slab064 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (281031398957/166125000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (777399996013/132900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab065 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (180264333026957/106541500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (124649799360751/21308300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (483/16 : ℝ) with hlrl | hlrr
      ·
        have hh := localize26_slab066 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (22583570483971/13345375000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (62457799679711/10676300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab067 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (362145578627059/213969000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (125181399358093/21396900000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (243/8 : ℝ) with hrl | hrr
    ·
      rcases le_total p (485/16 : ℝ) with hrll | hrlr
      ·
        have hh := localize26_slab068 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (9073850401151/5360300000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (31361799839191/5360300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab069 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (3637624416161/2148550000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (25142599871087/4297100000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (487/16 : ℝ) with hrrl | hrrr
      ·
        have hh := localize26_slab070 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (182285427729089/107649000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (62989399677053/10764900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab071 p (by linarith) (by linarith) X hB hS hT hG
        have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
          coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        apply domain_nonneg_group01 p (by linarith) (by linarith) X
        · intro j
          simpa [coordinateBox] using hBx j j
        · intro j i hji
          simpa [coordinateBox, hji] using hBx j i
        · intro j
          exact (hh.1 j).trans (by norm_num)
        · exact hT.le.trans (by norm_num)
        · intro i j k hij hik hjk
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (182689626797067/107870500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (126244599352777/21574100000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece26_08
