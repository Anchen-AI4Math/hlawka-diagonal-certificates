import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Hlawka21.PieceTools
import Hlawka21.Localized26.Slab000
import Hlawka21.Localized26.Slab001
import Hlawka21.Localized26.Slab002
import Hlawka21.Localized26.Slab003
import Hlawka21.Localized26.Slab004
import Hlawka21.Localized26.Slab005
import Hlawka21.Localized26.Slab006
import Hlawka21.Localized26.Slab007

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece26_00 (p : ℝ) (hpa : (26 : ℝ) ≤ p)
    (hpb : p ≤ (53/2 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (105/4 : ℝ) with hl | hr
  ·
    rcases le_total p (209/8 : ℝ) with hll | hlr
    ·
      rcases le_total p (417/16 : ℝ) with hlll | hllr
      ·
        have hh := localize26_slab000 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (2405838194997/1439750000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (3355399982723/575900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab001 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (61751354181761/36946200000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (107638599445807/18473100000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (419/16 : ℝ) with hlrl | hlrr
      ·
        have hh := localize26_slab002 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (154783117132199/92587000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (53952199722239/9258700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab003 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (310375679343583/185617000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (108170199443149/18561700000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (211/8 : ℝ) with hrl | hrr
    ·
      rcases le_total p (421/16 : ℝ) with hrll | hrlr
      ·
        have hh := localize26_slab004 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (3111851051629/1860600000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (5421799972091/930300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab005 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (7799862772869/4662575000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (108701799440491/18650300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (423/16 : ℝ) with hrrl | hrrr
      ·
        have hh := localize26_slab006 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (78200974553253/46736500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (54483799719581/9347300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab007 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (2450103654287/1463976562500 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (109233399437833/18738900000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece26_00
