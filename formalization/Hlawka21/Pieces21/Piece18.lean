import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab138
import Hlawka21.Localized21.Slab139
import Hlawka21.Localized21.Slab140
import Hlawka21.Localized21.Slab141
import Hlawka21.Localized21.Slab142
import Hlawka21.Localized21.Slab143
import Hlawka21.Localized21.Slab144
import Hlawka21.Localized21.Slab145

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece21_18 (p : ℝ) (hpa : (405/16 : ℝ) ≤ p)
    (hpb : p ≤ (409/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (407/16 : ℝ) with hl | hr
  ·
    rcases le_total p (203/8 : ℝ) with hll | hlr
    ·
      rcases le_total p (811/32 : ℝ) with hlll | hllr
      ·
        have hh := localize21_slab138 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (35933285990507/22113000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (12867799933661/2211300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab139 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (179911534997083/110701500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (128841799335791/22140300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (813/32 : ℝ) with hlrl | hlrr
      ·
        have hh := localize21_slab140 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (90078318076919/55419000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (32251399833743/5541900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab141 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (180401733643111/110974500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (129169399334153/22194900000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (51/2 : ℝ) with hrl | hrr
    ·
      rcases le_total p (815/32 : ℝ) with hrll | hrlr
      ·
        have hh := localize21_slab142 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (45161707282687/27777750000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (64666599666667/11111100000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab143 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (9044596092167/5562375000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (25899399866503/4449900000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (817/32 : ℝ) with hrrl | hrrr
      ·
        have hh := localize21_slab144 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (2830265791711/1740375000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (8103799958231/1392300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab145 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (362764195006901/223041000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (129824599330877/22304100000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece21_18
