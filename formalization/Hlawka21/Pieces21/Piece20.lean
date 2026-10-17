import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab154
import Hlawka21.Localized21.Slab155
import Hlawka21.Localized21.Slab156
import Hlawka21.Localized21.Slab157
import Hlawka21.Localized21.Slab158
import Hlawka21.Localized21.Slab159

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece21_20 (p : ℝ) (hpa : (413/16 : ℝ) ≤ p)
    (hpb : p ≤ (26 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (829/32 : ℝ) with hl | hr
  ·
    rcases le_total p (827/32 : ℝ) with hll | hlr
    ·
      have hh := localize21_slab154 p (by linarith) (by linarith) X hB hS hT hG
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
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (11474234388229/7046812500000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (65649399661753/11274900000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (207/8 : ℝ) with hlrl | hlrr
      ·
        have hh := localize21_slab155 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (367665617125403/225771000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (131462599322687/22577100000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab156 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (92038932253349/56511000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (32906599830467/5651100000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (415/16 : ℝ) with hrl | hrr
    ·
      have hh := localize21_slab157 p (by linarith) (by linarith) X hB hS hT hG
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
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (184322916236803/113158500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (131790199321049/22631700000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (831/32 : ℝ) with hrrl | hrrr
      ·
        have hh := localize21_slab158 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (18456796692241/11329500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (13195399932023/2265900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab159 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (184813014190057/113431500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (132117799319411/22686300000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece21_20
