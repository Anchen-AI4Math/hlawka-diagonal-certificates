import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab008
import Hlawka21.Localized21.Slab009
import Hlawka21.Localized21.Slab010
import Hlawka21.Localized21.Slab011
import Hlawka21.Localized21.Slab012
import Hlawka21.Localized21.Slab013
import Hlawka21.Localized21.Slab014
import Hlawka21.Localized21.Slab015

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece21_01 (p : ℝ) (hpa : (85/4 : ℝ) ≤ p)
    (hpb : p ≤ (43/2 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (171/8 : ℝ) with hl | hr
  ·
    rcases le_total p (341/16 : ℝ) with hll | hlr
    ·
      rcases le_total p (681/32 : ℝ) with hlll | hllr
      ·
        have hh := localize21_slab008 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (7388647222319/4641000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (2684599986077/464100000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab009 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (74009274572951/46478250000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (107547799442261/18591300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (683/32 : ℝ) with hlrl | hlrr
      ·
        have hh := localize21_slab010 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (148264148879827/93093000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (53855799720721/9309300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab011 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (297019484857601/186459000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (107875399440623/18645900000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (343/16 : ℝ) with hrl | hrr
    ·
      rcases le_total p (685/32 : ℝ) with hrll | hrlr
      ·
        have hh := localize21_slab012 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (74377666337237/46683000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (27009799859951/4668300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab013 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (59600366799511/37401000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (21640599887797/3740100000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (687/32 : ℝ) with hrrl | hrrr
      ·
        have hh := localize21_slab014 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (149246496888469/93639000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (54183399719083/9363900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab015 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (37373018014327/23443875000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (108530599437347/18755100000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece21_01
