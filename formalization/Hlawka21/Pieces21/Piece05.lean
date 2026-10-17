import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab040
import Hlawka21.Localized21.Slab041
import Hlawka21.Localized21.Slab042
import Hlawka21.Localized21.Slab043
import Hlawka21.Localized21.Slab044
import Hlawka21.Localized21.Slab045
import Hlawka21.Localized21.Slab046
import Hlawka21.Localized21.Slab047

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece21_05 (p : ℝ) (hpa : (89/4 : ℝ) ≤ p)
    (hpb : p ≤ (45/2 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (179/8 : ℝ) with hl | hr
  ·
    rcases le_total p (357/16 : ℝ) with hll | hlr
    ·
      rcases le_total p (713/32 : ℝ) with hlll | hllr
      ·
        have hh := localize21_slab040 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (19453740635099/12148500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (14078199927109/2429700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab041 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (155875380935527/97324500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (112789399416053/19464900000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (715/32 : ℝ) with hlrl | hlrr
      ·
        have hh := localize21_slab042 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (4878775976153/3045656250000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (56476599707617/9746100000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab043 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (62546511366331/39039000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (22623399882883/3903900000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (359/16 : ℝ) with hrl | hrr
    ·
      rcases le_total p (717/32 : ℝ) with hrll | hrlr
      ·
        have hh := localize21_slab044 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (19576465199243/12216750000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (28320199853399/4886700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab045 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (156857159692213/97870500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (113444599412777/19574100000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (719/32 : ℝ) with hrrl | hrrr
      ·
        have hh := localize21_slab046 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (78551297086889/49003500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (56804199705979/9800700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab047 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (78674012322623/49071750000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (113772199411139/19628700000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece21_05
