import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
import Hlawka21.PieceTools
import Hlawka21.Localized21.Slab032
import Hlawka21.Localized21.Slab033
import Hlawka21.Localized21.Slab034
import Hlawka21.Localized21.Slab035
import Hlawka21.Localized21.Slab036
import Hlawka21.Localized21.Slab037
import Hlawka21.Localized21.Slab038
import Hlawka21.Localized21.Slab039

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece21_04 (p : ℝ) (hpa : (22 : ℝ) ≤ p)
    (hpb : p ≤ (89/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (177/8 : ℝ) with hl | hr
  ·
    rcases le_total p (353/16 : ℝ) with hll | hlr
    ·
      rcases le_total p (705/32 : ℝ) with hlll | hllr
      ·
        have hh := localize21_slab032 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (480206631467/300300000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (1739299990991/300300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab033 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (15391161227167/9623250000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (22295799884521/3849300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (707/32 : ℝ) with hlrl | hlrr
      ·
        have hh := localize21_slab034 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (154157099181247/96369000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (55821399710893/9636900000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab035 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (308805162895007/193011000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (111806599420967/19301100000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (355/16 : ℝ) with hrl | hrr
    ·
      rcases le_total p (709/32 : ℝ) with hrll | hrlr
      ·
        have hh := localize21_slab036 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (7732402914599/4832100000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (27992599855037/4832100000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab037 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (61957412772793/38711400000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (112134199419329/19355700000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (711/32 : ℝ) with hrrl | hrrr
      ·
        have hh := localize21_slab038 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (31027800221687/19383000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (11229799941851/1938300000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize21_slab039 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (1139124440087/716625000000 : ℝ) ≤ (310768928722121/194103000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (3314799982801/573300000000 : ℝ) ≤ (112461799417691/19410300000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece21_04
