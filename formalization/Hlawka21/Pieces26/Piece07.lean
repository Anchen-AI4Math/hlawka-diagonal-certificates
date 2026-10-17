import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Hlawka21.PieceTools
import Hlawka21.Localized26.Slab056
import Hlawka21.Localized26.Slab057
import Hlawka21.Localized26.Slab058
import Hlawka21.Localized26.Slab059
import Hlawka21.Localized26.Slab060
import Hlawka21.Localized26.Slab061
import Hlawka21.Localized26.Slab062
import Hlawka21.Localized26.Slab063

set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem nonneg_piece26_07 (p : ℝ) (hpa : (59/2 : ℝ) ≤ p)
    (hpb : p ≤ (30 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (119/4 : ℝ) with hl | hr
  ·
    rcases le_total p (237/8 : ℝ) with hll | hlr
    ·
      rcases le_total p (473/16 : ℝ) with hlll | hllr
      ·
        have hh := localize26_slab056 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (5519561267617/3267125000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (15282199921589/2613700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab057 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (354060501204873/209539000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (122523399371383/20953900000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (475/16 : ℝ) with hlrl | hlrr
      ·
        have hh := localize26_slab058 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (177434533430861/104991000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (61394599685027/10499100000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab059 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (14227104888363/8417000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (4922199974749/841700000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (239/8 : ℝ) with hrl | hrr
    ·
      rcases le_total p (477/16 : ℝ) with hrll | hrlr
      ·
        have hh := localize26_slab060 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (89121540370211/52717000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (30830199841849/5271700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab061 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (178647344396471/105655500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (123586599366067/21131100000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      rcases le_total p (479/16 : ℝ) with hrrl | hrrr
      ·
        have hh := localize26_slab062 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (3581032030011/2117540000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (61926199682369/10587700000000 : ℝ) by norm_num).trans hh.2.2.2.le
      ·
        have hh := localize26_slab063 p (by linarith) (by linarith) X hB hS hT hG
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
          exact (show (82967765642843/51460500000000 : ℝ) ≤ (179455851581307/106098500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
        · exact (show (59752599691237/10292100000000 : ℝ) ≤ (124118199363409/21219700000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.nonneg_piece26_07
