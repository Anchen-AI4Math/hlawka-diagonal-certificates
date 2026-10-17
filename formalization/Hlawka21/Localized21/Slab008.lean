import Hlawka21.Window21.Slab008
import Hlawka21.LinearFloors
import Mathlib.Analysis.Complex.ExponentialBounds

/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab008 (p : ℝ) (hpa : (85/4 : ℝ) ≤ p) (hpb : p ≤ (681/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1192491431/1000000000 : ℝ)) ∧ coordinateBox (553/1250 : ℝ) (5517/5000 : ℝ) (947/1250 : ℝ) (1479/1250 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (7388647222319/4641000000000 : ℝ) ≤ X j i + X k i) ∧
    (2684599986077/464100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (967907561/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(85/4 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (967907561/1000000000 : ℝ))
      (by norm_num) 4 85 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(85/4 : ℝ)) ≤ (483953781/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (483953781/500000000 : ℝ))
      (by norm_num) (by norm_num) 4 85 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(681/32 : ℝ)) ≤ (241988481/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (241988481/250000000 : ℝ))
      (by norm_num) (by norm_num) 32 681 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (53177055341/2320500000000 : ℝ) (5919007/500000000 : ℝ) (100000013923/464100000000 : ℝ) (3033/2500 : ℝ) (241988481/125000000 : ℝ) (967907561/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (85/4 : ℝ)) (β := (681/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (53177055341/2320500000000 : ℝ)) (δ := (5919007/500000000 : ℝ)) (h := (100000013923/464100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (967907561/1000000000 : ℝ)) (thia := (483953781/500000000 : ℝ)) (thib := (241988481/250000000 : ℝ))
      (ell := (189/500 : ℝ)) (u := (607/500 : ℝ))
      (v := (349/500 : ℝ)) (w := (607/500 : ℝ))
      (by norm_num) hpa hpb hp1 (by norm_num) hcrit
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) htlo hthia hthib
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hB hS hT hG htail
    norm_num at facts
    exact facts
  have hn0 := initial_norm_lower hp1 X hB
  have hh := contract21_slab008 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.localize21_slab008
