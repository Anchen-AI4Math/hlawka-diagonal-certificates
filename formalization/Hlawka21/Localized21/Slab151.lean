import Hlawka21.Window21.Slab151
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

theorem localize21_slab151 (p : ℝ) (hpa : (823/32 : ℝ) ≤ p) (hpb : p ≤ (103/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1194289991/1000000000 : ℝ)) ∧ coordinateBox (4691/10000 : ℝ) (2797/2500 : ℝ) (98/125 : ℝ) (5931/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (365705116865321/224679000000000 : ℝ) ≤ X j i + X k i) ∧
    (130807399325963/22467900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (973408893/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(823/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (973408893/1000000000 : ℝ))
      (by norm_num) 32 823 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(823/32 : ℝ)) ≤ (486704447/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (486704447/500000000 : ℝ))
      (by norm_num) (by norm_num) 32 823 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(103/4 : ℝ)) ≤ (973440733/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (973440733/1000000000 : ℝ))
      (by norm_num) (by norm_num) 4 103 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (2076614055263/112339500000000 : ℝ) (9495067/1000000000 : ℝ) (4000000674037/22467900000000 : ℝ) (3033/2500 : ℝ) (973440733/500000000 : ℝ) (973408893/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (823/32 : ℝ)) (β := (103/4 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (2076614055263/112339500000000 : ℝ)) (δ := (9495067/1000000000 : ℝ)) (h := (4000000674037/22467900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (973408893/1000000000 : ℝ)) (thia := (486704447/500000000 : ℝ)) (thib := (973440733/1000000000 : ℝ))
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
  have hh := contract21_slab151 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.localize21_slab151
