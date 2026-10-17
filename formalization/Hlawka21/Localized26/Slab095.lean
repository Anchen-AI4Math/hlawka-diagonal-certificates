import Hlawka21.Window26.Slab095
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

theorem localize26_slab095 (p : ℝ) (hpa : (511/16 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (72430689/62500000 : ℝ)) ∧ coordinateBox (5657/10000 : ℝ) (219/200 : ℝ) (1663/2000 : ℝ) (5757/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (192388679980159/113186500000000 : ℝ) ≤ X j i + X k i) ∧
    (132623799320881/22637300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (489265291/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(511/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (489265291/500000000 : ℝ))
      (by norm_num) 16 511 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(511/16 : ℝ)) ≤ (978530583/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (978530583/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 511 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(32 : ℝ)) ≤ (978572063/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (978572063/1000000000 : ℝ))
      (by norm_num) (by norm_num) 1 32 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (354928597993/28296625000000 : ℝ) (6409173/1000000000 : ℝ) (3200000679119/22637300000000 : ℝ) (591/500 : ℝ) (978572063/500000000 : ℝ) (489265291/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (511/16 : ℝ)) (β := (32 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (354928597993/28296625000000 : ℝ)) (δ := (6409173/1000000000 : ℝ)) (h := (3200000679119/22637300000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (489265291/500000000 : ℝ)) (thia := (978530583/1000000000 : ℝ)) (thib := (978572063/1000000000 : ℝ))
      (ell := (477/1000 : ℝ)) (u := (1183/1000 : ℝ))
      (v := (3/4 : ℝ)) (w := (1183/1000 : ℝ))
      (by norm_num) hpa hpb hp1 (by norm_num) hcrit
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) htlo hthia hthib
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hB hS hT hG htail
    norm_num at facts
    exact facts
  have hn0 := initial_norm_lower hp1 X hB
  have hh := contract26_slab095 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.localize26_slab095
