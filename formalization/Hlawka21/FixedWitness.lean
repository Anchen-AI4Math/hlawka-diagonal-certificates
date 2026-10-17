import Hlawka21.CyclicUpper
import Hlawka21.ContractionCore

/- Fixed cyclic witnesses and Bernoulli transport of endpoint root bounds.
   This is a kernel-checkable route to the remaining scalar lower bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem root_transfer_upper {m p B b A : ℝ} (hm : 0 < m) (hp : m ≤ p)
    (hB : 0 ≤ B) (hBb : B ≤ b) (hb : b ≤ A^m) (hA : 1 ≤ A) :
    B^(1/p) ≤ 1+(m/p)*(A-1) := by
  have hp0 : 0 < p := hm.trans_le hp
  have hmp : 0 ≤ m/p := div_nonneg hm.le hp0.le
  have hbase : 0 ≤ 1+(m/p)*(A-1) := by positivity
  have hratio : 1 ≤ p/m := (le_div_iff₀ hm).mpr (by simpa using hp)
  have hb0 := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ (m/p)*(A-1) by
      have hnon := mul_nonneg hmp (sub_nonneg.mpr hA)
      linarith) hratio
  have hroot : A ≤ (1+(m/p)*(A-1))^(p/m) := by
    convert hb0 using 1 <;> field_simp <;> ring
  have hpow : A^m ≤ (1+(m/p)*(A-1))^p := by
    have h := Real.rpow_le_rpow (by linarith : 0 ≤ A) hroot hm.le
    rw [← Real.rpow_mul hbase] at h
    convert h using 1 <;> field_simp
  calc
    _ ≤ ((1+(m/p)*(A-1))^p)^(1/p) :=
      Real.rpow_le_rpow hB (hBb.trans (hb.trans hpow)) (by positivity)
    _ = _ := by rw [one_div, Real.rpow_rpow_inv hbase hp0.ne']

theorem cyclic_denominator_positive21 {p t : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : 0 < 6*cyclicA p t-3*cyclicB p t := by
  obtain ⟨hb,_,_,_⟩ := root_two_three_bounds hp hp32
  have hAb := (cyclicA_lower21 hp ht).1
  have hB := cyclicB_upper21 hp ht
  have hp0 : 0 < p := by linarith
  have hu32 : (1/32 : ℝ) ≤ 1/p := one_div_le_one_div_of_le hp0 hp32
  have hA : 1+1/64 ≤ cyclicA p t := by nlinarith [sq_nonneg (1/p)]
  linarith

theorem cyclicB_lower_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  have h : (2 : ℝ)^p ≤ 2*|1-t|^p+2^p := by
    have := Real.rpow_nonneg (abs_nonneg (1-t)) p
    linarith
  calc
    (2 : ℝ) = (2^p)^(1/p) := by rw [one_div, Real.rpow_rpow_inv (by norm_num) hp.ne']
    _ ≤ cyclicB p t := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem cyclicRatio_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 21 ≤ p) (hp32 : p ≤ 32) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicRatio p t := by
  have hp0 : 0 < p := by linarith
  have htpos : 0 < t := by linarith
  have htp : t^p ≤ t^alpha := Real.rpow_le_rpow_of_exponent_ge htpos ht1 hap
  have hAp : cyclicA p t ≤ 1+(alpha/p)*(Aup-1) := by
    exact root_transfer_upper ha hap (by positivity) (by linarith) hAend hAup
  have hap' : (3 : ℝ)^(1/p) ≤ 1+(alpha/p)*(aup-1) :=
    root_transfer_upper ha hap (by norm_num) le_rfl haend haup
  have hB := cyclicB_lower_two (t := t) hp0
  have hden := cyclic_denominator_positive21 hp hp32 (show t ∈ Set.Icc (1/2 : ℝ) 2 by exact ⟨ht0,by linarith⟩)
  have hmono := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left ha.le hp0 hpb) hH
  have hpos : 0 < 3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hAp (show 0 ≤ 6*c*p-3 by linarith)
  have h2 := mul_le_mul_of_nonneg_left hap' (show 0 ≤ 2-t by linarith)
  have heq : (6*c*p-3)*(1+(alpha/p)*(Aup-1))+(2-t)*(1+(alpha/p)*(aup-1)) =
      6*c*p-(3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) := by
    field_simp
    ring
  have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*c*p by positivity)
  unfold cyclicRatio
  rw [abs_of_nonneg (show 0 ≤ 2-t by linarith), lt_div_iff₀ hden]
  nlinarith

theorem cyclicConstant_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 21 ≤ p) (hp32 : p ≤ 32) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicConstant p := by
  have hratio := cyclicRatio_lower_endpoint hp hp32 ha hap hpb hc hcp ht0 ht1 hAup haup hAend haend hH hcheck
  have hbounded : BddAbove (cyclicRatio p '' Set.Icc (1/2 : ℝ) 2) := by
    refine ⟨p/2, ?_⟩
    rintro y ⟨s,hs,rfl⟩
    exact cyclicRatio_upper21 hp hp32 hs
  have ht : t ∈ Set.Icc (1/2 : ℝ) 2 := ⟨ht0,by linarith⟩
  exact hratio.trans_le (le_csSup hbounded (Set.mem_image_of_mem (cyclicRatio p) ht))

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.cyclicConstant_lower_endpoint
