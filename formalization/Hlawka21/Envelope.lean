import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Hlawka21.Tail

/- The envelope comparison can be proved from one rational integer-power
   certificate per window. Bernoulli transports that endpoint certificate
   to every larger real exponent. No interval-checker oracle is assumed. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem bernoulli_scale (m : ℕ) (hm : 1 ≤ m) {p d : ℝ}
    (hp : (m : ℝ) ≤ p) (hd : 0 ≤ d) (hdm : d < m) :
    (1-d/(m : ℝ))^m ≤ (1-d/p)^p := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hm)
  have hp0 : 0 < p := hm0.trans_le hp
  have hbase : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have he : (1 : ℝ) ≤ p/(m : ℝ) := (le_div_iff₀ hm0).mpr (by simpa using hp)
  have hs : -1 ≤ -d/p := by
    have h := (div_le_one hp0).mpr (show d ≤ p by linarith)
    simpa only [neg_div] using neg_le_neg h
  have hb := one_add_mul_self_le_rpow_one_add hs he
  have hroot : 1-d/(m : ℝ) ≤ (1-d/p)^(p/(m : ℝ)) := by
    convert hb using 1 <;> field_simp <;> ring
  calc
    _ ≤ ((1-d/p)^(p/(m : ℝ)))^m := pow_le_pow_left₀
      (by apply sub_nonneg.mpr; exact (div_le_one hm0).mpr hdm.le) hroot m
    _ = (1-d/p)^p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
      congr 1
      field_simp

theorem envelope_linear_of_certificate (m : ℕ) (hm : 1 ≤ m)
    {p q c : ℝ} (hp : (m : ℝ) ≤ p) (hq : 0 ≤ q) (hq1 : q < 1) (hc : 0 < c)
    (hdm : (1-q)/(2*c) < m)
    (hcert : (1+q^m)/2 < (1-((1-q)/(2*c))/(m : ℝ))^m) :
    scalarEnvelope p q < c*p := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hm)
  have hp0 : 0 < p := hm0.trans_le hp
  set d := (1-q)/(2*c) with hd_def
  have hd : 0 ≤ d := div_nonneg (by linarith) (by positivity)
  have hscale := bernoulli_scale m hm hp hd hdm
  have hqpow : q^p ≤ q^m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge' hq hq1.le (by positivity) hp
  have hg0 : 0 ≤ scalarEnvelopeRoot p q := Real.rpow_nonneg (by positivity) _
  have hgpow : scalarEnvelopeRoot p q ^ p = (1+q^p)/2 := by
    unfold scalarEnvelopeRoot
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hb0 : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have hpow : scalarEnvelopeRoot p q ^ p < (1-d/p)^p := by
    rw [hgpow]
    exact (show (1+q^p)/2 < (1-d/(m : ℝ))^m by linarith).trans_le hscale
  have hg : scalarEnvelopeRoot p q < 1-d/p :=
    (Real.rpow_lt_rpow_iff hg0 hb0 hp0).mp hpow
  have hgap : 0 < 2*(1-scalarEnvelopeRoot p q) := by
    have := div_nonneg hd hp0.le
    linarith
  have hdp : d < p*(1-scalarEnvelopeRoot p q) := by
    have ht : d/p < 1-scalarEnvelopeRoot p q := by linarith
    have hm := (div_lt_iff₀ hp0).mp ht
    simpa only [mul_comm] using hm
  have hmul := mul_lt_mul_of_pos_left hdp (show 0 < 2*c by positivity)
  have heq : 2*c*d = 1-q := by rw [hd_def]; field_simp
  unfold scalarEnvelope
  apply (div_lt_iff₀ hgap).mpr
  nlinarith

theorem envelope_linear21 {p : ℝ} (hp : 21 ≤ p) :
    scalarEnvelope p (1011/2500 : ℝ) < (273/625 : ℝ)*p := by
  apply envelope_linear_of_certificate 21 (by norm_num) hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num

theorem envelope_linear26 {p : ℝ} (hp : 26 ≤ p) :
    scalarEnvelope p (197/500 : ℝ) < (443/1000 : ℝ)*p := by
  apply envelope_linear_of_certificate 26 (by norm_num) hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.envelope_linear21
#print axioms HlawkaSchatten.DiagonalCutoff21.envelope_linear26
