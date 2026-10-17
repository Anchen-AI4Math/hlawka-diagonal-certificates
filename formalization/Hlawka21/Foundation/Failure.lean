import Hlawka21.Foundation.Normalization
import Hlawka21.Foundation.ScalarEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
/- Generic confinement adapted from @bwdaugherty, Apache-2.0,
   accepted cutoff-32 submission d5944a03-85b4-4962-b146-4e6c7e7e50c7.
   Original definitions and normalization by Ezzeri Esa. -/
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff21.Failure
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
section Deficit
variable {ι : Type*} [Fintype ι]

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]

theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith

theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)

/-- The envelope hypothesis at `q` confines the normalized total below `q`. -/
theorem normalized_failure_total_lt_q {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    lpNorm p (x + y + z) < q := by
  have hT1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp hK x y z hS hf
  by_contra hn
  have hle : q ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp.le
    (show q ∈ Set.Ico 0 1 from ⟨hq0.le, hq1⟩)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hT1⟩) hle
  linarith

end Deficit

/-- Scaled normalization: singleton norms sum to 3, each at most the total,
and the total is below `3q`. -/
theorem scaled_failure {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    ∃ x y z : Fin 3 → ℝ, hlawkaDeficit p K x y z < 0 ∧
      lpNorm p x + lpNorm p y + lpNorm p z = 3 ∧
      lpNorm p x ≤ lpNorm p (x + y + z) ∧
      lpNorm p y ≤ lpNorm p (x + y + z) ∧
      lpNorm p z ≤ lpNorm p (x + y + z) ∧
      lpNorm p (x + y + z) < 3 * q := by
  have hp0 : 0 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ := exists_normalized_failure hp0 hK x y z hf
  have hT := normalized_failure_total_lt_q hp hK hq0 hq1 henvelope x y z hS hf
  have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
  have hsum : (3 : ℝ) • x + (3 : ℝ) • y + (3 : ℝ) • z = (3 : ℝ) • (x + y + z) := by
    rw [smul_add, smul_add]
  refine ⟨(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp0, h3]
    linarith
  · rw [lpNorm_smul hp0, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, h3]
    linarith


end HlawkaSchatten.DiagonalCutoff21.Failure
