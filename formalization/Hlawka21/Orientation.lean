import Hlawka21.Foundation.Failure
import Hlawka21.NormBasic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Generic coordinate maximum and orientation identities adapted from
   @bwdaugherty's accepted cutoff-32 coarse localization, Apache-2.0,
   submission d5944a03-85b4-4962-b146-4e6c7e7e50c7.
   New signed conflict is parameterized by loss and pair-gap caps. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem lpNorm_le_three_root_mul_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h

theorem inverse_three_root_deficit (p : ℝ) :
    1 - ((3 : ℝ) ^ (1 / p))⁻¹ ≤ Real.log 3 / p := by
  have h := Real.add_one_le_exp (-(Real.log 3 / p))
  have he : ((3 : ℝ) ^ (1 / p))⁻¹ = Real.exp (-(Real.log 3 / p)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  linarith


theorem exists_signed_coord_bound {p m B E : ℝ} (hm : 0 < m) (hp : m ≤ p)
    (hBE : (1099 / (1000 * m)) * B ≤ E) (v : Fin 3 → ℝ) (hv : lpNorm p v ≤ B) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ lpNorm p v - E ≤ s * v i := by
  have hp0 : 0 < p := hm.trans_le hp
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |v i|) Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 v i (fun j ↦ hi j (Finset.mem_univ _))
  set c := ((3 : ℝ) ^ (1 / p))⁻¹ with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hmax' : c * lpNorm p v ≤ |v i| := by
    have hh := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |v i|) = |v i| := by
      rw [hcdef, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rwa [he] at hh
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 1099 / 1000 := by linarith [Real.log_three_lt_d9]
  have hr : 0 ≤ (1099 : ℝ) / (1000 * m) := by positivity
  have he : (1099 : ℝ) / (1000 * m) * m = 1099 / 1000 := by field_simp
  have hlogp : Real.log 3 / p ≤ 1099 / (1000 * m) := by
    rw [div_le_iff₀ hp0]
    have hh := mul_le_mul_of_nonneg_left hp hr
    rw [he] at hh
    linarith
  have hn0 := lpNorm_nonneg p v
  have h1 := mul_le_mul_of_nonneg_right (hd.trans hlogp) hn0
  have h2 := mul_le_mul_of_nonneg_left hv hr
  have hbound : lpNorm p v - |v i| ≤ E := by nlinarith
  by_cases hi0 : 0 ≤ v i
  · rw [abs_of_nonneg hi0] at hbound
    exact ⟨i, 1, Or.inl rfl, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    exact ⟨i, -1, Or.inr rfl, by linarith⟩

theorem signed_conflict_bound {a b c Na Nb Nc P1 P2 T G E s r : ℝ}
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : |a| ≤ Na) (hb : |b| ≤ Nb) (hc : |c| ≤ Nc) (hcol : |a + b + c| ≤ T)
    (h1 : P1 - E ≤ s * a + s * b) (h2 : P2 - E ≤ r * a + r * c)
    (hP1 : Na + Nb - P1 ≤ G) (hP2 : Na + Nc - P2 ≤ G)
    (hNa : G + E < Na) (hS : Na + Nb + Nc = 3) (hT : T < 3 - 2 * (G + E)) :
    False := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hcol' := abs_le.mp hcol
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> linarith

theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _

theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e

theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]


end HlawkaSchatten.DiagonalCutoff21
