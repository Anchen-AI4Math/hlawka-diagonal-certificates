import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Topology.Order.Compact
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window26
import Mathlib.Analysis.Complex.ExponentialBounds
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff21

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction


/- Norm laws from @bwdaugherty's accepted cutoff-32 coarse localization,
   submission d5944a03-85b4-4962-b146-4e6c7e7e50c7, Apache-2.0,
   based on Ezzeri Esa's original coordinate lpNorm definition. -/
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

section Basic
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end Basic

end HlawkaSchatten.DiagonalRealBundle


/- Adapted from @bwdaugherty's accepted cutoff-32 contribution,
   submission d75400b0-5a0e-4167-8192-7fd299469c2e (2026-10-16),
   https://prove2.me/theorems/4e05427b-74d9-4e61-8d14-a52384a5ca10 .
   Public Prove2Me contribution under Apache-2.0; see sources/NOTICE.md.
   These generic lemmas do not assume p >= 32. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

/-- Increments of `x ↦ x ^ p` over intervals of equal length grow to the right. -/
theorem rpow_swap_le {p : ℝ} (hp : 1 ≤ p) {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hc : 0 ≤ c) : (x + c) ^ p + y ^ p ≤ x ^ p + (y + c) ^ p := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ y - x + c by linarith) with h | h
  · have hc0 : c = 0 := by linarith
    have hy : y = x := by linarith
    subst hc0 hy; simp
  · have hconv := (convexOn_rpow hp).2
    have hxm : x ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 hx
    have hym : y + c ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith)
    have hl : 0 ≤ (y - x) / (y - x + c) := div_nonneg (by linarith) h.le
    have hm : 0 ≤ c / (y - x + c) := div_nonneg hc h.le
    have hs : (y - x) / (y - x + c) + c / (y - x + c) = 1 := by
      rw [← add_div, div_self h.ne']
    have h1 := hconv hxm hym hl hm hs
    have h2 := hconv hxm hym hm hl (by linarith)
    simp only [smul_eq_mul] at h1 h2
    have e1 : (y - x) / (y - x + c) * x + c / (y - x + c) * (y + c) = x + c := by
      field_simp; ring
    have e2 : c / (y - x + c) * x + (y - x) / (y - x + c) * (y + c) = y := by
      field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    calc (x + c) ^ p + y ^ p ≤ _ := add_le_add h1 h2
      _ = ((y - x) / (y - x + c) + c / (y - x + c)) * (x ^ p + (y + c) ^ p) := by ring
      _ = _ := by rw [hs, one_mul]

/-- Power mean for two terms. -/
theorem add_rpow_le_two {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ p ≤ 2 ^ p / 2 * (u ^ p + v ^ p) := by
  have h := (convexOn_rpow hp).2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1/2 * u + 1/2 * v = (u + v) / 2 := by ring
  rw [e, Real.div_rpow (by linarith) (by norm_num)] at h
  have h2p : 0 < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  rw [div_le_iff₀ h2p] at h
  calc (u + v) ^ p ≤ _ := h
    _ = _ := by ring

/-- The two-coordinate constant `2 ^ (1 - 1/p)`. -/
noncomputable def cp (p : ℝ) : ℝ := 2 * (1/2 : ℝ) ^ (1/p)

theorem cp_pos (p : ℝ) : 0 < cp p := by unfold cp; positivity

theorem cp_rpow {p : ℝ} (hp : 0 < p) : cp p ^ p = 2 ^ p / 2 := by
  unfold cp
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num),
    one_div_mul_cancel hp.ne', Real.rpow_one]; ring

theorem sum_div_cp_rpow_le {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((u + v) / cp p) ^ p ≤ u ^ p + v ^ p := by
  have hp0 : 0 < p := by linarith
  rw [Real.div_rpow (by linarith) (cp_pos p).le, cp_rpow hp0, div_le_iff₀ (by positivity)]
  rw [mul_comm]; exact add_rpow_le_two hp hu hv

theorem sum_le_cp_mul {p : ℝ} (hp : 1 ≤ p) {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hS : 0 ≤ S) (h : u ^ p + v ^ p ≤ S ^ p) : u + v ≤ cp p * S := by
  have hp0 : 0 < p := by linarith
  have h1 := (sum_div_cp_rpow_le hp hu hv).trans h
  have h2 : (u + v) / cp p ≤ S :=
    (Real.rpow_le_rpow_iff (div_nonneg (by linarith) (cp_pos p).le) hS hp0).1 h1
  rw [div_le_iff₀ (cp_pos p)] at h2; linarith

/-- Diagonal certificate: a row with nearly extremal two-coordinate mass has a small
diagonal entry. -/
theorem diag_cert {p : ℝ} (hp : 1 ≤ p) {a w c N D δ U Ab : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hrow : a ^ p + (w / c) ^ p ≤ N ^ p) (hw : c * N - D ≤ w) (hDc : D / c ≤ δ)
    (hδ : 0 ≤ δ) (hδN : δ ≤ N) (hNU : N ≤ U) (hU : 0 < U) (hAb : 0 ≤ Ab)
    (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p) : a ≤ Ab := by
  have hp0 : 0 < p := by linarith
  have h1 : N - δ ≤ w / c := by
    have e : w / c = N - D / c + (w - (c * N - D)) / c := by field_simp; ring
    rw [e]
    have : 0 ≤ (w - (c * N - D)) / c := div_nonneg (by linarith) hc.le
    linarith
  have h2 : (N - δ) ^ p ≤ (w / c) ^ p := Real.rpow_le_rpow (by linarith) h1 hp0.le
  have h3 := rpow_swap_le hp (x := N - δ) (y := U - δ) (c := δ) (by linarith) (by linarith) hδ
  rw [sub_add_cancel, sub_add_cancel] at h3
  have h4 : U ^ p ≤ Ab ^ p + (U - δ) ^ p := by
    have e : 1 - δ / U = (U - δ) / U := by field_simp
    rw [e, Real.div_rpow hAb hU.le, Real.div_rpow (by linarith) hU.le, ← add_div,
      le_div_iff₀ (by positivity), one_mul] at hcert
    exact hcert
  have h5 : a ^ p ≤ Ab ^ p := by linarith
  exact (Real.rpow_le_rpow_iff ha hAb hp0).1 h5

/-- Two-dimensional Minkowski inequality in power form. -/
theorem mink2 {p : ℝ} (hp : 1 ≤ p) {x1 y1 x2 y2 N1 N2 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (h1 : x1 ^ p + y1 ^ p ≤ N1 ^ p) (h2 : x2 ^ p + y2 ^ p ≤ N2 ^ p) :
    (x1 + x2) ^ p + (y1 + y2) ^ p ≤ (N1 + N2) ^ p := by
  have hp0 : 0 < p := by linarith
  have hM := Real.Lp_add_le (Finset.univ : Finset (Fin 2)) ![x1, y1] ![x2, y2] hp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hM
  rw [abs_of_nonneg (by linarith : 0 ≤ x1 + x2), abs_of_nonneg (by linarith : 0 ≤ y1 + y2),
    abs_of_nonneg hx1, abs_of_nonneg hy1, abs_of_nonneg hx2, abs_of_nonneg hy2] at hM
  have hr1 : (x1 ^ p + y1 ^ p) ^ (1/p) ≤ N1 := by
    calc (x1 ^ p + y1 ^ p) ^ (1/p) ≤ (N1 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = N1 := by rw [one_div, Real.rpow_rpow_inv hN1 hp0.ne']
  have hr2 : (x2 ^ p + y2 ^ p) ^ (1/p) ≤ N2 := by
    calc (x2 ^ p + y2 ^ p) ^ (1/p) ≤ (N2 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ = N2 := by rw [one_div, Real.rpow_rpow_inv hN2 hp0.ne']
  have h3 : ((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p) ≤ N1 + N2 := by linarith
  have hS : 0 ≤ (x1 + x2) ^ p + (y1 + y2) ^ p := by positivity
  calc (x1 + x2) ^ p + (y1 + y2) ^ p
      = (((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p)) ^ p := by
        rw [← Real.rpow_mul hS, one_div_mul_cancel hp0.ne', Real.rpow_one]
    _ ≤ (N1 + N2) ^ p := Real.rpow_le_rpow (by positivity) h3 hp0.le

/-- Ratio lower bound from a convexity certificate. -/
theorem ratio_lower {p x y s τ : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s)
    (hc : 1 < τ ^ p + (s - τ) ^ p) : τ < x := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have h1 := rpow_swap_le hp (x := x) (y := s - τ) (c := τ - x) hx (by linarith) (by linarith)
  have e1 : x + (τ - x) = τ := by ring
  have e2 : s - τ + (τ - x) = s - x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-- Ratio upper bound from a convexity certificate. -/
theorem ratio_upper {p x y s σ : ℝ} (hp : 1 ≤ p) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hc : 1 < σ ^ p + (s - σ) ^ p) : x < σ := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have hx1 : x ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < x ^ p := Real.one_lt_rpow h hp0
    have : 0 ≤ y ^ p := Real.rpow_nonneg hy p
    linarith
  have h1 := rpow_swap_le hp (x := s - x) (y := σ) (c := x - σ) (by linarith) (by linarith)
    (by linarith)
  have e1 : s - x + (x - σ) = s - σ := by ring
  have e2 : σ + (x - σ) = x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-! ## Turning integer-power checks into real-exponent certificates -/

theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'

theorem cert_le {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 ≤ X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 ≤ x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith

theorem cert_lt {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 < X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 < x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith


end HlawkaSchatten.DiagonalRealBundle


/- The contraction rounds of @bwdaugherty's cutoff-32 proof, generalized
   to arbitrary nonnegative singleton sizes and rational output boxes.
   Source: submission d75400b0-5a0e-4167-8192-7fd299469c2e, Apache-2.0.
   Paper Section 4: diagonal/ratio bounds, lower update, upper update,
   and final box. N will be instantiated with the original lpNorm. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

theorem others (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i <;> decide

theorem third {i j : Fin 3} (h : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

structure Facts (p c D δ h A cmax tlo : ℝ) (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ) : Prop where
  Nnonneg : ∀ i, 0 ≤ N i
  hp : 1 ≤ p
  hc : 0 < c
  hcm : c ≤ cmax
  hct : 2 * tlo ≤ c
  hDc : D / c ≤ δ
  hA : 0 < A
  diag : ∀ i, 0 ≤ -X i i
  off : ∀ i j, i ≠ j → 0 ≤ X i j
  nsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    N i + N j + N k = 3
  rowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + X i j ^ p + X i k ^ p = N i ^ p
  row : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + ((X i j + X i k) / c) ^ p ≤ N i ^ p
  wD : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → c * N i - D ≤ X i j + X i k
  wD2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    c * (N j + N k) - D ≤ (X j i + X j k) + (X k i + X k j)
  offsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    6 - h < (X i j + X i k) + (X j i + X j k) + (X k i + X k j)
  T1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i i + X j i + X k i < A
  T2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (X i j + X j j + X k j) + (X i k + X j k + X k k) < cmax * A

section Rounds

variable {p c D δ h A cmax tlo : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N : Fin 3 → ℝ}

theorem ratio_round (F : Facts p c D δ h A cmax tlo X N) {n s τ σ : ℝ}
    (hn : ∀ i, n ≤ N i) (hn0 : 0 < n) (hD0 : 0 ≤ D) (hs : s ≤ 2 * tlo - D / n)
    (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hτc : 1 < τ ^ p + (s - τ) ^ p) (hσc : 1 < σ ^ p + (s - σ) ^ p) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i := by
  intro i j k hij hik hjk
  have hp0 : 0 < p := by linarith [F.hp]
  have hN : 0 < N i := lt_of_lt_of_le hn0 (hn i)
  set Ni := N i with hNdef
  have hbj := F.off i j hij
  have hbk := F.off i k hik
  have hxy : (X i j / Ni) ^ p + (X i k / Ni) ^ p ≤ 1 := by
    rw [Real.div_rpow (by linarith) hN.le, Real.div_rpow (by linarith) hN.le, ← add_div,
      div_le_one (by positivity)]
    have := F.rowfull i j k hij hik hjk
    have := Real.rpow_nonneg (F.diag i) p
    linarith
  have hsum : s ≤ X i j / Ni + X i k / Ni := by
    rw [← add_div, le_div_iff₀ hN]
    have a1 : s * Ni ≤ (2 * tlo - D / n) * Ni := mul_le_mul_of_nonneg_right hs hN.le
    have a2 : D ≤ D / n * Ni := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (hn i) hD0
    have a3 : 2 * tlo * Ni ≤ c * Ni := mul_le_mul_of_nonneg_right F.hct hN.le
    have a4 := F.wD i j k hij hik hjk
    have e : (2 * tlo - D / n) * Ni = 2 * tlo * Ni - D / n * Ni := by ring
    linarith
  have h1 := ratio_lower F.hp (by positivity) (by positivity) hxy hsum hτ0 hτs hτc
  have h2 := ratio_upper F.hp (by positivity) (by positivity) hxy hsum hs1 hσs hσc
  exact ⟨(lt_div_iff₀ hN).1 h1, (div_lt_iff₀ hN).1 h2⟩

theorem lower_round (F : Facts p c D δ h A cmax tlo X N) {n τ n' Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → τ * N i < X i j)
    (hn'0 : 0 < n') (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / n') ^ p + (1 - δ / n') ^ p)
    (hchk : A ≤ τ * (3 - n') - Ab) : ∀ i, n' ≤ N i := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ha := diag_cert F.hp (F.diag i) F.hc (F.row i j k hij hik hjk) (F.wD i j k hij hik hjk)
    F.hDc hδ0 (hδn.trans (hn i)) hlt.le hn'0 hAb hcert
  have t1 := F.T1 i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have ns := F.nsum i j k hij hik hjk
  have m1 : τ * (3 - n') ≤ τ * (N j + N k) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ0
  rw [mul_add] at m1
  linarith

theorem upper_round (F : Facts p c D δ h A cmax tlo X N) {n σ U Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j < σ * N i)
    (hU3 : U < 3) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / (3 - U)) ^ p + (1 - δ / (3 - U)) ^ p)
    (hchk : cmax * A ≤ 6 - h - σ * (3 - U) - Ab) : ∀ i, N i ≤ U := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ns := F.nsum i j k hij hik hjk
  have rj := F.row j i k (Ne.symm hij) hjk hik
  have rk := F.row k i j (Ne.symm hik) (Ne.symm hjk) hij
  have hbji := F.off j i (Ne.symm hij)
  have hbjk := F.off j k hjk
  have hbki := F.off k i (Ne.symm hik)
  have hbkj := F.off k j (Ne.symm hjk)
  have hm := mink2 F.hp (F.diag j) (div_nonneg (by linarith) F.hc.le) (F.diag k)
    (div_nonneg (by linarith) F.hc.le) (F.Nnonneg j) (F.Nnonneg k) rj rk
  rw [← add_div] at hm
  have hNj := hn j
  have hNk := hn k
  have ha := diag_cert F.hp (by linarith [F.diag j, F.diag k]) F.hc hm (F.wD2 i j k hij hik hjk)
    F.hDc hδ0 (by linarith) (by linarith : N j + N k ≤ 3 - U)
    (by linarith) hAb hcert
  have t2 := F.T2 i j k hij hik hjk
  have os := F.offsum i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have m1 : σ * (N j + N k) ≤ σ * (3 - U) :=
    mul_le_mul_of_nonneg_left (by linarith) hσ0
  rw [mul_add] at m1
  linarith

theorem final_round (F : Facts p c D δ h A cmax tlo X N) {n U τ σ Ab ell u v w : ℝ}
    (hn : ∀ i, n ≤ N i) (hU : ∀ i, N i ≤ U) (hδn : δ ≤ n)
    (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i)
    (hU0 : 0 < U) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p)
    (h1 : v ≤ τ * n) (h2 : σ * U ≤ w) (h3 : Ab ≤ u)
    (h4 : ell ≤ τ * (3 - U) - A) : (∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) := by
  intro j i
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    obtain ⟨k, l, hjk, hjl, hkl⟩ := others j
    have ha := diag_cert F.hp (F.diag j) F.hc (F.row j k l hjk hjl hkl)
      (F.wD j k l hjk hjl hkl) F.hDc hδ0 (hδn.trans (hn j)) (hU j) hU0 hAb hcert
    have t1 := F.T1 j k l hjk hjl hkl
    have r1 := (hr k j l (Ne.symm hjk) hkl hjl).1
    have r2 := (hr l j k (Ne.symm hjl) (Ne.symm hkl) hjk).1
    have ns := F.nsum j k l hjk hjl hkl
    have m1 : τ * (3 - U) ≤ τ * (N k + N l) :=
      mul_le_mul_of_nonneg_left (by linarith [hU j]) hτ0
    rw [mul_add] at m1
    constructor <;> linarith
  · rw [if_neg hji]
    obtain ⟨k, hjk, hik⟩ := third hji
    have r := hr j i k hji hjk hik
    have m1 : τ * n ≤ τ * N j := mul_le_mul_of_nonneg_left (hn j) hτ0
    have m2 : σ * N j ≤ σ * U := mul_le_mul_of_nonneg_left (hU j) hσ0
    constructor <;> linarith [r.1, r.2]

end Rounds


end HlawkaSchatten.DiagonalRealBundle



/- Coordinate lemmas adapted from the attributed cutoff-32 implementation;
   original lpNorm definition by Ezzeri Esa, Apache-2.0. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction
abbrev Triple := Fin 3 → Fin 3 → ℝ

theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem offperm (X : Triple) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem lpNorm_nonneg3 (p : ℝ) (x : Fin 3 → ℝ) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_pow3 {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) :
    lpNorm p x ^ p = ∑ l, |x l| ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  simp [Real.norm_eq_abs]

theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]

theorem coord_le {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x i| ≤ lpNorm p x := by
  have h := lpNorm_pow3 hp x
  rw [sum3 _ hij hik hjk] at h
  have : |x i| ^ p ≤ lpNorm p x ^ p := by
    rw [h]; have := Real.rpow_nonneg (abs_nonneg (x j)) p
    have := Real.rpow_nonneg (abs_nonneg (x k)) p; linarith
  exact (Real.rpow_le_rpow_iff (abs_nonneg _) (lpNorm_nonneg3 p x) hp).1 this

theorem two_coord_le {p : ℝ} (hp : 1 ≤ p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x j| + |x k| ≤ cp p * lpNorm p x := by
  have hp0 : 0 < p := by linarith
  have h := lpNorm_pow3 hp0 x
  rw [sum3 _ hij hik hjk] at h
  apply sum_le_cp_mul hp (abs_nonneg _) (abs_nonneg _) (lpNorm_nonneg3 p x)
  rw [h]; have := Real.rpow_nonneg (abs_nonneg (x i)) p; linarith


end HlawkaSchatten.DiagonalRealBundle


/- Residual-budget monotonicity from paper Section 4, with the coefficient
   generalized from the attributed cutoff-32 implementation. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

theorem mono_deficit {c alpha p : ℝ} (hc : 0 < c) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hcrit : 6 * Real.log 2 ≤ 2 / c) :
    6 * (1 / 2 : ℝ) ^ (1 / p) + 2 / (c * p) ≤
      6 * (1 / 2 : ℝ) ^ (1 / alpha) + 2 / (c * alpha) := by
  have hp : 0 < p := ha.trans_le hap
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e (r : ℝ) : (1 / 2 : ℝ) ^ r = Real.exp (-(Real.log 2 * r)) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]
    ring_nf
  rw [e, e]
  have huw : 1 / p ≤ 1 / alpha := one_div_le_one_div_of_le ha hap
  set u := 1 / p with hu_def
  set w := 1 / alpha with hw_def
  set L := Real.log 2
  have h1 : Real.exp (-(L * w)) = Real.exp (-(L * u)) * Real.exp (-(L * (w - u))) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : 1 - L * (w - u) ≤ Real.exp (-(L * (w - u))) := by
    have := Real.add_one_le_exp (-(L * (w - u)))
    linarith
  have h3 : Real.exp (-(L * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have hLu : 0 ≤ L * u := mul_nonneg hL0.le (by positivity)
    linarith)
  have h4 := Real.exp_pos (-(L * u))
  have g1 : 2 / (c * p) = 2 / c * u := by rw [hu_def]; field_simp
  have g2 : 2 / (c * alpha) = 2 / c * w := by rw [hw_def]; field_simp
  rw [g1, g2, h1]
  have hwu : 0 ≤ w - u := sub_nonneg.mpr huw
  have h5 : 0 ≤ (2 / c - 6 * L) * (w - u) :=
    mul_nonneg (sub_nonneg.mpr hcrit) hwu
  have h6 : 0 ≤ 6 * L * (w - u) * (1 - Real.exp (-(L * u))) :=
    mul_nonneg (mul_nonneg (by positivity) hwu) (sub_nonneg.mpr h3)
  have h7 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 6 * Real.exp (-(L * u)) by positivity)
  nlinarith

theorem residual_budget {c alpha p eps D thia W : ℝ}
    (hc : 0 < c) (ha : 0 < alpha) (hap : alpha ≤ p)
    (hcrit : 6 * Real.log 2 ≤ 2 / c)
    (hthia : (1 / 2 : ℝ) ^ (1 / alpha) ≤ thia)
    (hW : 6 - 2 / (c * p) - 3 * eps < W)
    (hD : 2 / (c * alpha) + 3 * eps - 6 * (1 - thia) ≤ D) :
    cp p * 3 - W < D := by
  have hm := mono_deficit hc ha hap hcrit
  unfold cp
  linarith

end HlawkaSchatten.DiagonalRealBundle



/- Normalized norm data imply every premise used by the contraction rounds.
   Adapted from @bwdaugherty's cutoff-32 facts_of; all cutoff, box, gap and
   tail constants are parameters, with the original lpNorm unchanged. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

def coordinateBox (ell u v w : ℝ) (X : Triple) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w

theorem facts_of {p α β tlo thia thib D δ h A c eps ell u v w : ℝ} {X : Triple}
    (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β) (hp1 : 1 ≤ p)
    (hc0 : 0 < c) (hcrit : 6 * Real.log 2 ≤ 2 / c)
    (hell : 0 < ell) (hv : 0 < v) (hA : 0 < A)
    (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthia : (1/2 : ℝ) ^ (1/α) ≤ thia) (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : 2 / (c * α) + 3 * eps - 6 * (1 - thia) ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : 2 / (c * α) + 3 * eps ≤ h)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < A)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / (c * p))
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ (X j i + X k i) + eps) :
    Facts p (cp p) D δ h A (2 * thib) tlo X (fun i ↦ lpNorm p (X i)) := by
  have hp : 1 ≤ p := hp1
  have hp0 : 0 < p := by linarith
  have hdiag : ∀ i, -(u : ℝ) ≤ X i i ∧ X i i ≤ -(ell : ℝ) := fun i ↦ by
    simpa using hB i i
  have hoff : ∀ i j, i ≠ j → (v : ℝ) ≤ X i j ∧ X i j ≤ w := fun i j h ↦ by
    have := hB i j; rwa [if_neg h] at this
  have hrowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + X i j ^ p + X i k ^ p = lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    rw [lpNorm_pow3 hp0, sum3 _ hij hik hjk, abs_of_neg (by linarith [(hdiag i).2]),
      abs_of_pos (by linarith [(hoff i j hij).1]), abs_of_pos (by linarith [(hoff i k hik).1])]
  have hdn : ∀ i, 0 ≤ -X i i := fun i ↦ by linarith [(hdiag i).2]
  have hrow : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + ((X i j + X i k) / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    have := sum_div_cp_rpow_le hp (u := X i j) (v := X i k) (by linarith [(hoff i j hij).1])
      (by linarith [(hoff i k hik).1])
    have := hrowfull i j k hij hik hjk
    linarith
  have hwle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j + X i k ≤ cp p * lpNorm p (X i) := by
    intro i j k hij hik hjk
    apply sum_le_cp_mul hp (by linarith [(hoff i j hij).1]) (by linarith [(hoff i k hik).1])
      (lpNorm_nonneg3 p _)
    have := hrowfull i j k hij hik hjk
    have := Real.rpow_nonneg (hdn i) p
    linarith
  have hoffsum0 : 6 - 2 / (c * p) - 3 * eps <
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    unfold pairGapSum pairGap at hG
    have t01 := htail 2 0 1 (by decide) (by decide) (by decide)
    have t02 := htail 1 0 2 (by decide) (by decide) (by decide)
    have t12 := htail 0 1 2 (by decide) (by decide) (by decide)
    linarith
  have hg : 2 / (c * p) ≤ 2 / (c * α) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hαp hc0.le)
  have hmono := mono_deficit hc0 hα hαp hcrit
  have hct : 2 * tlo ≤ cp p := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/α) ≤ (1/2 : ℝ) ^ (1/p) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hα hαp)
    linarith
  have hcm : cp p ≤ 2 * thib := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/p) ≤ (1/2 : ℝ) ^ (1/β) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hp0 hpβ)
    linarith
  have hnsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X i) + lpNorm p (X j) + lpNorm p (X k) = 3 := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
    rw [Fin.sum_univ_three] at this
    linarith
  have hoffperm : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
        X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    intro i j k hij hik hjk
    exact offperm X hij hik hjk
  have key : cp p * 3 - (X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) < D := by
    unfold cp; linarith
  have hcN : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      cp p * lpNorm p (X i) + cp p * lpNorm p (X j) + cp p * lpNorm p (X k) = cp p * 3 := by
    intro i j k hij hik hjk
    rw [← hnsum i j k hij hik hjk]; ring
  have hcpos := cp_pos p
  set vtotal : Fin 3 → ℝ := X 0 + X 1 + X 2 with hvtotal
  have hvc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → vtotal i = X i i + X j i + X k i := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ X l i) hij hik hjk
    rw [Fin.sum_univ_three] at this
    simp only [hvtotal, Pi.add_apply]
    linarith
  refine ⟨fun i ↦ lpNorm_nonneg3 p (X i), hp, hcpos, hcm, hct, ?_, by linarith, hdn, fun i j h ↦ hv.le.trans (hoff i j h).1, hnsum,
    hrowfull, hrow, ?_, ?_, ?_, ?_, ?_⟩
  · calc D / cp p ≤ D / (2 * tlo) := div_le_div_of_nonneg_left hD0 (by positivity) hct
      _ ≤ δ := hδ
  · intro i j k hij hik hjk
    have := hwle j i k (Ne.symm hij) hjk hik
    have := hwle k i j (Ne.symm hik) (Ne.symm hjk) hij
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have := hwle i j k hij hik hjk
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    rw [mul_add]
    linarith
  · intro i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have h1 := coord_le hp0 vtotal hij hik hjk
    rw [hvc i j k hij hik hjk] at h1
    linarith [le_abs_self (X i i + X j i + X k i)]
  · intro i j k hij hik hjk
    have h1 := two_coord_le hp vtotal hij hik hjk
    rw [hvc j i k (Ne.symm hij) hjk hik, hvc k i j (Ne.symm hik) (Ne.symm hjk) hij] at h1
    have h2 : cp p * lpNorm p vtotal < cp p * (A) := mul_lt_mul_of_pos_left hT hcpos
    have h3 : cp p * (A) ≤ 2 * thib * (A) :=
      mul_le_mul_of_nonneg_right hcm (by linarith)
    have := le_abs_self (X j j + X i j + X k j)
    have := le_abs_self (X k k + X i k + X j k)
    linarith


end HlawkaSchatten.DiagonalRealBundle



/- Pair-tail bounds from Section 3 of the cutoff-21 paper. The finite
   numerical premise is an integer-power rational inequality, not an
   assumption that an external checker succeeded. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

theorem two_tail_norm_bound (m : ℕ) (hm : 1 ≤ m)
    {p S y1 y2 rho cap eps : ℝ}
    (hp : (m : ℝ) ≤ p) (hS : 0 ≤ S) (hScap : S ≤ cap) (hcap : 0 < cap)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (heps : 0 ≤ eps)
    (hy1 : |y1| ≤ rho * S) (hy2 : |y2| ≤ rho * S)
    (hcert : 2 * rho ^ m * cap ≤ (m : ℝ) * eps) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + eps := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 : 1 ≤ p := hm1.trans hp
  have hp0 : 0 < p := by linarith
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · have hzero : S = 0 := hS0.symm
    subst S
    have hy10 : y1 = 0 := abs_nonpos_iff.mp (by simpa using hy1)
    have hy20 : y2 = 0 := abs_nonpos_iff.mp (by simpa using hy2)
    subst y1 y2
    simpa [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')] using heps
  · rw [abs_of_pos hSpos]
    have hpow : rho ^ p ≤ rho ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hrho hrho1 (by positivity) hp
    have hy (y : ℝ) (hy : |y| ≤ rho * S) :
        |y| ^ p ≤ rho ^ m * S ^ p := by
      calc
        _ ≤ (rho * S) ^ p := Real.rpow_le_rpow (abs_nonneg _) hy hp0.le
        _ = rho ^ p * S ^ p := Real.mul_rpow hrho hSpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
    have hnum : 2 * rho ^ m ≤ p * (eps / S) := by
      have h1 : 2 * rho ^ m ≤ (m : ℝ) * eps / cap := (le_div_iff₀ hcap).2 hcert
      have h2 : eps / cap ≤ eps / S := div_le_div_of_nonneg_left heps hSpos hScap
      have h3 := mul_le_mul hp h2 (div_nonneg heps hcap.le) (by positivity : (0 : ℝ) ≤ p)
      calc
        _ ≤ (m : ℝ) * eps / cap := h1
        _ = (m : ℝ) * (eps / cap) := by ring
        _ ≤ p * (eps / S) := h3
    have hbern : 1 + p * (eps / S) ≤ (1 + eps / S) ^ p :=
      one_add_mul_self_le_rpow_one_add (by have := div_nonneg heps hSpos.le; linarith) hp1
    have heq : (S + eps) ^ p = S ^ p * (1 + eps / S) ^ p := by
      rw [← Real.mul_rpow hSpos.le (by positivity)]
      congr 1
      field_simp
    have h1 := hy y1 hy1
    have h2 := hy y2 hy2
    have h3 := mul_le_mul_of_nonneg_right hnum (show 0 ≤ S ^ p by positivity)
    have h4 := mul_le_mul_of_nonneg_left hbern (show 0 ≤ S ^ p by positivity)
    have hsum : S ^ p + |y1| ^ p + |y2| ^ p ≤ (S + eps) ^ p := by
      rw [heq]
      nlinarith
    calc
      _ ≤ ((S + eps) ^ p) ^ (1 / p) := Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ = S + eps := by rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne']

theorem half_tail21 {p S y1 y2 : ℝ} (hp : 21 ≤ p)
    (hS : 0 ≤ S) (hS3 : S ≤ 3) (hy1 : |y1| ≤ S / 2) (hy2 : |y2| ≤ S / 2) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000 := by
  apply two_tail_norm_bound 21 (by norm_num) hp hS hS3 (by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem refined_tail21 {p S y1 y2 : ℝ} (hp : 21 ≤ p)
    (hS : 349 / 250 ≤ S) (hS3 : S ≤ 3)
    (hy1 : |y1| ≤ 129 / 250) (hy2 : |y2| ≤ 129 / 250) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000000 := by
  apply two_tail_norm_bound 21 (by norm_num) hp (by linarith) hS3 (by norm_num)
    (show (0 : ℝ) ≤ 129 / 349 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem refined_tail26 {p S y1 y2 : ℝ} (hp : 26 ≤ p)
    (hS : 3 / 2 ≤ S) (hS3 : S ≤ 3)
    (hy1 : |y1| ≤ 353 / 500) (hy2 : |y2| ≤ 353 / 500) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000000 := by
  apply two_tail_norm_bound 26 (by norm_num) hp (by linarith) hS3 (by norm_num)
    (show (0 : ℝ) ≤ 353 / 750 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem clip_pair_tail {ell u v w A diagonal off total excluded y : ℝ}
    (hd : -u ≤ diagonal ∧ diagonal ≤ -ell) (ho : v ≤ off ∧ off ≤ w)
    (hV : total ≤ A) (hx : v ≤ excluded)
    (hpair : y = diagonal + off) (hclip : y = total - excluded) :
    v - u ≤ y ∧ y ≤ min (w - ell) (A - v) := by
  constructor
  · linarith [hd.1, ho.1]
  · apply le_min <;> linarith [hd.2, ho.2]

end HlawkaSchatten.DiagonalRealBundle



/- Paper Section 3.2: the actual pair norm, rather than an independent
   scalar surrogate, has a uniformly small non-main contribution. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem total_coordinate_perm {p A : ℝ} (hp : 1 ≤ p) (X : Triple)
    (hT : lpNorm p (X 0 + X 1 + X 2) ≤ A)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : Fin 3) :
    X i r + X j r + X k r ≤ A := by
  have hc := norm_apply_le_lpNorm hp (X 0 + X 1 + X 2) r
  simp only [Pi.add_apply, Real.norm_eq_abs] at hc
  have hs := sum3 (fun l ↦ X l r) hij hik hjk
  rw [Fin.sum_univ_three] at hs
  linarith [le_abs_self (X 0 r + X 1 r + X 2 r)]

theorem refined_pair_tail21 {p : ℝ} (hp : 21 ≤ p) (X : Triple)
    (hB : coordinateBox (189/500) (607/500) (349/500) (607/500) X)
    (hT : lpNorm p (X 0 + X 1 + X 2) ≤ 3033/2500) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + 1/100000000 := by
  have hp1 : 1 ≤ p := by linarith
  have hd (i : Fin 3) : -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ) := by
    simpa [coordinateBox] using hB i i
  have ho (j i : Fin 3) (hji : j ≠ i) : (349/500 : ℝ) ≤ X j i ∧ X j i ≤ 607/500 := by
    simpa [coordinateBox, hji] using hB j i
  intro i j k hij hik hjk
  have hji := ho j i hij.symm
  have hki := ho k i hik.symm
  have hkj := ho k j hjk.symm
  have hjk' := ho j k hjk
  have hij' := ho i j hij
  have hik' := ho i k hik
  have hvj := total_coordinate_perm hp1 X hT hij hik hjk j
  have hvk := total_coordinate_perm hp1 X hT hij hik hjk k
  have hj := hd j
  have hk := hd k
  rw [lpNorm_eq3 p _ hij hik hjk]
  simp only [Pi.add_apply]
  apply refined_tail21 hp (by linarith) (by linarith)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem refined_pair_tail26 {p : ℝ} (hp : 26 ≤ p) (X : Triple)
    (hB : coordinateBox (477/1000) (1183/1000) (3/4) (1183/1000) X) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + 1/100000000 := by
  have hd (i : Fin 3) : -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ) := by
    simpa [coordinateBox] using hB i i
  have ho (j i : Fin 3) (hji : j ≠ i) : (3/4 : ℝ) ≤ X j i ∧ X j i ≤ 1183/1000 := by
    simpa [coordinateBox, hji] using hB j i
  intro i j k hij hik hjk
  have hji := ho j i hij.symm
  have hki := ho k i hik.symm
  have hkj := ho k j hjk.symm
  have hjk' := ho j k hjk
  have hj := hd j
  have hk := hd k
  rw [lpNorm_eq3 p _ hij hik hjk]
  simp only [Pi.add_apply]
  apply refined_tail26 hp (by linarith) (by linarith)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem initial_norm_lower {p ell u v w : ℝ} (hp : 1 ≤ p) (X : Triple)
    (hB : coordinateBox ell u v w X) : ∀ i, v ≤ lpNorm p (X i) := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  have hx : v ≤ X i j := by
    have h : v ≤ X i j ∧ X i j ≤ w := by simpa [coordinateBox, hij] using hB i j
    exact h.1
  have hc := norm_apply_le_lpNorm hp (X i) j
  rw [Real.norm_eq_abs] at hc
  exact hx.trans ((le_abs_self _).trans hc)

end HlawkaSchatten.DiagonalRealBundle



/- The linear pair and offsum floors retained in the convex domain.
   They follow from the original norms, not from independent certificates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem pairGapSum_perm (p : ℝ) (X : Triple) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pairGapSum (lpNorm p) (X i) (X j) (X k) =
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) := by
  have h10 : lpNorm p (X 1 + X 0) = lpNorm p (X 0 + X 1) := by rw [add_comm]
  have h20 : lpNorm p (X 2 + X 0) = lpNorm p (X 0 + X 2) := by rw [add_comm]
  have h21 : lpNorm p (X 2 + X 1) = lpNorm p (X 1 + X 2) := by rw [add_comm]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  all_goals simp only [pairGapSum, pairGap, h10, h20, h21]; ring

theorem pair_floor_of_norm_data {p a c U eps : ℝ} (hp : 1 ≤ p)
    (ha : 0 < a) (hap : a ≤ p) (hc : 0 < c) (X : Triple)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hU : ∀ i, lpNorm p (X i) ≤ U)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / (c * p))
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + eps) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      3 - U - 2 / (c * a) - eps ≤ X j i + X k i := by
  intro i j k hij hik hjk
  have hperm := pairGapSum_perm p X hij hik hjk
  have hg := hG
  rw [← hperm] at hg
  have h1 := pairGap_nonneg hp (X i) (X j)
  have h2 := pairGap_nonneg hp (X i) (X k)
  have hsum := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
  rw [Fin.sum_univ_three] at hsum
  have hratio : 2 / (c * p) ≤ 2 / (c * a) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hap hc.le)
  have ht := htail i j k hij hik hjk
  have hi := hU i
  dsimp only [pairGapSum, pairGap] at hg h1 h2
  linarith

end HlawkaSchatten.DiagonalRealBundle



/- The convex domain retains norm caps and the derived linear floors.
   Normalization S=3 is deliberately absent: it is only used to place an
   actual counterexample in this domain before the averaging argument. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

def offsum (X : Triple) : ℝ :=
  X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1

def normCappedDomain (p ell u v w U A J W0 : ℝ) : Set Triple :=
  {X | coordinateBox ell u v w X ∧
    (∀ i, lpNorm p (X i) ≤ U) ∧ lpNorm p (X 0 + X 1 + X 2) ≤ A ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → J ≤ X j i + X k i) ∧
    W0 ≤ offsum X}

theorem coordinateBox_convex (ell u v w : ℝ) :
    Convex ℝ {X : Triple | coordinateBox ell u v w X} := by
  intro X hX Y hY a b ha hb hab j i
  have hx := hX j i
  have hy := hY j i
  by_cases hji : j = i
  · rw [if_pos hji] at hx hy ⊢
    have hh := (convex_Icc (-u) (-ell)) hx hy ha hb hab
    simpa only [Set.mem_Icc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  · rw [if_neg hji] at hx hy ⊢
    have hh := (convex_Icc v w) hx hy ha hb hab
    simpa only [Set.mem_Icc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh

theorem norm_cap_convex_combination {p U a b : ℝ} (hp : 1 ≤ p)
    (x y : Fin 3 → ℝ) (hx : lpNorm p x ≤ U) (hy : lpNorm p y ≤ U)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    lpNorm p (a • x + b • y) ≤ U := by
  have hh := (convexOn_lpNorm (ι := Fin 3) (E := ℝ) hp).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hh
  calc
    _ ≤ a * lpNorm p x + b * lpNorm p y := hh
    _ ≤ a * U + b * U := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = U := by rw [← add_mul, hab, one_mul]

theorem normCappedDomain_convex {p : ℝ} (hp : 1 ≤ p) (ell u v w U A J W0 : ℝ) :
    Convex ℝ (normCappedDomain p ell u v w U A J W0) := by
  intro X hX Y hY a b ha hb hab
  rcases hX with ⟨hBX, hNX, hTX, hJX, hWX⟩
  rcases hY with ⟨hBY, hNY, hTY, hJY, hWY⟩
  refine ⟨coordinateBox_convex ell u v w hBX hBY ha hb hab, ?_, ?_, ?_, ?_⟩
  · intro i
    exact norm_cap_convex_combination hp (X i) (Y i) (hNX i) (hNY i) ha hb hab
  · have he : (a • X + b • Y) 0 + (a • X + b • Y) 1 + (a • X + b • Y) 2 =
        a • (X 0 + X 1 + X 2) + b • (Y 0 + Y 1 + Y 2) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    exact norm_cap_convex_combination hp _ _ hTX hTY ha hb hab
  · intro i j k hij hik hjk
    have hx := hJX i j k hij hik hjk
    have hy := hJY i j k hij hik hjk
    have hh := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun r : ℝ ↦ r * J) hab]
  · have he : offsum (a • X + b • Y) = a * offsum X + b * offsum Y := by
      simp only [offsum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    have hh := add_le_add (mul_le_mul_of_nonneg_left hWX ha)
      (mul_le_mul_of_nonneg_left hWY hb)
    nlinarith [congrArg (fun r : ℝ ↦ r * W0) hab]

end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem normDomain_of_localized {p ell u v w U A J W0 ell' u' v' w' U' J' W' : ℝ}
    (X : Triple) (hN : ∀ i, lpNorm p (X i) ≤ U')
    (hB : coordinateBox ell' u' v' w' X)
    (hT : lpNorm p (X 0 + X 1 + X 2) < A)
    (hJ : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → J' ≤ X j i + X k i)
    (hW : W' < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (hell : ell ≤ ell') (hu : u' ≤ u) (hv : v ≤ v') (hw : w' ≤ w)
    (hU : U' ≤ U) (hJJ : J ≤ J') (hWW : W0 ≤ W') :
    X ∈ normCappedDomain p ell u v w U A J W0 := by
  refine ⟨?_, fun i ↦ (hN i).trans hU, hT.le, ?_, ?_⟩
  · intro j i
    have hh := hB j i
    by_cases hji : j = i
    · rw [if_pos hji] at hh ⊢
      constructor <;> linarith
    · rw [if_neg hji] at hh ⊢
      constructor <;> linarith
  · intro i j k hij hik hjk
    exact hJJ.trans (hJ i j k hij hik hjk)
  · exact hWW.trans hW.le

end HlawkaSchatten.DiagonalRealBundle

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Directional second derivatives of the finite real coordinate norm -/

set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The power sum is nonneg. -/
theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p

/-- The power sum equals the `p`-norm raised to `p`. -/
theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl

/-- The power sum is strictly positive for nonzero `v`. -/
theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in
private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]

/-- The quadratic form at `h = v` equals the power sum. -/
theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)

/-- The power residual decomposes into radial and tangential parts. -/
theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The optimal radial coefficient minimizes the residual. -/
theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

/-- The residual at the optimal coefficient is minimal. -/
theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]

/-- The power residual is nonneg. -/
theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))

/-- The norm Hessian is nonneg for `p ≥ 1`. -/
theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)

/-- The norm Hessian is bounded by the power residual. -/
theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))

omit [Fintype ι] in
private theorem hasDerivAt_abs_power_slope {p : ℝ} (hp : 4 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ (p - 2) * x) ((p - 1) * |x| ^ (p - 2)) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).mul (hasDerivAt_id x)
  have heq : ((p - 2) * |x| ^ (p - 2 - 2) * x) * x + |x| ^ (p - 2) * 1 =
      (p - 1) * |x| ^ (p - 2) := by
    have hh := abs_rpow_mul_sq (by linarith : 0 < p - 2 - 2) x
    have hcancel : p - 2 - 2 + 2 = p - 2 := by ring
    rw [hcancel] at hh
    nlinarith
  convert! h using 1
  simpa only [id_eq] using heq.symm

/-- Differentiability of the power sum along a line. -/
theorem hasDerivAt_powerSum_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerSum p (v + s • h))
      (p * powerPair p (v + t • h) h) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ ↦ |v i + s * h i| ^ p)
      (p * |v i + t * h i| ^ (p - 2) * (v i + t * h i) * h i) t := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hasDerivAt_abs_rpow _ hp).comp t (((hasDerivAt_id t).mul_const (h i)).const_add (v i))
  simpa only [powerSum, powerPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

/-- Differentiability of the first-order form along a line. -/
theorem hasDerivAt_powerPair_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerPair p (v + s • h) h)
      ((p - 1) * powerQuad p (v + t • h) h) t := by
  have hi (i : ι) := ((hasDerivAt_abs_power_slope hp (v i + t * h i)).comp t
    (((hasDerivAt_id t).mul_const (h i)).const_add (v i))).mul_const (h i)
  simpa only [powerPair, powerQuad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    pow_two, mul_assoc, Function.comp_def, id_eq, one_mul] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

/-- Differentiability of the `p`-norm along a line. -/
theorem hasDerivAt_lpNorm_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ lpNorm p (v + s • h)) (normSlope p (v + t • h) h) t := by
  have hp0 := zero_lt_one.trans hp
  have hh := (hasDerivAt_powerSum_line hp v h t).rpow_const (p := 1 / p)
    (Or.inl (powerSum_pos hp0 hv).ne')
  have he : p * powerPair p (v + t • h) h * (1 / p) * powerSum p (v + t • h) ^ (1 / p - 1) =
      normSlope p (v + t • h) h := by
    unfold normSlope
    field_simp
  convert hh using 1
  · rfl
  · exact he.symm

/-- Differentiability of the norm slope along a line. -/
theorem hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by
  have hp0 : 0 < p := by linarith
  have hS := powerSum_pos hp0 hv
  have hh := ((hasDerivAt_powerSum_line (by linarith) v h t).rpow_const (p := 1 / p - 1)
    (Or.inl hS.ne')).mul (hasDerivAt_powerPair_line hp v h t)
  have hpow : powerSum p (v + t • h) ^ (1 / p - 1 - 1) =
      powerSum p (v + t • h) ^ (1 / p - 1) / powerSum p (v + t • h) := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have he : (p * powerPair p (v + t • h) h * (1 / p - 1) *
      powerSum p (v + t • h) ^ (1 / p - 1 - 1)) * powerPair p (v + t • h) h +
      powerSum p (v + t • h) ^ (1 / p - 1) * ((p - 1) * powerQuad p (v + t • h) h) =
        normHessian p (v + t • h) h := by
    rw [normHessian, powerResidual_radial (by linarith) _ _ hv, hpow]
    field_simp
    ring
  rwa [he] at hh

/-- The first-order form with a radial correction. -/
theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The norm Hessian with a radial correction. -/
theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

/-- The `(p-1)/p`-th power of the power sum root. -/
theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]

/-- The norm Hessian as a ratio of quadratic form to power sum. -/
theorem normHessian_eq_div {p : ℝ} (hp : 0 < p) (v h : ι → ℝ) :
    normHessian p v h = (p - 1) / lpNorm p v ^ (p - 1) *
      powerResidual p v h (radialCoefficient p v h) := by
  rw [normHessian, powerSum_root_pred hp]
  rfl

end HlawkaSchatten.DiagonalConstruction

/- The cap-based lower coefficient is the one used in the new convex domain.
   The generic canceled pair upper bound is adapted from @bwdaugherty's
   accepted cutoff-32 submission 9194204b-0072-43c0-8df1-f8fce4b9c5ef,
   Apache-2.0; original norm/Hessian definitions by Ezzeri Esa. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)

theorem normHessian_lower_norm_cap {p : ℝ} (hp : 2 < p)
    (v h : Fin 3 → ℝ) (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hlo : ∀ i, m ≤ |v i|) (hcap : lpNorm p v ≤ U) :
    ((p - 1) * m ^ (p - 2) / U ^ (p - 1)) *
      euclideanSq (h - radialCoefficient p v h • v) ≤ normHessian p v h := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hv : v ≠ 0 := by
    intro he
    have hh := hlo 0
    simp only [he, Pi.zero_apply, abs_zero] at hh
    linarith
  have hN := lpNorm_pos hp0 hv
  have hden : lpNorm p v ^ (p - 1) ≤ U ^ (p - 1) :=
    Real.rpow_le_rpow hN.le hcap (by linarith)
  have hweight : m ^ (p - 2) * euclideanSq (h - radialCoefficient p v h • v) ≤
      powerResidual p v h (radialCoefficient p v h) := by
    simp only [euclideanSq, powerResidual, Finset.mul_sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm.le (hlo i) (by linarith)) (sq_nonneg _)
  have hcoef : (p - 1) * m ^ (p - 2) / U ^ (p - 1) ≤
      ((p - 1) / lpNorm p v ^ (p - 1)) * m ^ (p - 2) := by
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ (p - 1) * m ^ (p - 2) by positivity)
      (Real.rpow_pos_of_pos hN _) hden
    calc
      _ ≤ ((p - 1) * m ^ (p - 2)) / lpNorm p v ^ (p - 1) := hh
      _ = _ := by ring
  rw [normHessian_eq_div hp0]
  calc
    _ ≤ (((p - 1) / lpNorm p v ^ (p - 1)) * m ^ (p - 2)) *
        euclideanSq (h - radialCoefficient p v h • v) :=
      mul_le_mul_of_nonneg_right hcoef (euclideanSq_nonneg _)
    _ = ((p - 1) / lpNorm p v ^ (p - 1)) *
        (m ^ (p - 2) * euclideanSq (h - radialCoefficient p v h • v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)

theorem normHessian_upper_canceled {p : ℝ} (hp : 2 < p)
    (v h : Fin 3 → ℝ) (k : Fin 3) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hk : m ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ M) :
    normHessian p v h ≤
      ((p - 1) * M ^ (p - 2) / m ^ (p - 1)) *
        (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hkv : v k ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hk
    linarith
  have hv : v ≠ 0 := by intro he; apply hkv; simp [he]
  have hN := lpNorm_pos hp0 hv
  have hlarge : m ≤ lpNorm p v := hk.trans (norm_apply_le_lpNorm (by linarith) v k)
  have hden : m ^ (p - 1) ≤ lpNorm p v ^ (p - 1) :=
    Real.rpow_le_rpow hm.le hlarge (by linarith)
  have hres : powerResidual p v h (h k / v k) ≤
      M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
    have hz : |v k| ^ (p - 2) * (h k - h k / v k * v k) ^ 2 = 0 := by
      simp [div_mul_cancel₀ _ hkv]
    rw [powerResidual, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hz, add_zero,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi'
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (hi i (Finset.mem_erase.mp hi').1) (by linarith))
      (sq_nonneg _)
  have hcoef : (p - 1) / lpNorm p v ^ (p - 1) ≤ (p - 1) / m ^ (p - 1) :=
    div_le_div_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hm _) hden
  have hmin := normHessian_le_residual hp v h hv (h k / v k)
  rw [powerSum_root_pred hp0] at hmin
  change normHessian p v h ≤
    (p - 1) / lpNorm p v ^ (p - 1) * powerResidual p v h (h k / v k) at hmin
  calc
    _ ≤ _ := hmin
    _ ≤ ((p - 1) / lpNorm p v ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ((p - 1) / m ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Real.rpow_nonneg hM _)
        (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
    _ = _ := by ring

end HlawkaSchatten.DiagonalRealBundle


/- Parameterized two-coordinate geometry for the norm-constrained domain.
   The separating cross expression is the generic cutoff-32 argument of
   @bwdaugherty (Apache-2.0). Bounds use each slab's actual total-coordinate
   interval, rather than the old fixed cutoff-32 box constants. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem total_pair_shape_interval (s t x y : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hxlo : s ≤ x) (hxhi : x ≤ t) (hylo : s ≤ y) (hyhi : y ≤ t) :
    (x ^ 2 + y ^ 2) * (s + t) ^ 2 ≤ (s ^ 2 + t ^ 2) * (x + y) ^ 2 := by
  have ht : 0 ≤ t := hs.le.trans hst
  have ha : 0 ≤ t * x - s * y := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hxlo),
      mul_nonneg hs.le (sub_nonneg.mpr hyhi)]
  have hb : 0 ≤ t * y - s * x := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hylo),
      mul_nonneg hs.le (sub_nonneg.mpr hxhi)]
  nlinarith [mul_nonneg ha hb]

theorem spread_from_residual_interval (m s t x y r0 r1 gap : ℝ)
    (hm : 0 < m) (hs : 0 < s) (hst : s ≤ t)
    (hxlo : s ≤ x) (hxhi : x ≤ t) (hylo : s ≤ y) (hyhi : y ≤ t)
    (hgap : 0 ≤ gap) (hsep : m * (x + y) * gap ≤ x * r1 - y * r0) :
    gap ^ 2 ≤ ((s ^ 2 + t ^ 2) / (m ^ 2 * (s + t) ^ 2)) * (r0 ^ 2 + r1 ^ 2) := by
  have hxy : 0 < x + y := by linarith
  have hst0 : 0 < s + t := by linarith
  have hleft : 0 ≤ m * (x + y) * gap := by positivity
  have hsquare := mul_self_le_mul_self hleft hsep
  have hcauchy : (x * r1 - y * r0) ^ 2 ≤ (x ^ 2 + y ^ 2) * (r0 ^ 2 + r1 ^ 2) := by
    nlinarith [sq_nonneg (x * r0 + y * r1)]
  have hshape := total_pair_shape_interval s t x y hs hst hxlo hxhi hylo hyhi
  have hweight := mul_le_mul_of_nonneg_right hshape (show 0 ≤ r0 ^ 2 + r1 ^ 2 by positivity)
  have hdiv : (m ^ 2 * (s + t) ^ 2) * ((s ^ 2 + t ^ 2) / (m ^ 2 * (s + t) ^ 2)) =
      s ^ 2 + t ^ 2 := mul_div_cancel₀ _ (by positivity)
  apply (mul_le_mul_iff_right₀ (show 0 < m ^ 2 * (x + y) ^ 2 by positivity)).mp
  have hbound : (x ^ 2 + y ^ 2) ≤
      ((s ^ 2 + t ^ 2) / (m ^ 2 * (s + t) ^ 2)) * (m ^ 2 * (x + y) ^ 2) := by
    apply (mul_le_mul_iff_right₀ (show 0 < (s + t) ^ 2 by positivity)).mp
    have he : (s + t) ^ 2 *
        (((s ^ 2 + t ^ 2) / (m ^ 2 * (s + t) ^ 2)) * (m ^ 2 * (x + y) ^ 2)) =
        (s ^ 2 + t ^ 2) * (x + y) ^ 2 := by
      field_simp [hm.ne', hst0.ne']
    rw [he]
    nlinarith only [hshape]
  have hh := mul_le_mul_of_nonneg_right hbound (show 0 ≤ r0 ^ 2 + r1 ^ 2 by positivity)
  nlinarith

theorem young_square (eps x y : ℝ) (heps : 0 < eps) :
    (x + y) ^ 2 ≤ (1 + eps) * x ^ 2 + (1 + 1 / eps) * y ^ 2 := by
  have hmul : eps * (1 / eps) = 1 := by field_simp
  have hh := sq_nonneg (eps * x - y)
  apply (mul_le_mul_iff_right₀ heps).mp
  nlinarith [congrArg (fun z : ℝ ↦ z * y ^ 2) hmul]

end HlawkaSchatten.DiagonalRealBundle


/- Generic separating cross expression and finite three-coordinate identities
   adapted from @bwdaugherty's accepted cutoff-32 convex-box proof,
   Apache-2.0. The spread estimate below uses explicit interval and Young
   parameters, with no cutoff-32 box assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction
theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)


theorem euclideanSq_add_le (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (u i - v i)]


theorem euclideanSq_neg (v : Fin 3 → ℝ) : euclideanSq (-v) = euclideanSq v := by
  simp [euclideanSq]


theorem euclideanSq_sub_le (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simpa only [sub_eq_add_neg, euclideanSq_neg] using euclideanSq_add_le u (-v)


theorem euclideanSq_smul (a : ℝ) (v : Fin 3 → ℝ) :
    euclideanSq (a • v) = a ^ 2 * euclideanSq v := by
  simp only [euclideanSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]


theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]


theorem extreme_pair_separation
    (m t0 t1 x00 x10 x20 x01 x11 x21 a0 a1 a2 : ℝ)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1)
    (hrow0 : t0 = x00 + x10 + x20)
    (hrow1 : t1 = x01 + x11 + x21)
    (h00 : x00 ≤ -m) (h11 : x11 ≤ -m)
    (h10 : m ≤ x10) (h01 : m ≤ x01)
    (ha1 : a1 ≤ a2) (ha0 : a2 ≤ a0) :
    m * (t0 + t1) * (a0 - a1) ≤
      t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) := by
  have hgap : 0 ≤ a0 - a1 := by linarith
  by_cases hc : 0 ≤ t0 * x21 - t1 * x20
  · have hbase : m * (t0 + t1) ≤ t0 * x01 - t1 * x00 := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h01),
        mul_nonneg ht1 (show 0 ≤ -x00 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc (sub_nonneg.mpr ha1)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t0 * x01 - t1 * x00) * (a0 - a1) +
          (t0 * x21 - t1 * x20) * (a2 - a1) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith
  · have hc' : 0 ≤ -(t0 * x21 - t1 * x20) := by linarith
    have hbase : m * (t0 + t1) ≤ t1 * x10 - t0 * x11 := by
      nlinarith [mul_nonneg ht1 (sub_nonneg.mpr h10),
        mul_nonneg ht0 (show 0 ≤ -x11 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc' (sub_nonneg.mpr ha0)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t1 * x10 - t0 * x11) * (a0 - a1) -
          (t0 * x21 - t1 * x20) * (a0 - a2) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith

theorem ordered_pair_difference_sum (a b c : ℝ) (h1 : b ≤ c) (h2 : c ≤ a) :
    (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 ≤ 2 * (a - b) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

def pairLeft : Fin 3 → Fin 3 := ![1, 0, 0]
def pairRight : Fin 3 → Fin 3 := ![2, 2, 1]
def pairDifference (a : Fin 3 → ℝ) : Fin 3 → ℝ := fun j ↦ a (pairLeft j) - a (pairRight j)

theorem pairTriple_eq_indices (X : Triple) (j : Fin 3) :
    pairTriple X j = X (pairLeft j) + X (pairRight j) := by
  fin_cases j <;> rfl

theorem sum_three_distinct (v : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ i, v i) = v j + v k + v l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [Fin.sum_univ_three] <;> ring

theorem exists_ordered_indices (a : Fin 3 → ℝ) :
    ∃ j k l : Fin 3, j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ a k ≤ a l ∧ a l ≤ a j := by
  by_cases h01 : a 0 ≤ a 1
  · by_cases h12 : a 1 ≤ a 2
    · exact ⟨2, 0, 1, by decide, by decide, by decide, h01, h12⟩
    · by_cases h02 : a 0 ≤ a 2
      · exact ⟨1, 0, 2, by decide, by decide, by decide, h02, le_of_not_ge h12⟩
      · exact ⟨1, 2, 0, by decide, by decide, by decide, le_of_not_ge h02, h01⟩
  · by_cases h02 : a 0 ≤ a 2
    · exact ⟨2, 1, 0, by decide, by decide, by decide, le_of_not_ge h01, h02⟩
    · by_cases h12 : a 1 ≤ a 2
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h12, le_of_not_ge h02⟩
      · exact ⟨0, 2, 1, by decide, by decide, by decide, le_of_not_ge h12, le_of_not_ge h01⟩

theorem pair_difference_ordered (a : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 * (a j - a k) ^ 2 := by
  have hs : (∑ i, pairDifference a i ^ 2) =
      (a j - a k) ^ 2 + (a j - a l) ^ 2 + (a k - a l) ^ 2 := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [pairDifference, pairLeft, pairRight, Fin.sum_univ_three] <;> ring
  rw [hs]
  exact ordered_pair_difference_sum _ _ _ hlo hhi

theorem two_coordinates_sq_le (v : Fin 3 → ℝ) (j k : Fin 3) (hjk : j ≠ k) :
    v j ^ 2 + v k ^ 2 ≤ euclideanSq v := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s := {j, k}) (t := Finset.univ) (f := fun i ↦ v i ^ 2)
    (Finset.subset_univ _) (fun i _ _ ↦ sq_nonneg _)
  simpa [euclideanSq, Finset.sum_pair hjk] using h


theorem ordered_spread_interval {X : Triple} (m s t eps : ℝ)
    (hm : 0 < m) (hs : 0 < s) (hst : s ≤ t) (heps : 0 < eps)
    (hdiag : ∀ i, X i i ≤ -m) (hoff : ∀ j i, j ≠ i → m ≤ X j i)
    (htotal : ∀ i, s ≤ totalTriple X i ∧ totalTriple X i ≤ t)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X)
    (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (a j - a k) ^ 2 ≤ ((s ^ 2 + t ^ 2) / (m ^ 2 * (s + t) ^ 2)) *
      ((1 + eps) * euclideanSq D + 3 * (1 + 1/eps) * frobeniusSq U) := by
  have htj := htotal j
  have htk := htotal k
  have hsep := extreme_pair_separation m (totalTriple X j) (totalTriple X k)
    (X j j) (X k j) (X l j) (X j k) (X k k) (X l k) (a j) (a k) (a l)
    (by linarith) (by linarith)
    (sum_three_distinct (fun i ↦ X i j) j k l hjk hjl hkl)
    (sum_three_distinct (fun i ↦ X i k) j k l hjk hjl hkl)
    (hdiag j) (hdiag k) (hoff k j hjk.symm) (hoff j k hjk) hlo hhi
  have happly (i : Fin 3) : applyTriple X a i = X j i * a j + X k i * a k + X l i * a l := by
    rw [applyTriple, sum_three_distinct _ j k l hjk hjl hkl]
    ring
  have hcross : totalTriple X j * (D k - totalTriple U k) -
      totalTriple X k * (D j - totalTriple U j) =
      totalTriple X j * (X j k * a j + X k k * a k + X l k * a l) -
      totalTriple X k * (X j j * a j + X k j * a k + X l j * a l) := by
    rw [hD]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, happly]
    ring
  have hspread := spread_from_residual_interval m s t (totalTriple X j) (totalTriple X k)
    (D j - totalTriple U j) (D k - totalTriple U k) (a j - a k)
    hm hs hst htj.1 htj.2 htk.1 htk.2 (by linarith) (by rw [hcross]; exact hsep)
  have h0 := young_square eps (D j) (-totalTriple U j) heps
  have h1 := young_square eps (D k) (-totalTriple U k) heps
  have hd := two_coordinates_sq_le D j k hjk
  have hu := two_coordinates_sq_le (totalTriple U) j k hjk
  have hut := euclideanSq_total_le U
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 1 + eps by positivity)
  have hu' := mul_le_mul_of_nonneg_left (hu.trans hut) (show 0 ≤ 1 + 1/eps by positivity)
  have hsum : (D j - totalTriple U j) ^ 2 + (D k - totalTriple U k) ^ 2 ≤
      (1 + eps) * euclideanSq D + 3 * (1 + 1/eps) * frobeniusSq U := by
    nlinarith only [h0, h1, hd', hu']
  exact hspread.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

theorem coefficient_differences_interval {X : Triple} (m s t eps : ℝ)
    (hm : 0 < m) (hs : 0 < s) (hst : s ≤ t) (heps : 0 < eps)
    (hdiag : ∀ i, X i i ≤ -m) (hoff : ∀ j i, j ≠ i → m ≤ X j i)
    (htotal : ∀ i, s ≤ totalTriple X i ∧ totalTriple X i ≤ t)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 *
      (((s ^ 2 + t ^ 2) / (m ^ 2 * (s + t) ^ 2)) *
        ((1 + eps) * euclideanSq D + 3 * (1 + 1/eps) * frobeniusSq U)) := by
  obtain ⟨j, k, l, hjk, hjl, hkl, hlo, hhi⟩ := exists_ordered_indices a
  have hspread := ordered_spread_interval m s t eps hm hs hst heps hdiag hoff htotal
    a b U D hD j k l hjk hjl hkl hlo hhi
  have hdiff := pair_difference_ordered a j k l hjk hjl hkl hlo hhi
  linarith

end HlawkaSchatten.DiagonalRealBundle



/- The residual estimate in Section 6.2 of the cutoff-21 paper.
   This algebraic energy bound is slightly stronger than its rounded
   coefficient (7/4 + 2*rho)^2, and uses no square-root approximation. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

theorem weighted_square_bound (rho a b : ℝ) :
    rho * (a - b) ^ 2 ≤ rho * (1 + rho) * a ^ 2 + (1 + rho) * b ^ 2 := by
  nlinarith [sq_nonneg (rho * a + b)]

theorem residual_energy_bound {ι : Type*} [Fintype ι]
    (rho S : ℝ) (a b : ι → ℝ)
    (hrho : 0 ≤ rho) (hS : 0 ≤ S)
    (ha : ∑ i, (a i) ^ 2 ≤ 3 * S)
    (hb : ∑ i, (b i) ^ 2 ≤ 4 * rho ^ 2 * S) :
    ∑ i, (a i - b i) ^ 2 ≤ (3 + 7 * rho + 4 * rho ^ 2) * S := by
  rcases eq_or_lt_of_le hrho with hrho0 | hrhop
  · have hr : rho = 0 := hrho0.symm
    subst rho
    have hbi (i : ι) : b i = 0 := by
      have hi : (b i) ^ 2 ≤ ∑ j, (b j) ^ 2 :=
        Finset.single_le_sum (fun j _ ↦ sq_nonneg (b j)) (Finset.mem_univ i)
      norm_num at hb
      nlinarith [sq_nonneg (b i)]
    simpa [hbi] using ha
  · have hy : rho * (∑ i, (a i - b i) ^ 2) ≤
        rho * (1 + rho) * (∑ i, (a i) ^ 2) +
          (1 + rho) * (∑ i, (b i) ^ 2) := by
      simpa only [Finset.mul_sum, Finset.sum_add_distrib] using
        (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
          weighted_square_bound rho (a i) (b i)))
    have h1 := mul_le_mul_of_nonneg_left ha
      (show 0 ≤ rho * (1 + rho) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hb
      (show 0 ≤ 1 + rho by positivity)
    have h : rho * (∑ i, (a i - b i) ^ 2) ≤
        rho * ((3 + 7 * rho + 4 * rho ^ 2) * S) := by
      calc
        _ ≤ rho * (1 + rho) * (3 * S) + (1 + rho) * (4 * rho ^ 2 * S) :=
          hy.trans (add_le_add h1 h2)
        _ = _ := by ring
    exact le_of_mul_le_mul_left h hrhop

theorem residual_energy_bound_rounded {ι : Type*} [Fintype ι]
    (rho S : ℝ) (a b : ι → ℝ)
    (hrho : 0 ≤ rho) (hS : 0 ≤ S)
    (ha : ∑ i, (a i) ^ 2 ≤ 3 * S)
    (hb : ∑ i, (b i) ^ 2 ≤ 4 * rho ^ 2 * S) :
    ∑ i, (a i - b i) ^ 2 ≤ (7 / 4 + 2 * rho) ^ 2 * S := by
  have h := residual_energy_bound rho S a b hrho hS ha hb
  have hc : 3 + 7 * rho + 4 * rho ^ 2 ≤ (7 / 4 + 2 * rho) ^ 2 := by
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right hc hS)

end HlawkaSchatten.DiagonalRealBundle



/- The six non-main coordinates of the three pair residuals, in order
   (k,i) = (0,1), (0,2), (1,0), (1,2), (2,0), (2,1).
   U j i denotes row j, coordinate i. No orthogonality assumptions are needed
   for these two operator bounds from Section 6.2 of the paper. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

noncomputable def matrixEnergy (U : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ j, ∑ i, U j i ^ 2

noncomputable def pairDirect (U : Fin 3 → Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![U 1 1 + U 2 1, U 1 2 + U 2 2,
    U 0 0 + U 2 0, U 0 2 + U 2 2,
    U 0 0 + U 1 0, U 0 1 + U 1 1]

noncomputable def pairMain (U : Fin 3 → Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![U 1 0 + U 2 0, U 1 0 + U 2 0,
    U 0 1 + U 2 1, U 0 1 + U 2 1,
    U 0 2 + U 1 2, U 0 2 + U 1 2]

theorem two_sums_square_le (x y z : ℝ) :
    (x + y) ^ 2 + (x + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y - z), sq_nonneg (y - z)]

theorem pairDirect_energy_bound (U : Fin 3 → Fin 3 → ℝ) :
    ∑ i, pairDirect U i ^ 2 ≤ 3 * matrixEnergy U := by
  have h0 := two_sums_square_le (U 0 0) (U 1 0) (U 2 0)
  have h1 := two_sums_square_le (U 1 1) (U 0 1) (U 2 1)
  have h2 := two_sums_square_le (U 2 2) (U 0 2) (U 1 2)
  simp [pairDirect, matrixEnergy, Fin.sum_univ_succ] at *
  nlinarith

theorem pairMain_energy_bound (U : Fin 3 → Fin 3 → ℝ) :
    ∑ i, pairMain U i ^ 2 ≤ 4 * matrixEnergy U := by
  have h0 : (U 1 0 + U 2 0) ^ 2 ≤ 2 * (U 1 0 ^ 2 + U 2 0 ^ 2) := by
    nlinarith [sq_nonneg (U 1 0 - U 2 0)]
  have h1 : (U 0 1 + U 2 1) ^ 2 ≤ 2 * (U 0 1 ^ 2 + U 2 1 ^ 2) := by
    nlinarith [sq_nonneg (U 0 1 - U 2 1)]
  have h2 : (U 0 2 + U 1 2) ^ 2 ≤ 2 * (U 0 2 ^ 2 + U 1 2 ^ 2) := by
    nlinarith [sq_nonneg (U 0 2 - U 1 2)]
  simp [pairMain, matrixEnergy, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (U 0 0), sq_nonneg (U 1 1), sq_nonneg (U 2 2)]

theorem pairPerturbation_energy_bound (U : Fin 3 → Fin 3 → ℝ)
    (theta : Fin 6 → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (htheta : ∀ i, |theta i| ≤ rho) :
    ∑ i, (theta i * pairMain U i) ^ 2 ≤ 4 * rho ^ 2 * matrixEnergy U := by
  have hi (i : Fin 6) : (theta i * pairMain U i) ^ 2 ≤
      rho ^ 2 * pairMain U i ^ 2 := by
    have ht : theta i ^ 2 ≤ rho ^ 2 := by
      have h := abs_le.mp (htheta i)
      nlinarith
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right ht (sq_nonneg (pairMain U i))
  calc
    _ ≤ ∑ i, rho ^ 2 * pairMain U i ^ 2 := Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = rho ^ 2 * ∑ i, pairMain U i ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ rho ^ 2 * (4 * matrixEnergy U) :=
      mul_le_mul_of_nonneg_left (pairMain_energy_bound U) (sq_nonneg rho)
    _ = _ := by ring

theorem matrix_pair_residual_bound (U : Fin 3 → Fin 3 → ℝ)
    (theta : Fin 6 → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (htheta : ∀ i, |theta i| ≤ rho) :
    ∑ i, (pairDirect U i - theta i * pairMain U i) ^ 2 ≤
      (7 / 4 + 2 * rho) ^ 2 * matrixEnergy U := by
  exact residual_energy_bound_rounded rho (matrixEnergy U)
    (pairDirect U) (fun i ↦ theta i * pairMain U i) hrho
    (Finset.sum_nonneg (fun j _ ↦ Finset.sum_nonneg (fun i _ ↦ sq_nonneg (U j i))))
    (pairDirect_energy_bound U) (pairPerturbation_energy_bound U theta rho hrho htheta)

end HlawkaSchatten.DiagonalRealBundle


/- Canceled pair decomposition and weighted radial component adapted from
   @bwdaugherty's accepted cutoff-32 convex-box proof, Apache-2.0.
   The sharper six-coordinate matrix estimate is from the current paper.
   All box/ratio and Young constants are parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction
theorem weighted_component_bound (a b c d M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : |c| ≤ M) (hd : |d| ≤ M) :
    |(b * c - a * d) / (a + b)| ≤ M := by
  have hab : 0 < a + b := by positivity
  rw [abs_div, abs_of_pos hab, div_le_iff₀ hab]
  calc
    |b * c - a * d| ≤ |b * c| + |a * d| := abs_sub _ _
    _ = b * |c| + a * |d| := by rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_pos ha]
    _ ≤ b * M + a * M := by gcongr
    _ = M * (a + b) := by ring

noncomputable def pairRadial (X : Triple) (a : Fin 3 → ℝ) (j i : Fin 3) : ℝ :=
  pairDifference a j *
    ((X (pairRight j) j * X (pairLeft j) i - X (pairLeft j) j * X (pairRight j) i) /
      (X (pairLeft j) j + X (pairRight j) j))

noncomputable def pairError (X U : Triple) (j i : Fin 3) : ℝ :=
  pairTriple U j i - (pairTriple X j i / pairTriple X j j) * pairTriple U j j

noncomputable def canceledPairSq (X Z : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j,
    (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2

noncomputable def radialPairSq (X : Triple) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairRadial X a j i ^ 2

noncomputable def errorPairSq (X U : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairError X U j i ^ 2

theorem pair_indices_off (j : Fin 3) : j ≠ pairLeft j ∧ j ≠ pairRight j := by
  fin_cases j <;> decide


theorem pair_main_pos {X : Triple}
    (hoff : ∀ j i, j ≠ i → 0 < X j i) (j : Fin 3) : 0 < pairTriple X j j := by
  have ho := pair_indices_off j
  rw [pairTriple_eq_indices, Pi.add_apply]
  exact add_pos (hoff _ _ ho.1.symm) (hoff _ _ ho.2.symm)

theorem canceled_pair_decomposition {X : Triple}
    (hoff : ∀ j i, j ≠ i → 0 < X j i)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (j i : Fin 3) :
    pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i =
      pairRadial X a j i + pairError X U j i := by
  have ho := pair_indices_off j
  have hden : X (pairLeft j) j + X (pairRight j) j ≠ 0 :=
    (add_pos (hoff _ _ ho.1.symm) (hoff _ _ ho.2.symm)).ne'
  simp only [pairRadial, pairError, pairDifference, pairTriple_eq_indices, Pi.add_apply, hZ]
  field_simp
  ring

theorem radial_pair_component_sq {X : Triple} {M : ℝ}
    (hoff : ∀ j i, j ≠ i → 0 < X j i) (hM : 0 ≤ M)
    (hcol : ∀ j i, |X j i| ≤ M) (a : Fin 3 → ℝ) (j i : Fin 3) :
    pairRadial X a j i ^ 2 ≤ M ^ 2 * pairDifference a j ^ 2 := by
  have ho := pair_indices_off j
  have hc := weighted_component_bound (X (pairLeft j) j) (X (pairRight j) j)
    (X (pairLeft j) i) (X (pairRight j) i) M
    (hoff _ _ ho.1.symm) (hoff _ _ ho.2.symm) (hcol _ _) (hcol _ _)
  have hs := (sq_le_sq₀ (abs_nonneg _) hM).mpr hc
  rw [sq_abs] at hs
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (pairDifference a j))
  simpa only [pairRadial, mul_pow, mul_comm] using hh

theorem radial_pairs_sq_bound {X : Triple} {M : ℝ}
    (hoff : ∀ j i, j ≠ i → 0 < X j i) (hM : 0 ≤ M)
    (hcol : ∀ j i, |X j i| ≤ M) (a : Fin 3 → ℝ) :
    (∑ j, radialPairSq X a j) ≤ 2 * M ^ 2 * ∑ j, pairDifference a j ^ 2 := by
  have hh (j : Fin 3) : radialPairSq X a j ≤ 2 * M ^ 2 * pairDifference a j ^ 2 := by
    have hi := Finset.sum_le_sum (s := Finset.univ.erase j)
      (fun i _ ↦ radial_pair_component_sq hoff hM hcol a j i)
    simpa [radialPairSq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
      mul_assoc] using hi
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hh j)
  simpa only [← Finset.mul_sum] using hs

theorem error_pairs_sharp_bound {X : Triple} (U : Triple) (rho : ℝ) (hrho : 0 ≤ rho)
    (hoff : ∀ j i, j ≠ i → 0 < X j i)
    (hratio : ∀ j i, i ≠ j → |pairTriple X j i / pairTriple X j j| ≤ rho) :
    (∑ j, errorPairSq X U j) ≤ (7/4 + 2*rho) ^ 2 * frobeniusSq U := by
  let theta : Fin 6 → ℝ := ![
    pairTriple X 0 1 / pairTriple X 0 0, pairTriple X 0 2 / pairTriple X 0 0,
    pairTriple X 1 0 / pairTriple X 1 1, pairTriple X 1 2 / pairTriple X 1 1,
    pairTriple X 2 0 / pairTriple X 2 2, pairTriple X 2 1 / pairTriple X 2 2]
  have htheta : ∀ i, |theta i| ≤ rho := by
    intro i
    fin_cases i
    · simpa [theta] using hratio 0 1 (by decide)
    · simpa [theta] using hratio 0 2 (by decide)
    · simpa [theta] using hratio 1 0 (by decide)
    · simpa [theta] using hratio 1 2 (by decide)
    · simpa [theta] using hratio 2 0 (by decide)
    · simpa [theta] using hratio 2 1 (by decide)
  have hz (j : Fin 3) : pairError X U j j = 0 := by
    simp only [pairError, div_self (pair_main_pos hoff j).ne', one_mul, sub_self]
  have hfull (j : Fin 3) : errorPairSq X U j = ∑ i, pairError X U j i ^ 2 := by
    have hh := Finset.sum_erase_add (Finset.univ) (fun i ↦ pairError X U j i ^ 2) (Finset.mem_univ j)
    simpa only [errorPairSq, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using hh
  have hs : (∑ j, errorPairSq X U j) =
      ∑ i, (pairDirect U i - theta i * pairMain U i) ^ 2 := by
    simp only [hfull, Fin.sum_univ_three]
    rw [hz 0, hz 1, hz 2]
    simp [pairError, pairTriple, theta, pairDirect, pairMain, Fin.sum_univ_succ] <;> ring
  rw [hs]
  simpa only [matrixEnergy, frobeniusSq, euclideanSq] using
    matrix_pair_residual_bound U theta rho hrho htheta

theorem canceled_pairs_sq_estimate {X : Triple} {M rho eps Q : ℝ}
    (hoff : ∀ j i, j ≠ i → 0 < X j i) (hM : 0 ≤ M) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hcol : ∀ j i, |X j i| ≤ M)
    (hratio : ∀ j i, i ≠ j → |pairTriple X j i / pairTriple X j j| ≤ rho)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hspread : (∑ j, pairDifference a j ^ 2) ≤ 2 * Q) :
    (∑ j, canceledPairSq X Z j) ≤
      4 * M ^ 2 * (1 + eps) * Q + (7/4 + 2*rho) ^ 2 * (1 + 1/eps) * frobeniusSq U := by
  have hy (j : Fin 3) : canceledPairSq X Z j ≤
      (1 + eps) * radialPairSq X a j + (1 + 1/eps) * errorPairSq X U j := by
    unfold canceledPairSq radialPairSq errorPairSq
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [canceled_pair_decomposition hoff Z U a hZ j i]
    exact young_square eps _ _ heps
  have hyall := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hy j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hyall
  have hr := radial_pairs_sq_bound hoff hM hcol a
  have hrad : (∑ j, radialPairSq X a j) ≤ 4 * M ^ 2 * Q := by
    calc
      _ ≤ 2 * M ^ 2 * ∑ j, pairDifference a j ^ 2 := hr
      _ ≤ 2 * M ^ 2 * (2 * Q) := mul_le_mul_of_nonneg_left hspread (by positivity)
      _ = _ := by ring
  have he := error_pairs_sharp_bound U rho hrho hoff hratio
  calc
    _ ≤ (1 + eps) * (∑ j, radialPairSq X a j) +
        (1 + 1/eps) * (∑ j, errorPairSq X U j) := hyall
    _ ≤ (1 + eps) * (4 * M ^ 2 * Q) +
        (1 + 1/eps) * ((7/4 + 2*rho) ^ 2 * frobeniusSq U) :=
      add_le_add (mul_le_mul_of_nonneg_left hrad (by positivity))
        (mul_le_mul_of_nonneg_left he (by positivity))
    _ = _ := by ring

end HlawkaSchatten.DiagonalRealBundle



/- Every coefficient used in the geometric estimate follows from the
   coordinate box, actual norm cap and linear pair floor retained in the
   convex domain. No normalization equality is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]

theorem pairTriple_add_excluded (X : Triple) (j i : Fin 3) :
    pairTriple X j i + X j i = totalTriple X i := by
  fin_cases j <;> simp [pairTriple, totalTriple, Fin.sum_univ_three] <;> ring

theorem coordinateBox_column_bounds {ell u v w m M : ℝ} {X : Triple}
    (hB : coordinateBox ell u v w X) (hm : 0 < m)
    (hmell : m ≤ ell) (hmv : m ≤ v) (huM : u ≤ M) (hwM : w ≤ M) :
    ∀ j i, m ≤ |X j i| ∧ |X j i| ≤ M := by
  intro j i
  have hx := hB j i
  by_cases hji : j = i
  · rw [if_pos hji] at hx
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · rw [if_neg hji] at hx
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith

theorem coordinateBox_pair_main {ell u v w : ℝ} {X : Triple}
    (hB : coordinateBox ell u v w X) : ∀ j, 2*v ≤ pairTriple X j j := by
  intro j
  have ho := pair_indices_off j
  have hl := hB (pairLeft j) j
  have hr := hB (pairRight j) j
  rw [if_neg ho.1.symm] at hl
  rw [if_neg ho.2.symm] at hr
  rw [pairTriple_eq_indices, Pi.add_apply]
  linarith

theorem coordinateBox_pair_tail {ell u v w : ℝ} {X : Triple}
    (hB : coordinateBox ell u v w X) :
    ∀ j i, i ≠ j → v-u ≤ pairTriple X j i ∧ pairTriple X j i ≤ w-ell := by
  intro j i hij
  have h0 := hB 0 i
  have h1 := hB 1 i
  have h2 := hB 2 i
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, Fin.ext_iff] at h0 h1 h2 ⊢
    constructor <;> linarith

theorem pair_floor_main {J : ℝ} {X : Triple}
    (hJ : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → J ≤ X j i + X k i) :
    ∀ j, J ≤ pairTriple X j j := by
  intro j
  fin_cases j
  · simpa [pairTriple] using hJ 0 1 2 (by decide) (by decide) (by decide)
  · simpa [pairTriple] using hJ 1 0 2 (by decide) (by decide) (by decide)
  · simpa [pairTriple] using hJ 2 0 1 (by decide) (by decide) (by decide)

theorem total_coordinate_le_cap {p A : ℝ} (hp : 1 ≤ p) (X : Triple)
    (hT : lpNorm p (X 0 + X 1 + X 2) ≤ A) : ∀ i, totalTriple X i ≤ A := by
  intro i
  have hh := norm_apply_le_lpNorm hp (X 0 + X 1 + X 2) i
  rw [← totalTriple_eq X, Real.norm_eq_abs] at hh
  rw [← totalTriple_eq X] at hT
  exact (le_abs_self _).trans (hh.trans hT)

theorem norm_domain_pair_bounds {p ell u v w U A J W0 L s t eta : ℝ}
    (hp : 1 ≤ p) (X : Triple) (hX : X ∈ normCappedDomain p ell u v w U A J W0)
    (hL : L ≤ max (2*v) J) (hs : s ≤ L-u) (ht : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta) :
    (∀ j, L ≤ pairTriple X j j) ∧
    (∀ i, s ≤ totalTriple X i ∧ totalTriple X i ≤ t) ∧
    (∀ j i, i ≠ j → |pairTriple X j i| ≤ eta) := by
  rcases hX with ⟨hB, hN, hT, hJ, hW⟩
  have hmain (j : Fin 3) : L ≤ pairTriple X j j :=
    hL.trans (max_le (coordinateBox_pair_main hB j) (pair_floor_main hJ j))
  have hcap := total_coordinate_le_cap hp X hT
  have htotal (i : Fin 3) : s ≤ totalTriple X i ∧ totalTriple X i ≤ t := by
    have hd : -u ≤ X i i ∧ X i i ≤ -ell := by simpa [coordinateBox] using hB i i
    have hm := hmain i
    have h0 := hB 0 i
    have h1 := hB 1 i
    have h2 := hB 2 i
    have hupper : totalTriple X i ≤ 2*w-ell := by
      fin_cases i <;> norm_num [Fin.ext_iff, totalTriple, Fin.sum_univ_three] at h0 h1 h2 ⊢ <;> linarith
    constructor
    · have he := pairTriple_add_excluded X i i
      linarith
    · exact (le_min hupper (hcap i)).trans ht
  refine ⟨hmain, htotal, ?_⟩
  intro j i hij
  have hb := coordinateBox_pair_tail hB j i hij
  have hoff : v ≤ X j i := by
    have hh := hB j i
    rw [if_neg hij.symm] at hh
    exact hh.1
  have he := pairTriple_add_excluded X j i
  have htailcap : pairTriple X j i ≤ A-v := by linarith [hcap i]
  exact abs_le.mpr ⟨by linarith, (le_min hb.2 htailcap).trans hetahi⟩

theorem norm_domain_pair_ratio {p ell u v w U A J W0 L s t eta : ℝ}
    (hp : 1 ≤ p) (X : Triple) (hX : X ∈ normCappedDomain p ell u v w U A J W0)
    (hL : L ≤ max (2*v) J) (hs : s ≤ L-u) (ht : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (hLpos : 0 < L) (heta : 0 ≤ eta) :
    ∀ j i, i ≠ j → |pairTriple X j i / pairTriple X j j| ≤ eta/L := by
  have hh := norm_domain_pair_bounds hp X hX hL hs ht hetalo hetahi
  intro j i hij
  have hmain := hh.1 j
  have htail := hh.2.2 j i hij
  rw [abs_div, abs_of_pos (hLpos.trans_le hmain)]
  calc
    _ ≤ eta / pairTriple X j j := div_le_div_of_nonneg_right htail (hLpos.le.trans hmain)
    _ ≤ eta/L := div_le_div_of_nonneg_left heta hLpos hmain

end HlawkaSchatten.DiagonalRealBundle


/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/- Adapted upstream derivative proofs, generalized from entryBox to a convex
   domain with seven nonzero norm arguments. Endpoint continuity uses lpNorm. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

/-- The deficit expressed in terms of power sums. -/
theorem tripleDeficit_eq_sums (p K : ℝ) (X : Triple) :
    tripleDeficit p K X = (2 * K - 1) * (∑ j, lpNorm p (X j)) +
      lpNorm p (totalTriple X) - K * (∑ j, lpNorm p (pairTriple X j)) := by
  simp only [tripleDeficit, hlawkaDeficit, totalTriple_eq, pairTriple, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- The total of a linearly perturbed triple. -/
theorem totalTriple_add_smul (X Z : Triple) (t : ℝ) :
    totalTriple (X + t • Z) = totalTriple X + t • totalTriple Z := by
  simp [totalTriple, Finset.sum_add_distrib, Finset.smul_sum]

/-- The pairs of a linearly perturbed triple. -/
theorem pairTriple_add_smul (X Z : Triple) (t : ℝ) :
    pairTriple (X + t • Z) = pairTriple X + t • pairTriple Z := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring

/-- Differentiability of the deficit along a line. -/
theorem hasDerivAt_tripleDeficit_line {p : ℝ} (hp : 1 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (hcol0 : ∀ j, (X + t • Z) j ≠ 0)
    (htotal0 : totalTriple (X + t • Z) ≠ 0)
    (hpair0 : ∀ j, pairTriple (X + t • Z) j ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ tripleDeficit p K (X + s • Z))
      (deficitSlope p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_lpNorm_line hp (X j) (Z j) t
    (hcol0 j)
  have htotal := hasDerivAt_lpNorm_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact htotal0)
  have hpair (j : Fin 3) := hasDerivAt_lpNorm_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact hpair0 j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [tripleDeficit_eq_sums, deficitSlope, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl

/-- Differentiability of the deficit slope along a line. -/
theorem hasDerivAt_deficitSlope_line {p : ℝ} (hp : 4 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (hcol0 : ∀ j, (X + t • Z) j ≠ 0)
    (htotal0 : totalTriple (X + t • Z) ≠ 0)
    (hpair0 : ∀ j, pairTriple (X + t • Z) j ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ deficitSlope p K (X + s • Z) Z)
      (deficitHessian p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_normSlope_line hp (X j) (Z j) t
    (hcol0 j)
  have htotal := hasDerivAt_normSlope_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact htotal0)
  have hpair (j : Fin 3) := hasDerivAt_normSlope_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact hpair0 j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [deficitSlope, deficitHessian, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl

/-- Continuity of the deficit functional. -/
theorem continuous_tripleDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) :
    Continuous (tripleDeficit p K) := by
  have hc (j : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j)) :=
    (continuous_lpNorm hp).comp (continuous_apply j)
  have ht : Continuous (fun X : Triple ↦ lpNorm p (X 0 + X 1 + X 2)) :=
    (continuous_lpNorm hp).comp
      (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
  have hpairs (j k : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j + X k)) :=
    (continuous_lpNorm hp).comp ((continuous_apply j).add (continuous_apply k))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add ht).sub
    (continuous_const.mul (((hpairs 0 1).add (hpairs 0 2)).add (hpairs 1 2)))

theorem convexOn_tripleDeficit_of_hessian {p K : ℝ} (hp : 4 < p)
    (C : Set Triple) (hC : Convex ℝ C)
    (hcol : ∀ X ∈ C, ∀ j, X j ≠ 0)
    (htotal : ∀ X ∈ C, totalTriple X ≠ 0)
    (hpair : ∀ X ∈ C, ∀ j, pairTriple X j ≠ 0)
    (hH : ∀ X ∈ C, ∀ Z, 0 ≤ deficitHessian p K X Z) :
    ConvexOn ℝ C (tripleDeficit p K) := by
  refine ⟨hC, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := Y - X
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : X + t • Z ∈ C := by
    have he : X + t • Z = (1 - t) • X + t • Y := by
      dsimp [Z]
      module
    rw [he]
    exact hC hX hY (by linarith [ht.2]) ht.1 (by ring)
  have hcont : Continuous (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) :=
    (continuous_tripleDeficit (by linarith : 0 < p) K).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcont.continuousOn
      (f' := fun t ↦ deficitSlope p K (X + t • Z) Z)
      (f'' := fun t ↦ deficitHessian p K (X + t • Z) Z)
    · intro t ht
      exact (hasDerivAt_tripleDeficit_line (by linarith : 1 < p) K X Z t
        (hcol _ (hline t (interior_subset ht)))
        (htotal _ (hline t (interior_subset ht)))
        (hpair _ (hline t (interior_subset ht)))).hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_deficitSlope_line (by linarith : 4 < p) K X Z t
        (hcol _ (hline t (interior_subset ht)))
        (htotal _ (hline t (interior_subset ht)))
        (hpair _ (hline t (interior_subset ht)))).hasDerivWithinAt
    · intro t ht
      exact hH _ (hline t (interior_subset ht)) Z
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha hb hab
  have hpoint : X + b • Z = a • X + b • Y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [Z]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    Z, add_sub_cancel, hpoint] using h


end HlawkaSchatten.DiagonalRealBundle


/- Nonvanishing follows from the actual coordinate and linear pair floors.
   No equal-norm or normalization equality is imposed on this convex domain. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem normCappedDomain_nonzero {p ell u v w U A J W0 L s t eta : ℝ}
    (hp : 1 ≤ p) (hell : 0 < ell) (hLpos : 0 < L) (hspos : 0 < s)
    (hL : L ≤ max (2*v) J) (hs : s ≤ L-u) (ht : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (X : Triple) (hX : X ∈ normCappedDomain p ell u v w U A J W0) :
    (∀ j, X j ≠ 0) ∧ totalTriple X ≠ 0 ∧ (∀ j, pairTriple X j ≠ 0) := by
  have hb := norm_domain_pair_bounds hp X hX hL hs ht hetalo hetahi
  refine ⟨?_, ?_, ?_⟩
  · intro j hz
    have hd : -u ≤ X j j ∧ X j j ≤ -ell := by
      simpa [coordinateBox] using hX.1 j j
    have he := congrFun hz j
    simp only [Pi.zero_apply] at he
    linarith
  · intro hz
    have hh := (hb.2.1 0).1
    have he := congrFun hz 0
    simp only [Pi.zero_apply] at he
    linarith
  · intro j hz
    have hh := hb.1 j
    have he := congrFun hz j
    simp only [Pi.zero_apply] at he
    linarith

theorem normCappedDomain_deficit_convex {p K ell u v w U A J W0 L s t eta : ℝ}
    (hp : 4 < p) (hell : 0 < ell) (hLpos : 0 < L) (hspos : 0 < s)
    (hL : L ≤ max (2*v) J) (hs : s ≤ L-u) (ht : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (hH : ∀ X ∈ normCappedDomain p ell u v w U A J W0, ∀ Z,
      0 ≤ deficitHessian p K X Z) :
    ConvexOn ℝ (normCappedDomain p ell u v w U A J W0) (tripleDeficit p K) := by
  have hn := normCappedDomain_nonzero (p := p) (ell := ell) (u := u) (v := v)
    (w := w) (U := U) (A := A) (J := J) (W0 := W0) (L := L) (s := s) (t := t)
    (eta := eta) (by linarith) hell hLpos hspos hL hs ht hetalo hetahi
  exact convexOn_tripleDeficit_of_hessian hp _
    (normCappedDomain_convex (by linarith) ell u v w U A J W0)
    (fun X hX ↦ (hn X hX).1) (fun X hX ↦ (hn X hX).2.1)
    (fun X hX ↦ (hn X hX).2.2) hH

end HlawkaSchatten.DiagonalRealBundle


/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The cyclic comparison constant

The constant is defined from an explicit scalar formula on a fixed compact
interval. Its denominator is positive, so continuity gives an attained
maximum without presupposing the global Hlawka inequality.
-/

namespace HlawkaSchatten.DiagonalConstruction

/-- The cyclic singleton norm is strictly positive for nonneg `t`. -/
theorem cyclicA_pos {p t : ℝ} (ht : 0 ≤ t) : 0 < cyclicA p t := by
  unfold cyclicA
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The cyclic pair-sum norm is nonneg. -/
theorem cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity

/-- Raising `cyclicA` to the `p`-th power recovers `t^p + 2`. -/
theorem cyclicA_rpow {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    cyclicA p t ^ p = t ^ p + 2 := by
  rw [cyclicA, ← Real.rpow_mul (by positivity : 0 ≤ t ^ p + 2),
    one_div_mul_cancel hp.ne', Real.rpow_one]

/-- Raising `cyclicB` to the `p`-th power recovers `2|1-t|^p + 2^p`. -/
theorem cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The denominator of the cyclic ratio is strictly positive for `p > 1`. -/
theorem cyclic_denominator_pos {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    0 < 6 * cyclicA p t - 3 * cyclicB p t := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have habs : |1 - t| ^ p ≤ 1 + t ^ p := by
    rcases le_total t 1 with h | h
    · have hpow := Real.rpow_le_rpow (abs_nonneg (1 - t))
        (show |1 - t| ≤ 1 by rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith) hp0.le
      rw [Real.one_rpow] at hpow
      linarith [Real.rpow_nonneg ht p]
    · have hpow := Real.rpow_le_rpow (abs_nonneg (1 - t))
        (show |1 - t| ≤ t by rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith) hp0.le
      linarith
  have htwo : (2 : ℝ) < (2 : ℝ) ^ p := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
  have hlt : cyclicB p t ^ p < (2 * cyclicA p t) ^ p := by
    rw [cyclicB_rpow hp0, Real.mul_rpow (by norm_num) (cyclicA_pos ht).le,
      cyclicA_rpow hp0 ht]
    nlinarith [Real.rpow_nonneg ht p]
  have h := (Real.rpow_lt_rpow_iff (cyclicB_nonneg p t)
    (mul_nonneg (by norm_num) (cyclicA_pos ht).le) hp0).mp hlt
  linarith

/-- `cyclicA p` is continuous in `t`. -/
theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- `cyclicB p` is continuous in `t`. -/
theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const

/-- `cyclicRatio p` is continuous on `[0, ∞)`. -/
theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'

/-- The cyclic constant is attained at some `t ∈ [1/2, 2]`. -/
theorem cyclic_maximum_attained {p : ℝ} (hp : 1 < p) :
    ∃ t ∈ Set.Icc (1 / 2 : ℝ) 2, cyclicRatio p t = cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun t ht ↦ by
      simp only [Set.mem_Ici]; linarith [ht.1])
  obtain ⟨t, ht, heq⟩ := isCompact_Icc.exists_sSup_image_eq
    (Set.nonempty_Icc.mpr (by norm_num : (1 / 2 : ℝ) ≤ 2)) hc
  exact ⟨t, ht, heq.symm⟩

/-- Every cyclic ratio on `[1/2, 2]` is at most `cyclicConstant p`. -/
theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)

/-- At `t = 2`, the cyclic ratio equals 1. -/
theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := cyclicA_pos (by norm_num)
  have hB : cyclicB p 2 = cyclicA p 2 := by
    norm_num [cyclicA, cyclicB, add_comm]
  rw [cyclicRatio, hB]
  norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
  have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
  rw [hden, div_self (by positivity)]

/-- The cyclic constant is at least 1. -/
theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  rw [← cyclicRatio_two p]
  exact cyclicRatio_le_constant hp (by norm_num)

end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Cyclic witnesses and the necessary lower bound

The three cyclic vectors have equal norms and their ratio is the scalar
formula defining the comparison constant. Zero padding preserves all seven
norms, so the lower bound holds in every dimension at least three.
-/

namespace HlawkaSchatten.DiagonalConstruction

/-- The first cyclic witness vector `(-t, 1, 1)`. -/
def cyclicX (t : ℝ) : Fin 3 → ℝ := ![-t, 1, 1]
/-- The second cyclic witness vector `(1, -t, 1)`. -/
def cyclicY (t : ℝ) : Fin 3 → ℝ := ![1, -t, 1]
/-- The third cyclic witness vector `(1, 1, -t)`. -/
def cyclicZ (t : ℝ) : Fin 3 → ℝ := ![1, 1, -t]

/-- The `p`-norm of `cyclicX t` equals `cyclicA p t`. -/
theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t) = cyclicA p t := by
  simp [lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

/-- The `p`-norm of `cyclicY t` equals `cyclicA p t`. -/
theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicY t) = cyclicA p t := by
  simp [lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

/-- The `p`-norm of `cyclicZ t` equals `cyclicA p t`. -/
theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

/-- The `p`-norm of `cyclicX + cyclicY` equals `cyclicB`. -/
theorem lpNorm_cyclicXY (p t : ℝ) :
    lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  have he : cyclicX t + cyclicY t = ![1 - t, 1 - t, 2] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY] <;> ring
  rw [he]
  simp [lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

/-- The `p`-norm of `cyclicX + cyclicZ` equals `cyclicB`. -/
theorem lpNorm_cyclicXZ (p t : ℝ) :
    lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  have he : cyclicX t + cyclicZ t = ![1 - t, 2, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicZ] <;> ring
  rw [he]
  simp [lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

/-- The `p`-norm of `cyclicY + cyclicZ` equals `cyclicB`. -/
theorem lpNorm_cyclicYZ (p t : ℝ) :
    lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  have he : cyclicY t + cyclicZ t = ![2, 1 - t, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicY, cyclicZ] <;> ring
  rw [he]
  simp [lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

/-- The `p`-norm of the cyclic total `X + Y + Z` equals `3^(1/p) |2-t|`. -/
theorem lpNorm_cyclicXYZ {p : ℝ} (hp : 0 < p) (t : ℝ) :
    lpNorm p (cyclicX t + cyclicY t + cyclicZ t) =
      (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have he : cyclicX t + cyclicY t + cyclicZ t = fun _ ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [he, lpNorm_const hp]
  simp

/-- The triple deficit of the cyclic family equals `3A - 3^(1/p)|2-t|`. -/
theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht,
    lpNorm_cyclicXYZ hp]
  ring

/-- The pair-deficit sum of the cyclic family equals `6A - 3B`. -/
theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY, lpNorm_cyclicXZ, lpNorm_cyclicYZ]
  ring

/-- Any real Hlawka constant in dimension 3 bounds every cyclic ratio. -/
theorem cyclicRatio_le_of_real_constant {p C : ℝ} (hp : 1 < p)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) C)
    {t : ℝ} (ht : 0 ≤ t) : cyclicRatio p t ≤ C := by
  have h := hC (cyclicX t) (cyclicY t) (cyclicZ t)
  rw [cyclic_tripleGap (zero_lt_one.trans hp) ht, cyclic_pairGapSum ht] at h
  exact (div_le_iff₀ (cyclic_denominator_pos hp ht)).mpr h

/-- A complex Hlawka constant is also a real Hlawka constant. -/
theorem real_constant_of_complex_constant {p C : ℝ} {n : ℕ}
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) C := by
  intro x y z
  have h := hC (fun i ↦ (x i : ℂ)) (fun i ↦ (y i : ℂ)) (fun i ↦ (z i : ℂ))
  have hadd (u v : Fin n → ℝ) :
      (fun i ↦ (u i : ℂ)) + (fun i ↦ (v i : ℂ)) =
        fun i ↦ ((u + v) i : ℂ) := by ext; simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_ofReal] using h

/-- Any complex Hlawka constant in dimension `n ≥ 3` is at least the cyclic constant. -/
theorem cyclicConstant_le_of_complex_constant {p C : ℝ} (hp : 1 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C) :
    cyclicConstant p ≤ C := by
  obtain ⟨t, ht, heq⟩ := cyclic_maximum_attained hp
  rw [← heq]
  exact cyclicRatio_le_of_real_constant hp
    (hasHlawkaConstant_fin_three_of_ge (zero_lt_one.trans hp) hn
      (real_constant_of_complex_constant hC)) (by linarith [ht.1])

end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/- The upstream six-element orbit and its explicit average are retained.
   The invariant domain will be the norm-capped domain, rather than entryBox. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

/-- Permute both row and column indices of a triple. -/
def conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) : Triple :=
  fun j i ↦ X (e j) (e i)

private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]

private theorem tripleDeficit_conjugate_six (p K : ℝ) (X : Triple) (k : Fin 6) :
    tripleDeficit p K (conjugate (permutations k) X) = tripleDeficit p K X := by
  have he (e : Equiv.Perm (Fin 3)) :
      tripleDeficit p K (conjugate e X) = hlawkaDeficit p K (X (e 0)) (X (e 1)) (X (e 2)) := by
    have hsum (u v : Fin 3 → ℝ) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
    change hlawkaDeficit p K (X (e 0) ∘ e) (X (e 1) ∘ e) (X (e 2) ∘ e) = _
    simp only [hlawkaDeficit, hsum, lpNorm_comp_equiv]
  rw [he]
  fin_cases k <;> simp [permutations, tripleDeficit, hlawkaDeficit, Equiv.swap_apply_def,
    add_comm, add_left_comm, add_assoc]

/-- The orbit average over the six simultaneous row-and-column permutations. -/
noncomputable def orbitAverage (X : Triple) : Triple :=
  ∑ k : Fin 6, (1 / 6 : ℝ) • conjugate (permutations k) X

/-- The average diagonal entry of a triple. -/
noncomputable def averageDiagonal (X : Triple) : ℝ := (X 0 0 + X 1 1 + X 2 2) / 3

/-- The average off-diagonal entry of a triple. -/
noncomputable def averageOffDiagonal (X : Triple) : ℝ :=
  (X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) / 6

/-- The orbit average is constant on diagonal and off-diagonal entries. -/
theorem orbitAverage_apply (X : Triple) (j i : Fin 3) :
    orbitAverage X j i = if i = j then averageDiagonal X else averageOffDiagonal X := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orbitAverage, permutations, conjugate, Fin.sum_univ_succ, Equiv.swap_apply_def,
      averageDiagonal, averageOffDiagonal, Fin.ext_iff] <;> ring!

/-- The orbit average is a scaled cyclic triple. -/
theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp


theorem offsum_eq_sum (X : Triple) :
    offsum X = ∑ j, ∑ i, if j = i then (0 : ℝ) else X j i := by
  simp [offsum, Fin.sum_univ_three]
  ring

theorem offsum_conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) :
    offsum (conjugate e X) = offsum X := by
  rw [offsum_eq_sum, offsum_eq_sum]
  calc
    _ = ∑ j, ∑ i, if e j = e i then (0 : ℝ) else X (e j) (e i) := by
      simp only [conjugate, e.injective.eq_iff]
    _ = ∑ j, ∑ i, if e j = i then (0 : ℝ) else X (e j) i := by
      apply Finset.sum_congr rfl
      intro j _
      exact Equiv.sum_comp e (fun i ↦ if e j = i then (0 : ℝ) else X (e j) i)
    _ = _ := Equiv.sum_comp e (fun j ↦ ∑ i, if j = i then (0 : ℝ) else X j i)

theorem totalTriple_conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) :
    totalTriple (conjugate e X) = totalTriple X ∘ e := by
  ext i
  change (∑ j, X (e j) (e i)) = ∑ j, X j (e i)
  exact Equiv.sum_comp e (fun j ↦ X j (e i))

theorem conjugate_mem_normCappedDomain (e : Equiv.Perm (Fin 3))
    {p ell u v w U A J W0 : ℝ} {X : Triple}
    (hX : X ∈ normCappedDomain p ell u v w U A J W0) :
    conjugate e X ∈ normCappedDomain p ell u v w U A J W0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j i
    simpa only [coordinateBox, conjugate, e.injective.eq_iff] using hX.1 (e j) (e i)
  · intro j
    change lpNorm p (X (e j) ∘ e) ≤ U
    rw [lpNorm_comp_equiv]
    exact hX.2.1 (e j)
  · rw [← totalTriple_eq, totalTriple_conjugate, lpNorm_comp_equiv, totalTriple_eq]
    exact hX.2.2.1
  · intro i j k hij hik hjk
    exact hX.2.2.2.1 (e i) (e j) (e k)
      (fun h ↦ hij (e.injective h)) (fun h ↦ hik (e.injective h))
      (fun h ↦ hjk (e.injective h))
  · rw [offsum_conjugate]
    exact hX.2.2.2.2

theorem orbitAverage_mem_normCappedDomain {p ell u v w U A J W0 : ℝ}
    (hp : 1 ≤ p) {X : Triple}
    (hX : X ∈ normCappedDomain p ell u v w U A J W0) :
    orbitAverage X ∈ normCappedDomain p ell u v w U A J W0 := by
  apply (normCappedDomain_convex hp ell u v w U A J W0).sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_normCappedDomain _ hX

theorem tripleDeficit_normDomain_orbitAverage_le {p K ell u v w U A J W0 : ℝ}
    (hc : ConvexOn ℝ (normCappedDomain p ell u v w U A J W0) (tripleDeficit p K))
    {X : Triple} (hX : X ∈ normCappedDomain p ell u v w U A J W0) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_normCappedDomain _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith

end HlawkaSchatten.DiagonalRealBundle

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Relabeling and normalization of a strict counterexample -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The deficit expressed in terms of gap functions. -/
theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

/-- The deficit is symmetric in the first two arguments. -/
theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

/-- The deficit is symmetric in the last two arguments. -/
theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

/-- Flipping to `(-(x+y+z), y, z)` exchanges the total norm with a singleton norm. -/
theorem lpNorm_flip_total (p : ℝ) (x y z : ι → ℝ) :
    lpNorm p (-(x + y + z) + y + z) = lpNorm p x := by
  have h : -(x + y + z) + y + z = -x := by abel
  rw [h, lpNorm_neg]

/-- The deficit of `(-(x+y+z), y, z)` differs from that of `(x, y, z)` by
`(2K - 2)(N(x+y+z) - N(x))`. -/
theorem hlawkaDeficit_flip (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (-(x + y + z)) y z = hlawkaDeficit p K x y z +
      (2 * K - 2) * (lpNorm p (x + y + z) - lpNorm p x) := by
  have hxy : -(x + y + z) + y = -(x + z) := by abel
  have hxz : -(x + y + z) + z = -(x + y) := by abel
  unfold hlawkaDeficit
  rw [lpNorm_flip_total, hxy, hxz]
  simp only [lpNorm_neg]
  ring

/-- A failed inequality can be relabeled so that its total norm is largest. -/
theorem exists_failure_total_largest {p K : ℝ} (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by
  have hmax : ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p v ≤ lpNorm p u ∧ lpNorm p w ≤ lpNorm p u := by
    rcases le_total (lpNorm p y) (lpNorm p x) with hxy | hxy
    · rcases le_total (lpNorm p z) (lpNorm p x) with hxz | hxz
      · exact ⟨x, y, z, hfail, hxy, hxz⟩
      · refine ⟨z, x, y, ?_, hxz, hxy.trans hxz⟩
        rw [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]
        exact hfail
    · rcases le_total (lpNorm p z) (lpNorm p y) with hyz | hyz
      · refine ⟨y, x, z, ?_, hxy, hyz⟩
        rw [hlawkaDeficit_swap_left]
        exact hfail
      · refine ⟨z, x, y, ?_, hxy.trans hyz, hyz⟩
        rw [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]
        exact hfail
  obtain ⟨u, v, w, hf, hv, hw⟩ := hmax
  rcases le_total (lpNorm p u) (lpNorm p (u + v + w)) with hu | hu
  · exact ⟨u, v, w, hf, hu, hv.trans hu, hw.trans hu⟩
  · refine ⟨-(u + v + w), v, w, ?_, ?_, ?_, ?_⟩
    · rw [hlawkaDeficit_flip]
      have hprod := mul_nonpos_of_nonneg_of_nonpos
        (by linarith : 0 ≤ 2 * K - 2) (sub_nonpos.mpr hu)
      linarith
    · simpa only [lpNorm_neg, lpNorm_flip_total] using hu
    · simpa only [lpNorm_flip_total] using hv
    · simpa only [lpNorm_flip_total] using hw

/-- The deficit scales linearly with `|c|` under scalar multiplication. -/
theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

/-- A failure triple has positive norm sum. -/
theorem failure_sum_pos {p K : ℝ} (hp : 0 < p) (x y z : ι → ℝ)
    (hfail : hlawkaDeficit p K x y z < 0) :
    0 < lpNorm p x + lpNorm p y + lpNorm p z := by
  have hx := lpNorm_nonneg p x
  have hy := lpNorm_nonneg p y
  have hz := lpNorm_nonneg p z
  by_contra hn
  have hnx : lpNorm p x = 0 := by linarith
  have hny : lpNorm p y = 0 := by linarith
  have hnz : lpNorm p z = 0 := by linarith
  have hx0 := (lpNorm_eq_zero_iff hp x).mp hnx
  have hy0 := (lpNorm_eq_zero_iff hp y).mp hny
  have hz0 := (lpNorm_eq_zero_iff hp z).mp hnz
  subst x; subst y; subst z
  simp [hlawkaDeficit, lpNorm_zero hp] at hfail

/-- Normalize after relabeling. No positivity of a pair-gap denominator is assumed. -/
theorem exists_normalized_failure {p K : ℝ} (hp : 0 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u + lpNorm p v + lpNorm p w = 1 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by
  obtain ⟨u, v, w, hf, hu, hv, hw⟩ := exists_failure_total_largest hK x y z hfail
  let s := lpNorm p u + lpNorm p v + lpNorm p w
  have hs : 0 < s := failure_sum_pos hp u v w hf
  refine ⟨s⁻¹ • u, s⁻¹ • v, s⁻¹ • w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp, abs_of_pos (inv_pos.mpr hs)]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hs) hf
  · simp only [lpNorm_smul hp, abs_of_pos (inv_pos.mpr hs)]
    rw [← mul_add, ← mul_add]
    exact inv_mul_cancel₀ hs.ne'
  all_goals
    simp only [← smul_add, lpNorm_smul hp, abs_of_pos (inv_pos.mpr hs)]
  · exact mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hs.le)
  · exact mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hs.le)
  · exact mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hs.le)

end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/- The original cyclic-average argument uses derived total-norm and offsum
   bounds here, rather than imposing a narrow fixed coordinate box. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem normDomain_average_parameter_bounds {p ell u v w U A J W0 : ℝ}
    (hp : 1 ≤ p) (hv : 0 < v) (huv : u ≤ 2*v) (hWA : 4*A ≤ W0)
    {X : Triple} (hX : X ∈ normCappedDomain p ell u v w U A J W0) :
    0 < averageOffDiagonal X ∧
      -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1/2) 2 := by
  have hbar := orbitAverage_mem_normCappedDomain hp hX
  have hd := hbar.1 0 0
  have ho := hbar.1 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [coordinateBox] at hd ho
  have hop : 0 < averageOffDiagonal X := hv.trans_le ho.1
  have hW : W0 ≤ 6*averageOffDiagonal X := by
    have hw := hX.2.2.2.2
    change W0 ≤ offsum X at hw
    dsimp [offsum] at hw
    dsimp [averageOffDiagonal]
    linarith only [hw]
  have htotal := total_coordinate_le_cap hp (orbitAverage X) hbar.2.2.1 0
  norm_num [totalTriple, Fin.sum_univ_three, orbitAverage_apply, Fin.ext_iff] at htotal
  refine ⟨hop, (le_div_iff₀ hop).mpr ?_, (div_le_iff₀ hop).mpr ?_⟩
  · linarith
  · linarith [ho.1, hd.1]

theorem tripleDeficit_normDomain_orbitAverage_nonneg {p ell u v w U A J W0 : ℝ}
    (hp : 1 < p) (hv : 0 < v) (huv : u ≤ 2*v) (hWA : 4*A ≤ W0)
    {X : Triple} (hX : X ∈ normCappedDomain p ell u v w U A J W0) :
    0 ≤ tripleDeficit p (cyclicConstant p) (orbitAverage X) := by
  obtain ⟨ho, ht⟩ := normDomain_average_parameter_bounds hp.le hv huv hWA hX
  let t := -averageDiagonal X / averageOffDiagonal X
  have ht0 : 0 ≤ t := by dsimp [t]; linarith [ht.1]
  have hratio := cyclicRatio_le_constant hp ht
  have hD := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, div_le_iff₀ hD] at hratio
  have hcyclic : 0 ≤ hlawkaDeficit p (cyclicConstant p) (cyclicX t) (cyclicY t) (cyclicZ t) := by
    rw [hlawkaDeficit_eq, cyclic_tripleGap (zero_lt_one.trans hp) ht0, cyclic_pairGapSum ht0]
    exact sub_nonneg.mpr hratio
  rw [orbitAverage_eq_cyclic X ho.ne']
  change 0 ≤ hlawkaDeficit p (cyclicConstant p) (averageOffDiagonal X • cyclicX t)
    (averageOffDiagonal X • cyclicY t) (averageOffDiagonal X • cyclicZ t)
  rw [hlawkaDeficit_smul (zero_lt_one.trans hp)]
  exact mul_nonneg (abs_nonneg _) hcyclic

theorem normDomain_deficit_nonneg_of_convex {p ell u v w U A J W0 : ℝ}
    (hp : 1 < p) (hv : 0 < v) (huv : u ≤ 2*v) (hWA : 4*A ≤ W0)
    (hc : ConvexOn ℝ (normCappedDomain p ell u v w U A J W0)
      (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ normCappedDomain p ell u v w U A J W0) :
    0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_normDomain_orbitAverage_nonneg hp hv huv hWA hX).trans
    (tripleDeficit_normDomain_orbitAverage_le hc hX)

end HlawkaSchatten.DiagonalRealBundle


/- Actual proofs of the two unchanged platform milestones are imported. -/
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem cyclicConstant_bounds_window {p : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32) :
    (273/625 : ℝ)*p < cyclicConstant p ∧ cyclicConstant p ≤ p/2 := by
  by_cases h26 : p ≤ 26
  · have h := scalar_window21 p hp h26
    exact ⟨h.1, h.2.1⟩
  · have h := scalar_window26 p (by linarith) hp32
    exact ⟨by nlinarith [h.1], h.2.1⟩

end HlawkaSchatten.DiagonalRealBundle


/- The geometric residual bound controls the sum of the three actual pair
   norm Hessians, with the exact coefficients used by the grouped checks. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem pair_hessian_domain_bound
    {p ell u v w Ucap A J W0 m M L s t eta eps1 eps2 : ℝ}
    (hp : 2 < p) (hm : 0 < m) (hM : 0 ≤ M) (hs : 0 < s) (hst : s ≤ t)
    (hLpos : 0 < L) (heta : 0 ≤ eta) (heps1 : 0 < eps1) (heps2 : 0 < eps2)
    (hmell : m ≤ ell) (hmv : m ≤ v) (huM : u ≤ M) (hwM : w ≤ M)
    (hL : L ≤ max (2*v) J) (hsgeom : s ≤ L-u) (htgeom : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (X : Triple) (hX : X ∈ normCappedDomain p ell u v w Ucap A J W0)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      ((p-1) * eta ^ (p-2) / L ^ (p-1)) *
        ((4 * M^2 * (1+eps2) * ((s^2+t^2)/(m^2*(s+t)^2)) * (1+eps1)) * euclideanSq D +
          (12 * M^2 * (1+eps2) * ((s^2+t^2)/(m^2*(s+t)^2)) * (1+1/eps1) +
            (7/4+2*(eta/L))^2 * (1+1/eps2)) * frobeniusSq U) := by
  have hp1 : 1 ≤ p := by linarith
  have hpred : 0 ≤ p-1 := by linarith
  have hgeom := norm_domain_pair_bounds hp1 X hX hL hsgeom htgeom hetalo hetahi
  have hcols := coordinateBox_column_bounds hX.1 hm hmell hmv huM hwM
  have hdiag (i : Fin 3) : X i i ≤ -m := by
    have hh : -u ≤ X i i ∧ X i i ≤ -ell := by simpa [coordinateBox] using hX.1 i i
    linarith
  have hoff (j i : Fin 3) (hji : j ≠ i) : 0 < X j i := by
    have hh := hX.1 j i
    rw [if_neg hji] at hh
    linarith
  have hratio := norm_domain_pair_ratio hp1 X hX hL hsgeom htgeom hetalo hetahi hLpos heta
  have hspread := coefficient_differences_interval m s t eps1 hm hs hst heps1 hdiag
    (fun j i hji ↦ (hcols j i).1.trans_eq (abs_of_pos (hoff j i hji)))
    hgeom.2.1 a b U D hD
  have hcanceled := canceled_pairs_sq_estimate hoff hM (div_nonneg heta hLpos.le) heps2
    (fun j i ↦ (hcols j i).2) hratio Z U a hZ hspread
  have hpair (j : Fin 3) : normHessian p (pairTriple X j) (pairTriple Z j) ≤
      ((p-1) * eta ^ (p-2) / L ^ (p-1)) * canceledPairSq X Z j := by
    have hlarge : L ≤ |pairTriple X j j| := (hgeom.1 j).trans (le_abs_self _)
    exact normHessian_upper_canceled hp (pairTriple X j) (pairTriple Z j) j L eta hLpos heta
      hlarge (fun i hij ↦ hgeom.2.2 j i hij)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hpair j)
  rw [← Finset.mul_sum] at hh
  have hdp : 0 ≤ (p-1) * eta ^ (p-2) / L ^ (p-1) := by positivity
  calc
    _ ≤ ((p-1) * eta ^ (p-2) / L ^ (p-1)) * (∑ j, canceledPairSq X Z j) := hh
    _ ≤ ((p-1) * eta ^ (p-2) / L ^ (p-1)) *
        (4 * M^2 * (1+eps2) *
          (((s^2+t^2)/(m^2*(s+t)^2)) *
            ((1+eps1) * euclideanSq D + 3 * (1+1/eps1) * frobeniusSq U)) +
          (7/4+2*(eta/L))^2 * (1+1/eps2) * frobeniusSq U) :=
      mul_le_mul_of_nonneg_left hcanceled hdp
    _ = _ := by ring

end HlawkaSchatten.DiagonalRealBundle



/- Assemble the original seven norm Hessians. Numeric comparisons remain
   explicit premises until the two grouped real-exponent certificates are
   connected to these coefficients. No S=3/equal-norm premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

noncomputable def lowerNormCoefficient (p m U : ℝ) : ℝ :=
  (p-1) * m ^ (p-2) / U ^ (p-1)

noncomputable def shapeFactor (m s t : ℝ) : ℝ := (s^2+t^2)/(m^2*(s+t)^2)

noncomputable def pairTotalFactor (m M s t eps1 eps2 : ℝ) : ℝ :=
  4*M^2*(1+eps2)*shapeFactor m s t*(1+eps1)

noncomputable def pairColumnFactor (m M s t eta L eps1 eps2 : ℝ) : ℝ :=
  12*M^2*(1+eps2)*shapeFactor m s t*(1+1/eps1) + (7/4+2*(eta/L))^2*(1+1/eps2)

theorem deficit_hessian_algebra (K C T P EC ET bC bT d gC gT : ℝ)
    (hK : 1/2 ≤ K) (hEC : 0 ≤ EC) (hET : 0 ≤ ET)
    (hcol : bC*EC ≤ C) (htotal : bT*ET ≤ T) (hpair : P ≤ d*(gT*ET+gC*EC))
    (hCT : K*d*gT ≤ bT) (hCC : K*d*gC ≤ (2*K-1)*bC) :
    0 ≤ (2*K-1)*C + T - K*P := by
  have hc := mul_le_mul_of_nonneg_left hcol (show 0 ≤ 2*K-1 by linarith)
  have hp := mul_le_mul_of_nonneg_left hpair (show 0 ≤ K by linarith)
  have ht := mul_nonneg (sub_nonneg.mpr hCT) hET
  have hu := mul_nonneg (sub_nonneg.mpr hCC) hEC
  nlinarith only [hc, htotal, hp, ht, hu]

theorem deficit_hessian_domain_nonneg
    {p K ell u v w Ucap A J W0 m M L s t eta eps1 eps2 : ℝ}
    (hp : 2 < p) (hK : 1/2 ≤ K) (hm : 0 < m) (hM : 0 ≤ M)
    (hs : 0 < s) (hst : s ≤ t) (hU : 0 < Ucap) (hA : 0 < A)
    (hLpos : 0 < L) (heta : 0 ≤ eta) (heps1 : 0 < eps1) (heps2 : 0 < eps2)
    (hmell : m ≤ ell) (hmv : m ≤ v) (huM : u ≤ M) (hwM : w ≤ M)
    (hL : L ≤ max (2*v) J) (hsgeom : s ≤ L-u) (htgeom : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (hCT : K * lowerNormCoefficient p eta L * pairTotalFactor m M s t eps1 eps2 ≤
      lowerNormCoefficient p s A)
    (hCC : K * lowerNormCoefficient p eta L * pairColumnFactor m M s t eta L eps1 eps2 ≤
      (2*K-1) * lowerNormCoefficient p m Ucap)
    (X : Triple) (hX : X ∈ normCappedDomain p ell u v w Ucap A J W0) (Z : Triple) :
    0 ≤ deficitHessian p K X Z := by
  have hp1 : 1 ≤ p := by linarith
  let a : Fin 3 → ℝ := fun j ↦ radialCoefficient p (X j) (Z j)
  let U : Triple := fun j ↦ Z j - a j • X j
  let b : ℝ := radialCoefficient p (totalTriple X) (totalTriple Z)
  let D : Fin 3 → ℝ := totalTriple Z - b • totalTriple X
  have hZ (j i : Fin 3) : Z j i = a j * X j i + U j i := by
    simp only [U, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have htotalZ : totalTriple Z = applyTriple X a + totalTriple U := by
    ext i
    simp only [totalTriple, applyTriple, Fin.sum_univ_three, Pi.add_apply]
    rw [hZ 0 i, hZ 1 i, hZ 2 i]
    ring
  have hD : D = applyTriple X a + totalTriple U - b • totalTriple X := by
    dsimp [D]
    rw [htotalZ]
  have hcols := coordinateBox_column_bounds hX.1 hm hmell hmv huM hwM
  have hcol (j : Fin 3) : lowerNormCoefficient p m Ucap * euclideanSq (U j) ≤
      normHessian p (X j) (Z j) := by
    exact normHessian_lower_norm_cap hp (X j) (Z j) m Ucap hm hU
      (fun i ↦ (hcols j i).1) (hX.2.1 j)
  have hcolsum : lowerNormCoefficient p m Ucap * frobeniusSq U ≤
      ∑ j, normHessian p (X j) (Z j) := by
    simpa only [frobeniusSq, Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
  have hgeom := norm_domain_pair_bounds hp1 X hX hL hsgeom htgeom hetalo hetahi
  have htotalcap : lpNorm p (totalTriple X) ≤ A := by
    rw [totalTriple_eq]
    exact hX.2.2.1
  have htotal : lowerNormCoefficient p s A * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    exact normHessian_lower_norm_cap hp (totalTriple X) (totalTriple Z) s A hs hA
      (fun i ↦ ((hgeom.2.1 i).1).trans (le_abs_self _)) htotalcap
  have hpair := pair_hessian_domain_bound hp hm hM hs hst hLpos heta heps1 heps2
    hmell hmv huM hwM hL hsgeom htgeom hetalo hetahi X hX Z U a b D hZ hD
  change (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
    lowerNormCoefficient p eta L *
      (pairTotalFactor m M s t eps1 eps2 * euclideanSq D +
        pairColumnFactor m M s t eta L eps1 eps2 * frobeniusSq U) at hpair
  exact deficit_hessian_algebra K _ _ _ (frobeniusSq U) (euclideanSq D)
    (lowerNormCoefficient p m Ucap) (lowerNormCoefficient p s A) (lowerNormCoefficient p eta L)
    (pairColumnFactor m M s t eta L eps1 eps2) (pairTotalFactor m M s t eps1 eps2)
    hK (frobeniusSq_nonneg U) (euclideanSq_nonneg D) hcolsum htotal hpair hCT hCC

end HlawkaSchatten.DiagonalRealBundle



/- Convert the checked dimensionless margins to comparisons between the
   actual norm-Hessian coefficients. Real powers and all denominators are
   handled explicitly; the pair tail eta is allowed to be zero. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle

theorem lowerNormCoefficient_pos {p m U : ℝ} (hp : 2 < p) (hm : 0 < m) (hU : 0 < U) :
    0 < lowerNormCoefficient p m U := by
  have hpred : 0 < p-1 := by linarith
  unfold lowerNormCoefficient
  positivity

theorem lowerNormCoefficient_ratio {p eta L r A : ℝ} (heta : 0 ≤ eta)
    (hL : 0 < L) (hr : 0 < r) (hA : 0 < A) :
    lowerNormCoefficient p eta L = lowerNormCoefficient p r A *
      (A/L) * ((eta*A)/(L*r)) ^ (p-2) := by
  have hAP : A ^ (p-1) = A ^ (p-2) * A := by
    rw [show p-1 = (p-2)+1 by ring, Real.rpow_add hA, Real.rpow_one]
  have hLP : L ^ (p-1) = L ^ (p-2) * L := by
    rw [show p-1 = (p-2)+1 by ring, Real.rpow_add hL, Real.rpow_one]
  have hAr : A ^ (p-2) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
  have hLr : L ^ (p-2) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have hrr : r ^ (p-2) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  unfold lowerNormCoefficient
  rw [hAP, hLP, Real.div_rpow (mul_nonneg heta hA.le) (mul_nonneg hL.le hr.le),
    Real.mul_rpow heta hA.le, Real.mul_rpow hL.le hr.le]
  field_simp [hAr, hLr, hrr, hL.ne', hA.ne'] <;> ring

theorem curvature_coefficients_from_ratios {p K c m s U A eta L gT gC : ℝ}
    (hp : 2 < p) (hm : 0 < m) (hs : 0 < s) (hU : 0 < U) (hA : 0 < A)
    (hL : 0 < L) (heta : 0 ≤ eta) (hgT : 0 ≤ gT) (hgC : 0 ≤ gC)
    (hKlo : c*p ≤ K) (hKhi : K ≤ p/2)
    (hNT : (p/2) * gT * (A/L) * ((eta*A)/(L*s)) ^ (p-2) ≤ 1)
    (hNC : (gC/2) * (U/L) * ((eta*U)/(L*m)) ^ (p-2) ≤ 2*c - 1/p) :
    K * lowerNormCoefficient p eta L * gT ≤ lowerNormCoefficient p s A ∧
    K * lowerNormCoefficient p eta L * gC ≤ (2*K-1) * lowerNormCoefficient p m U := by
  have hp0 : 0 < p := by linarith
  have hTpos := (lowerNormCoefficient_pos hp hs hA).le
  have hCpos := (lowerNormCoefficient_pos hp hm hU).le
  have hdT := lowerNormCoefficient_ratio (p := p) (r := s) heta hL hs hA
  have hdC := lowerNormCoefficient_ratio (p := p) (r := m) heta hL hm hU
  have hFT : 0 ≤ gT * (A/L) * ((eta*A)/(L*s)) ^ (p-2) := by positivity
  have hFC : 0 ≤ gC * (U/L) * ((eta*U)/(L*m)) ^ (p-2) := by positivity
  constructor
  · have hk := mul_le_mul_of_nonneg_right hKhi hFT
    have hb : K * (A/L) * ((eta*A)/(L*s)) ^ (p-2) * gT ≤ 1 := by
      nlinarith only [hk, hNT]
    have hh := mul_le_mul_of_nonneg_left hb hTpos
    rw [hdT]
    nlinarith only [hh]
  · have hk := mul_le_mul_of_nonneg_right hKhi hFC
    have hn := mul_le_mul_of_nonneg_left hNC hp0.le
    have hinv : p*(1/p) = 1 := by field_simp
    have hb : K * (U/L) * ((eta*U)/(L*m)) ^ (p-2) * gC ≤ 2*K-1 := by
      nlinarith only [hk, hn, hinv, hKlo]
    have hh := mul_le_mul_of_nonneg_left hb hCpos
    rw [hdC]
    nlinarith only [hh]

end HlawkaSchatten.DiagonalRealBundle



/- Exact grouped numeric margins for all real p in this interval.
   The geometric/Hessian implication is a separate proof obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalRealBundle

theorem grouped_curvature_numeric00 (p : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ)) :
    p * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) * (284978746246398750000000/390014297326287552842569 : ℝ) ^ (p - 2) < 1 ∧
    (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) * (15647140399332897/20071372634332940 : ℝ) ^ (p - 2) < 2 * (273/625 : ℝ) - 1/p := by
  have hpn : 21 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hrt : (284978746246398750000000/390014297326287552842569 : ℝ) ^ (p - 2) ≤ (284978746246398750000000/390014297326287552842569 : ℝ) ^ (19 : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' (x := (284978746246398750000000/390014297326287552842569 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 19) (by linarith : (19 : ℝ) ≤ p - 2)
    calc _ ≤ (284978746246398750000000/390014297326287552842569 : ℝ) ^ ((19 : ℕ) : ℝ) := hh
         _ = _ := Real.rpow_natCast _ _
  have hrc : (15647140399332897/20071372634332940 : ℝ) ^ (p - 2) ≤ (15647140399332897/20071372634332940 : ℝ) ^ (19 : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' (x := (15647140399332897/20071372634332940 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 19) (by linarith : (19 : ℝ) ≤ p - 2)
    calc _ ≤ (15647140399332897/20071372634332940 : ℝ) ^ ((19 : ℕ) : ℝ) := hh
         _ = _ := Real.rpow_natCast _ _
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrt (show 0 ≤ p * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) * (284978746246398750000000/390014297326287552842569 : ℝ) ^ (19 : ℕ) by norm_num)
    have hend : (377/16 : ℝ) * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) * (284978746246398750000000/390014297326287552842569 : ℝ) ^ (19 : ℕ) < 1 := by norm_num
    nlinarith only [h1, h2, hend]
  · have h1 := mul_le_mul_of_nonneg_left hrc (show 0 ≤ (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(21 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpn
    have hend : (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) * (15647140399332897/20071372634332940 : ℝ) ^ (19 : ℕ) < 2 * (273/625 : ℝ) - 1/(21 : ℝ) := by norm_num
    linarith only [h1, hinv, hend]

end HlawkaSchatten.DiagonalRealBundle



/- The actual original deficit Hessian is nonnegative on this
   norm-capped convex domain for every real p in the group. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem grouped_deficit_hessian00 (p K : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ))
    (hKlo : (273/625 : ℝ)*p ≤ K) (hKhi : K ≤ p/2) :
    ∀ X : Triple, X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ)
      (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) →
    ∀ Z : Triple, 0 ≤ deficitHessian p K X Z := by
  let GT : ℝ := pairTotalFactor (881/2000 : ℝ) (11847/10000 : ℝ) (342380765087/716625000000 : ℝ) (3033/2500 : ℝ) (1 : ℝ) (1/4 : ℝ)
  let GC : ℝ := pairColumnFactor (881/2000 : ℝ) (11847/10000 : ℝ) (342380765087/716625000000 : ℝ) (3033/2500 : ℝ) (2287/5000 : ℝ) (1139124440087/716625000000 : ℝ) (1 : ℝ) (1/4 : ℝ)
  have hmarg := grouped_curvature_numeric00 p hpa hpb
  have hNT : (p/2) * GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) *
      (((2287/5000 : ℝ)*(3033/2500 : ℝ))/((1139124440087/716625000000 : ℝ)*(342380765087/716625000000 : ℝ))) ^ (p-2) ≤ 1 := by
    have hbase : (((2287/5000 : ℝ)*(3033/2500 : ℝ))/((1139124440087/716625000000 : ℝ)*(342380765087/716625000000 : ℝ))) = (284978746246398750000000/390014297326287552842569 : ℝ) := by norm_num
    have hconst : GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) / 2 = (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) := by
      norm_num [GT, pairTotalFactor, shapeFactor]
    have hprod : (p/2) * GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) = p * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) := by
      calc _ = p * (GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) / 2) := by ring
           _ = _ := by rw [hconst]
    rw [hbase, hprod]
    exact hmarg.1.le
  have hNC : (GC/2) * ((1193402307/1000000000 : ℝ)/(1139124440087/716625000000 : ℝ)) *
      (((2287/5000 : ℝ)*(1193402307/1000000000 : ℝ))/((1139124440087/716625000000 : ℝ)*(881/2000 : ℝ))) ^ (p-2) ≤ 2*(273/625 : ℝ)-1/p := by
    have hbase : (((2287/5000 : ℝ)*(1193402307/1000000000 : ℝ))/((1139124440087/716625000000 : ℝ)*(881/2000 : ℝ))) = (15647140399332897/20071372634332940 : ℝ) := by norm_num
    have hconst : (GC/2) * ((1193402307/1000000000 : ℝ)/(1139124440087/716625000000 : ℝ)) = (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) := by
      norm_num [GC, pairColumnFactor, shapeFactor]
    rw [hbase, hconst]
    exact hmarg.2.le
  have hcoef := curvature_coefficients_from_ratios (p := p) (K := K) (c := (273/625 : ℝ))
    (m := (881/2000 : ℝ)) (s := (342380765087/716625000000 : ℝ)) (U := (1193402307/1000000000 : ℝ)) (A := (3033/2500 : ℝ))
    (eta := (2287/5000 : ℝ)) (L := (1139124440087/716625000000 : ℝ)) (gT := GT) (gC := GC)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num [GT, pairTotalFactor, shapeFactor])
    (by norm_num [GC, pairColumnFactor, shapeFactor])
    hKlo hKhi hNT hNC
  intro X hX Z
  exact deficit_hessian_domain_nonneg (m := (881/2000 : ℝ)) (M := (11847/10000 : ℝ))
    (L := (1139124440087/716625000000 : ℝ)) (s := (342380765087/716625000000 : ℝ)) (t := (3033/2500 : ℝ)) (eta := (2287/5000 : ℝ))
    (eps1 := (1 : ℝ)) (eps2 := (1/4 : ℝ))
    (by linarith) (by nlinarith [hKlo]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcoef.1 hcoef.2 X hX Z

end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem grouped_deficit_convex00 (p K : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ))
    (hKlo : (273/625 : ℝ)*p ≤ K) (hKhi : K ≤ p/2) :
    ConvexOn ℝ (normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ))
      (tripleDeficit p K) := by
  exact normCappedDomain_deficit_convex (L := (1139124440087/716625000000 : ℝ)) (s := (342380765087/716625000000 : ℝ)) (t := (3033/2500 : ℝ)) (eta := (2287/5000 : ℝ))
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (grouped_deficit_hessian00 p K hpa hpb hKlo hKhi)

end HlawkaSchatten.DiagonalRealBundle


set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem grouped_deficit_nonneg00 (p : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ))
    (X : Triple) (hX : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hK := cyclicConstant_bounds_window (p := p) (by linarith) (by linarith)
  exact normDomain_deficit_nonneg_of_convex (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
    (grouped_deficit_convex00 p (cyclicConstant p) hpa hpb hK.1.le hK.2) hX

end HlawkaSchatten.DiagonalRealBundle


/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 48, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab048 (p : ℝ) (hpa : (45/2 : ℝ) ≤ p) (hpb : p ≤ (721/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527741573/24570000000 : ℝ) (221511/20000000 : ℝ) (50000007371/245700000000 : ℝ) (3033/2500 : ℝ) (969704577/500000000 : ℝ) (121207893/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192984831/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11081/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4511/10000 : ℝ)
      else (3831/5000 : ℝ) ≤ X j i ∧ X j i ≤ (148/125 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527741573/24570000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (221511/20000000 : ℝ) := by norm_num
  have pc0 : 1 < (228743017/250000000 : ℝ) ^ p + (198716373/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (228743017/250000000 : ℝ)) (y := (198716373/200000000 : ℝ)) (X := (1688030633069/12500000000000 : ℝ)) (Y := (21623942863013/25000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198716373/200000000 : ℝ) ^ p + (228743017/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198716373/200000000 : ℝ)) (y := (228743017/250000000 : ℝ)) (X := (21623942863013/25000000000000 : ℝ)) (Y := (1688030633069/12500000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908553933/1000000000 : ℝ)) (τ := (228743017/250000000 : ℝ)) (σ := (198716373/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (155432215/164935078 : ℝ) ^ p + (81359984/82467539 : ℝ) ^ p := by
    exact cert_lt (x := (155432215/164935078 : ℝ)) (y := (81359984/82467539 : ℝ)) (X := (26261816112969/100000000000000 : ℝ)) (Y := (2949527403023/4000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (228743017/250000000 : ℝ)) (n' := (82467539/100000000 : ℝ)) (Ab := (31086443/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (460381343/500000000 : ℝ) ^ p + (248129519/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (460381343/500000000 : ℝ)) (y := (248129519/250000000 : ℝ)) (X := (7783467587039/50000000000000 : ℝ)) (Y := (21108270296287/25000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248129519/250000000 : ℝ) ^ p + (460381343/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248129519/250000000 : ℝ)) (y := (460381343/500000000 : ℝ)) (X := (21108270296287/25000000000000 : ℝ)) (Y := (7783467587039/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956640381/500000000 : ℝ)) (τ := (460381343/500000000 : ℝ)) (σ := (248129519/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (783409095/831570167 : ℝ) ^ p + (820494617/831570167 : ℝ) ^ p := by
    exact cert_lt (x := (783409095/831570167 : ℝ)) (y := (820494617/831570167 : ℝ)) (X := (26074065433013/100000000000000 : ℝ)) (Y := (36962967831327/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (460381343/500000000 : ℝ)) (n' := (831570167/1000000000 : ℝ)) (Ab := (156681819/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (18420649/20000000 : ℝ) ^ p + (992464263/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18420649/20000000 : ℝ)) (y := (992464263/1000000000 : ℝ)) (X := (3917505020023/25000000000000 : ℝ)) (Y := (84329996718819/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992464263/1000000000 : ℝ) ^ p + (18420649/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (992464263/1000000000 : ℝ)) (y := (18420649/20000000 : ℝ)) (X := (84329996718819/100000000000000 : ℝ)) (Y := (3917505020023/25000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1913496713/1000000000 : ℝ)) (τ := (18420649/20000000 : ℝ)) (σ := (992464263/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (783699174/831890335 : ℝ) ^ p + (164162957/166378067 : ℝ) ^ p := by
    exact cert_lt (x := (783699174/831890335 : ℝ)) (y := (164162957/166378067 : ℝ)) (X := (26065411596623/100000000000000 : ℝ)) (Y := (73934589481841/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (18420649/20000000 : ℝ)) (n' := (166378067/200000000 : ℝ)) (Ab := (391849587/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921044881/1000000000 : ℝ) ^ p + (992461773/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921044881/1000000000 : ℝ)) (y := (992461773/1000000000 : ℝ)) (X := (15674786025673/100000000000000 : ℝ)) (Y := (84325229774169/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992461773/1000000000 : ℝ) ^ p + (921044881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992461773/1000000000 : ℝ)) (y := (921044881/1000000000 : ℝ)) (X := (84325229774169/100000000000000 : ℝ)) (Y := (15674786025673/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (956753327/500000000 : ℝ)) (τ := (921044881/1000000000 : ℝ)) (σ := (992461773/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (60285580/63992699 : ℝ) ^ p + (820829537/831905087 : ℝ) ^ p := by
    exact cert_lt (x := (60285580/63992699 : ℝ)) (y := (820829537/831905087 : ℝ)) (X := (26065013371799/100000000000000 : ℝ)) (Y := (73934988076363/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921044881/1000000000 : ℝ)) (n' := (831905087/1000000000 : ℝ)) (Ab := (39185627/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (460522727/500000000 : ℝ) ^ p + (496230829/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460522727/500000000 : ℝ)) (y := (496230829/500000000 : ℝ)) (X := (3135001148533/20000000000000 : ℝ)) (Y := (10540626202537/12500000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496230829/500000000 : ℝ) ^ p + (460522727/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496230829/500000000 : ℝ)) (y := (460522727/500000000 : ℝ)) (X := (10540626202537/12500000000000 : ℝ)) (Y := (3135001148533/20000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239188389/125000000 : ℝ)) (τ := (460522727/500000000 : ℝ)) (σ := (496230829/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (783713156/831905767 : ℝ) ^ p + (820830217/831905767 : ℝ) ^ p := by
    exact cert_lt (x := (783713156/831905767 : ℝ)) (y := (820830217/831905767 : ℝ)) (X := (26064994932217/100000000000000 : ℝ)) (Y := (9241875806183/12500000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (460522727/500000000 : ℝ)) (n' := (831905767/1000000000 : ℝ)) (Ab := (195928289/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (23026137/25000000 : ℝ) ^ p + (992461653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23026137/25000000 : ℝ)) (y := (992461653/1000000000 : ℝ)) (X := (15675015712441/100000000000000 : ℝ)) (Y := (84325000048401/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992461653/1000000000 : ℝ) ^ p + (23026137/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (992461653/1000000000 : ℝ)) (y := (23026137/25000000 : ℝ)) (X := (84325000048401/100000000000000 : ℝ)) (Y := (15675015712441/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1913507133/1000000000 : ℝ)) (τ := (23026137/25000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (391856592/415952899 : ℝ) ^ p + (410415124/415952899 : ℝ) ^ p := by
    exact cert_lt (x := (391856592/415952899 : ℝ)) (y := (410415124/415952899 : ℝ)) (X := (26064994029879/100000000000000 : ℝ)) (Y := (3696750364353/5000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (23026137/25000000 : ℝ)) (n' := (415952899/500000000 : ℝ)) (Ab := (24491037/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (921045481/1000000000 : ℝ) ^ p + (992461653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921045481/1000000000 : ℝ)) (y := (992461653/1000000000 : ℝ)) (X := (7837508047947/50000000000000 : ℝ)) (Y := (84325000048401/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992461653/1000000000 : ℝ) ^ p + (921045481/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992461653/1000000000 : ℝ)) (y := (921045481/1000000000 : ℝ)) (X := (84325000048401/100000000000000 : ℝ)) (Y := (7837508047947/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (783713185/831905799 : ℝ) ^ p + (273610083/277301933 : ℝ) ^ p := by
    exact cert_lt (x := (783713185/831905799 : ℝ)) (y := (273610083/277301933 : ℝ)) (X := (26064994073289/100000000000000 : ℝ)) (Y := (462093795713/625000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1650215134/1807015169 : ℝ) ^ p + (1795939619/1807015169 : ℝ) ^ p := by
    exact cert_lt (x := (1650215134/1807015169 : ℝ)) (y := (1795939619/1807015169 : ℝ)) (X := (12935712459887/100000000000000 : ℝ)) (Y := (87064287879077/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108096019/1192984831 : ℝ) ^ p + (1181909281/1192984831 : ℝ) ^ p := by
    exact cert_lt (x := (1108096019/1192984831 : ℝ)) (y := (1181909281/1192984831 : ℝ)) (X := (4738532396781/25000000000000 : ℝ)) (Y := (40522935567701/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992461653/1000000000 : ℝ)) (U := (1192984831/1000000000 : ℝ)) (Ab := (825107567/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ)) (Ab := (1108096019/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab048 (p : ℝ) (hpa : (45/2 : ℝ) ≤ p) (hpb : p ≤ (721/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1192984831/1000000000 : ℝ)) ∧ coordinateBox (4511/10000 : ℝ) (11081/10000 : ℝ) (3831/5000 : ℝ) (148/125 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (3939836245663/2457000000000 : ℝ) ≤ X j i + X k i) ∧
    (1424199992629/245700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (121207893/125000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(45/2 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (121207893/125000000 : ℝ))
      (by norm_num) 2 45 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(45/2 : ℝ)) ≤ (193932629/200000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (193932629/200000000 : ℝ))
      (by norm_num) (by norm_num) 2 45 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(721/32 : ℝ)) ≤ (969704577/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969704577/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 721 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (527741573/24570000000 : ℝ) (221511/20000000 : ℝ) (50000007371/245700000000 : ℝ) (3033/2500 : ℝ) (969704577/500000000 : ℝ) (121207893/125000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (45/2 : ℝ)) (β := (721/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (527741573/24570000000 : ℝ)) (δ := (221511/20000000 : ℝ)) (h := (50000007371/245700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (121207893/125000000 : ℝ)) (thia := (193932629/200000000 : ℝ)) (thib := (969704577/1000000000 : ℝ))
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
  have hh := contract21_slab048 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 49, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab049 (p : ℝ) (hpa : (721/32 : ℝ) ≤ p) (hpb : p ≤ (361/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1055292983209/49208250000000 : ℝ) (11057723/1000000000 : ℝ) (4000000590499/19683300000000 : ℝ) (3033/2500 : ℝ) (969745897/500000000 : ℝ) (7575817/7812500 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298249347/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11083/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4513/10000 : ℝ)
      else (479/625 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1055292983209/49208250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11057723/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (915096247/1000000000 : ℝ) ^ p + (496794383/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915096247/1000000000 : ℝ)) (y := (496794383/500000000 : ℝ)) (X := (6754047299463/50000000000000 : ℝ)) (Y := (86491922124141/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496794383/500000000 : ℝ) ^ p + (915096247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496794383/500000000 : ℝ)) (y := (915096247/1000000000 : ℝ)) (X := (86491922124141/100000000000000 : ℝ)) (Y := (6754047299463/50000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908685013/1000000000 : ℝ)) (τ := (915096247/1000000000 : ℝ)) (σ := (496794383/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (777324101/824792432 : ℝ) ^ p + (813734709/824792432 : ℝ) ^ p := by
    exact cert_lt (x := (777324101/824792432 : ℝ)) (y := (813734709/824792432 : ℝ)) (X := (13126655222309/50000000000000 : ℝ)) (Y := (36873345417397/50000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915096247/1000000000 : ℝ)) (n' := (51549527/62500000 : ℝ)) (Ab := (777324101/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (920882643/1000000000 : ℝ) ^ p + (248131371/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (920882643/1000000000 : ℝ)) (y := (248131371/250000000 : ℝ)) (X := (622901282539/4000000000000 : ℝ)) (Y := (16885496913743/20000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248131371/250000000 : ℝ) ^ p + (920882643/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248131371/250000000 : ℝ)) (y := (920882643/1000000000 : ℝ)) (X := (16885496913743/20000000000000 : ℝ)) (Y := (622901282539/4000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1913408127/1000000000 : ℝ)) (τ := (920882643/1000000000 : ℝ)) (σ := (248131371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (783567201/831680944 : ℝ) ^ p + (820623221/831680944 : ℝ) ^ p := by
    exact cert_lt (x := (783567201/831680944 : ℝ)) (y := (820623221/831680944 : ℝ)) (X := (26065806889181/100000000000000 : ℝ)) (Y := (14786838779923/20000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (920882643/1000000000 : ℝ)) (n' := (51980059/62500000 : ℝ)) (Ab := (783567201/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (460575843/500000000 : ℝ) ^ p + (496235899/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460575843/500000000 : ℝ)) (y := (496235899/500000000 : ℝ)) (X := (15675507205421/100000000000000 : ℝ)) (Y := (21081127071741/25000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496235899/500000000 : ℝ) ^ p + (460575843/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496235899/500000000 : ℝ)) (y := (460575843/500000000 : ℝ)) (X := (21081127071741/25000000000000 : ℝ)) (Y := (15675507205421/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478405871/250000000 : ℝ)) (τ := (460575843/500000000 : ℝ)) (σ := (496235899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (783856489/832000200 : ℝ) ^ p + (820942477/832000200 : ℝ) ^ p := by
    exact cert_lt (x := (783856489/832000200 : ℝ)) (y := (820942477/832000200 : ℝ)) (X := (162857382491/625000000000 : ℝ)) (Y := (73942819598897/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (460575843/500000000 : ℝ)) (n' := (4160001/5000000 : ℝ)) (Ab := (783856489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (460582029/500000000 : ℝ) ^ p + (24811733/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (460582029/500000000 : ℝ)) (y := (24811733/25000000 : ℝ)) (X := (15680258155529/100000000000000 : ℝ)) (Y := (84319758080641/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (24811733/25000000 : ℝ) ^ p + (460582029/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (24811733/25000000 : ℝ)) (y := (460582029/500000000 : ℝ)) (X := (84319758080641/100000000000000 : ℝ)) (Y := (15680258155529/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (956816689/500000000 : ℝ)) (τ := (460582029/500000000 : ℝ)) (σ := (24811733/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261289930/277338293 : ℝ) ^ p + (820957156/832014879 : ℝ) ^ p := by
    exact cert_lt (x := (261289930/277338293 : ℝ)) (y := (820957156/832014879 : ℝ)) (X := (26056784743581/100000000000000 : ℝ)) (Y := (73943216061927/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (460582029/500000000 : ℝ)) (n' := (832014879/1000000000 : ℝ)) (Ab := (78386979/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921164627/1000000000 : ℝ) ^ p + (496234603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (921164627/1000000000 : ℝ)) (y := (496234603/500000000 : ℝ)) (X := (15680476689321/100000000000000 : ℝ)) (Y := (843195395543/1000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496234603/500000000 : ℝ) ^ p + (921164627/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496234603/500000000 : ℝ)) (y := (921164627/1000000000 : ℝ)) (X := (843195395543/1000000000000 : ℝ)) (Y := (15680476689321/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1913633833/1000000000 : ℝ)) (τ := (921164627/1000000000 : ℝ)) (σ := (496234603/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (130645067/138669259 : ℝ) ^ p + (820957831/832015554 : ℝ) ^ p := by
    exact cert_lt (x := (130645067/138669259 : ℝ)) (y := (820957831/832015554 : ℝ)) (X := (26056766787973/100000000000000 : ℝ)) (Y := (73943234292619/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921164627/1000000000 : ℝ)) (n' := (416007777/500000000 : ℝ)) (Ab := (391935201/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (921164653/1000000000 : ℝ) ^ p + (992469201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921164653/1000000000 : ℝ)) (y := (992469201/1000000000 : ℝ)) (X := (15680486675117/100000000000000 : ℝ)) (Y := (84319529969823/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992469201/1000000000 : ℝ) ^ p + (921164653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992469201/1000000000 : ℝ)) (y := (921164653/1000000000 : ℝ)) (X := (84319529969823/100000000000000 : ℝ)) (Y := (15680486675117/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (956816927/500000000 : ℝ)) (τ := (921164653/1000000000 : ℝ)) (σ := (992469201/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (261290143/277338528 : ℝ) ^ p + (820957861/832015584 : ℝ) ^ p := by
    exact cert_lt (x := (261290143/277338528 : ℝ)) (y := (820957861/832015584 : ℝ)) (X := (13028382919973/50000000000000 : ℝ)) (Y := (73943235102871/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (921164653/1000000000 : ℝ)) (n' := (26000487/31250000 : ℝ)) (Ab := (783870429/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (184232931/200000000 : ℝ) ^ p + (2481173/2500000 : ℝ) ^ p := by
    exact cert_lt (x := (184232931/200000000 : ℝ)) (y := (2481173/2500000 : ℝ)) (X := (1960060930407/12500000000000 : ℝ)) (Y := (1317492625827/1562500000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (2481173/2500000 : ℝ) ^ p + (184232931/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (2481173/2500000 : ℝ)) (y := (184232931/200000000 : ℝ)) (X := (1317492625827/1562500000000 : ℝ)) (Y := (1960060930407/12500000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (261290144/277338529 : ℝ) ^ p + (820957864/832015587 : ℝ) ^ p := by
    exact cert_lt (x := (261290144/277338529 : ℝ)) (y := (820957864/832015587 : ℝ)) (X := (5211353194029/20000000000000 : ℝ)) (Y := (73943235183897/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (275065991/301167102 : ℝ) ^ p + (1795944889/1807002612 : ℝ) ^ p := by
    exact cert_lt (x := (275065991/301167102 : ℝ)) (y := (1795944889/1807002612 : ℝ)) (X := (12933024848981/100000000000000 : ℝ)) (Y := (87066975462059/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108210253/1192997388 : ℝ) ^ p + (1181939665/1192997388 : ℝ) ^ p := by
    exact cert_lt (x := (1108210253/1192997388 : ℝ)) (y := (1181939665/1192997388 : ℝ)) (X := (18949991341573/100000000000000 : ℝ)) (Y := (10131251155043/12500000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (2481173/2500000 : ℝ)) (U := (298249347/250000000 : ℝ)) (Ab := (825197973/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ)) (Ab := (1108210253/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab049 (p : ℝ) (hpa : (721/32 : ℝ) ≤ p) (hpb : p ≤ (361/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (298249347/250000000 : ℝ)) ∧ coordinateBox (4513/10000 : ℝ) (11083/10000 : ℝ) (479/625 : ℝ) (11841/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (157838871579733/98416500000000 : ℝ) ≤ X j i + X k i) ∧
    (114099799409501/19683300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (7575817/7812500 : ℝ) ≤ (1/2 : ℝ) ^ (1/(721/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (7575817/7812500 : ℝ))
      (by norm_num) 32 721 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(721/32 : ℝ)) ≤ (969704577/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969704577/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 721 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(361/16 : ℝ)) ≤ (969745897/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969745897/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 361 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (1055292983209/49208250000000 : ℝ) (11057723/1000000000 : ℝ) (4000000590499/19683300000000 : ℝ) (3033/2500 : ℝ) (969745897/500000000 : ℝ) (7575817/7812500 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (721/32 : ℝ)) (β := (361/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1055292983209/49208250000000 : ℝ)) (δ := (11057723/1000000000 : ℝ)) (h := (4000000590499/19683300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (7575817/7812500 : ℝ)) (thia := (969704577/1000000000 : ℝ)) (thib := (969745897/1000000000 : ℝ))
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
  have hh := contract21_slab049 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 50, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab050 (p : ℝ) (hpa : (361/16 : ℝ) ≤ p) (hpb : p ≤ (723/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527551819709/24638250000000 : ℝ) (2759989/250000000 : ℝ) (2000000295659/9855300000000 : ℝ) (3033/2500 : ℝ) (969787103/500000000 : ℝ) (121218237/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238601993/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2771/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(903/2000 : ℝ)
      else (3833/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527551819709/24638250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2759989/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (915220059/1000000000 : ℝ) ^ p + (496797827/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915220059/1000000000 : ℝ)) (y := (496797827/500000000 : ℝ)) (X := (540477271877/4000000000000 : ℝ)) (Y := (10811010606323/12500000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496797827/500000000 : ℝ) ^ p + (915220059/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496797827/500000000 : ℝ)) (y := (915220059/1000000000 : ℝ)) (X := (10811010606323/12500000000000 : ℝ)) (Y := (540477271877/4000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908815713/1000000000 : ℝ)) (τ := (915220059/1000000000 : ℝ)) (σ := (496797827/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (777486665/824909074 : ℝ) ^ p + (406934559/412454537 : ℝ) ^ p := by
    exact cert_lt (x := (777486665/824909074 : ℝ)) (y := (406934559/412454537 : ℝ)) (X := (6561209958691/25000000000000 : ℝ)) (Y := (14751032287461/20000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915220059/1000000000 : ℝ)) (n' := (412454537/500000000 : ℝ)) (Ab := (155497333/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (230250557/250000000 : ℝ) ^ p + (992532881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230250557/250000000 : ℝ)) (y := (992532881/1000000000 : ℝ)) (X := (7789054833381/50000000000000 : ℝ)) (Y := (21105476614877/25000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992532881/1000000000 : ℝ) ^ p + (230250557/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992532881/1000000000 : ℝ)) (y := (230250557/250000000 : ℝ)) (X := (21105476614877/25000000000000 : ℝ)) (Y := (7789054833381/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1913535109/1000000000 : ℝ)) (τ := (230250557/250000000 : ℝ)) (σ := (992532881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (391862421/415895660 : ℝ) ^ p + (205187841/207947830 : ℝ) ^ p := by
    exact cert_lt (x := (391862421/415895660 : ℝ)) (y := (205187841/207947830 : ℝ)) (X := (26057583660901/100000000000000 : ℝ)) (Y := (1848560435233/2500000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (230250557/250000000 : ℝ)) (n' := (20794783/25000000 : ℝ)) (Ab := (391862421/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115158819/125000000 : ℝ) ^ p + (992479323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115158819/125000000 : ℝ)) (y := (992479323/1000000000 : ℝ)) (X := (15680974894959/100000000000000 : ℝ)) (Y := (84319040917659/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992479323/1000000000 : ℝ) ^ p + (115158819/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992479323/1000000000 : ℝ)) (y := (115158819/125000000 : ℝ)) (X := (84319040917659/100000000000000 : ℝ)) (Y := (15680974894959/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (15309999/8000000 : ℝ)) (τ := (115158819/125000000 : ℝ)) (σ := (992479323/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784013341/832109667 : ℝ) ^ p + (821069711/832109667 : ℝ) ^ p := by
    exact cert_lt (x := (784013341/832109667 : ℝ)) (y := (821069711/832109667 : ℝ)) (X := (26048985668903/100000000000000 : ℝ)) (Y := (73951015103983/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115158819/125000000 : ℝ)) (n' := (832109667/1000000000 : ℝ)) (Ab := (784013341/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (230320717/250000000 : ℝ) ^ p + (198495371/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (230320717/250000000 : ℝ)) (y := (198495371/200000000 : ℝ)) (X := (15685711929547/100000000000000 : ℝ)) (Y := (8431430367093/10000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198495371/200000000 : ℝ) ^ p + (230320717/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198495371/200000000 : ℝ)) (y := (230320717/250000000 : ℝ)) (X := (8431430367093/10000000000000 : ℝ)) (Y := (15685711929547/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1913759723/1000000000 : ℝ)) (τ := (230320717/250000000 : ℝ)) (σ := (198495371/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261342194/277374759 : ℝ) ^ p + (821084321/832124277 : ℝ) ^ p := by
    exact cert_lt (x := (261342194/277374759 : ℝ)) (y := (821084321/832124277 : ℝ)) (X := (3256073989977/12500000000000 : ℝ)) (Y := (36975704772877/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (230320717/250000000 : ℝ)) (n' := (832124277/1000000000 : ℝ)) (Ab := (392013291/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921283433/1000000000 : ℝ) ^ p + (496238371/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (921283433/1000000000 : ℝ)) (y := (496238371/500000000 : ℝ)) (X := (7842964637581/50000000000000 : ℝ)) (Y := (84314086777149/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496238371/500000000 : ℝ) ^ p + (921283433/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496238371/500000000 : ℝ)) (y := (921283433/1000000000 : ℝ)) (X := (84314086777149/100000000000000 : ℝ)) (Y := (7842964637581/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (76550407/40000000 : ℝ)) (τ := (921283433/1000000000 : ℝ)) (σ := (496238371/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784027189/832124947 : ℝ) ^ p + (821084991/832124947 : ℝ) ^ p := by
    exact cert_lt (x := (784027189/832124947 : ℝ)) (y := (821084991/832124947 : ℝ)) (X := (2604857369893/10000000000000 : ℝ)) (Y := (72218191049/97656250000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921283433/1000000000 : ℝ)) (n' := (832124947/1000000000 : ℝ)) (Ab := (784027189/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (460641729/500000000 : ℝ) ^ p + (992476737/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460641729/500000000 : ℝ)) (y := (992476737/1000000000 : ℝ)) (X := (15685938892291/100000000000000 : ℝ)) (Y := (21078519295023/25000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992476737/1000000000 : ℝ) ^ p + (460641729/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992476737/1000000000 : ℝ)) (y := (460641729/500000000 : ℝ)) (X := (21078519295023/25000000000000 : ℝ)) (Y := (15685938892291/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (382752039/200000000 : ℝ)) (τ := (460641729/500000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784027216/832124977 : ℝ) ^ p + (821085021/832124977 : ℝ) ^ p := by
    exact cert_lt (x := (784027216/832124977 : ℝ)) (y := (821085021/832124977 : ℝ)) (X := (1628035796789/6250000000000 : ℝ)) (Y := (14790285688821/20000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (460641729/500000000 : ℝ)) (n' := (832124977/1000000000 : ℝ)) (Ab := (49001701/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (921283459/1000000000 : ℝ) ^ p + (992476737/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921283459/1000000000 : ℝ)) (y := (992476737/1000000000 : ℝ)) (X := (980371204811/6250000000000 : ℝ)) (Y := (21078519295023/25000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992476737/1000000000 : ℝ) ^ p + (921283459/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992476737/1000000000 : ℝ)) (y := (921283459/1000000000 : ℝ)) (X := (21078519295023/25000000000000 : ℝ)) (Y := (980371204811/6250000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (784027217/832124978 : ℝ) ^ p + (410542511/416062489 : ℝ) ^ p := by
    exact cert_lt (x := (784027217/832124978 : ℝ)) (y := (410542511/416062489 : ℝ)) (X := (26048572792013/100000000000000 : ℝ)) (Y := (36975714235551/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1650576292/1806990035 : ℝ) ^ p + (1795950079/1806990035 : ℝ) ^ p := by
    exact cert_lt (x := (1650576292/1806990035 : ℝ)) (y := (1795950079/1806990035 : ℝ)) (X := (6465174608077/50000000000000 : ℝ)) (Y := (87069651134273/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108324274/1193009965 : ℝ) ^ p + (1181970009/1193009965 : ℝ) ^ p := by
    exact cert_lt (x := (1108324274/1193009965 : ℝ)) (y := (1181970009/1193009965 : ℝ)) (X := (4736467414643/25000000000000 : ℝ)) (Y := (81054130781519/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992476737/1000000000 : ℝ)) (U := (238601993/200000000 : ℝ)) (Ab := (412644073/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ)) (Ab := (554162137/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab050 (p : ℝ) (hpa : (361/16 : ℝ) ≤ p) (hpb : p ≤ (723/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (238601993/200000000 : ℝ)) ∧ coordinateBox (903/2000 : ℝ) (2771/2500 : ℝ) (3833/5000 : ℝ) (11841/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (6323371517353/3942120000000 : ℝ) ≤ X j i + X k i) ∧
    (57131799704341/9855300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (121218237/125000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(361/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (121218237/125000000 : ℝ))
      (by norm_num) 16 361 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(361/16 : ℝ)) ≤ (969745897/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969745897/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 361 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(723/32 : ℝ)) ≤ (969787103/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969787103/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 723 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (527551819709/24638250000000 : ℝ) (2759989/250000000 : ℝ) (2000000295659/9855300000000 : ℝ) (3033/2500 : ℝ) (969787103/500000000 : ℝ) (121218237/125000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (361/16 : ℝ)) (β := (723/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (527551819709/24638250000000 : ℝ)) (δ := (2759989/250000000 : ℝ)) (h := (2000000295659/9855300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (121218237/125000000 : ℝ)) (thia := (969745897/1000000000 : ℝ)) (thib := (969787103/1000000000 : ℝ))
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
  have hh := contract21_slab050 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 51, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab051 (p : ℝ) (hpa : (723/32 : ℝ) ≤ p) (hpb : p ≤ (181/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527457192449/24672375000000 : ℝ) (68889/6250000 : ℝ) (4000000592137/19737900000000 : ℝ) (3033/2500 : ℝ) (484914099/250000000 : ℝ) (484893551/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193022531/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2217/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(4517/10000 : ℝ)
      else (1917/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527457192449/24672375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (68889/6250000 : ℝ) := by norm_num
  have pc0 : 1 < (915343521/1000000000 : ℝ) ^ p + (993602527/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915343521/1000000000 : ℝ)) (y := (993602527/1000000000 : ℝ)) (X := (1689470230819/12500000000000 : ℝ)) (Y := (17296851117049/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993602527/1000000000 : ℝ) ^ p + (915343521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993602527/1000000000 : ℝ)) (y := (915343521/1000000000 : ℝ)) (X := (17296851117049/20000000000000 : ℝ)) (Y := (1689470230819/12500000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (14913641/7812500 : ℝ)) (τ := (915343521/1000000000 : ℝ)) (σ := (993602527/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (777648774/825025349 : ℝ) ^ p + (814003109/825025349 : ℝ) ^ p := by
    exact cert_lt (x := (777648774/825025349 : ℝ)) (y := (814003109/825025349 : ℝ)) (X := (6559096407611/25000000000000 : ℝ)) (Y := (147527231501/200000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915343521/1000000000 : ℝ)) (n' := (825025349/1000000000 : ℝ)) (Ab := (388824387/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46056073/50000000 : ℝ) ^ p + (124067533/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (46056073/50000000 : ℝ)) (y := (124067533/125000000 : ℝ)) (X := (15583674676603/100000000000000 : ℝ)) (Y := (8441634099341/10000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124067533/125000000 : ℝ) ^ p + (46056073/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (124067533/125000000 : ℝ)) (y := (46056073/50000000 : ℝ)) (X := (8441634099341/10000000000000 : ℝ)) (Y := (15583674676603/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (478415431/250000000 : ℝ)) (τ := (46056073/50000000 : ℝ)) (σ := (124067533/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (783882028/831901333 : ℝ) ^ p + (820879093/831901333 : ℝ) ^ p := by
    exact cert_lt (x := (783882028/831901333 : ℝ)) (y := (820879093/831901333 : ℝ)) (X := (26049376090589/100000000000000 : ℝ)) (Y := (14790125015027/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46056073/50000000 : ℝ)) (n' := (831901333/1000000000 : ℝ)) (Ab := (195970507/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (921389067/1000000000 : ℝ) ^ p + (496243417/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (921389067/1000000000 : ℝ)) (y := (496243417/500000000 : ℝ)) (X := (1568642988699/10000000000000 : ℝ)) (Y := (84313586839053/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496243417/500000000 : ℝ) ^ p + (921389067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496243417/500000000 : ℝ)) (y := (921389067/1000000000 : ℝ)) (X := (84313586839053/100000000000000 : ℝ)) (Y := (1568642988699/10000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1913875901/1000000000 : ℝ)) (τ := (921389067/1000000000 : ℝ)) (σ := (496243417/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784169740/832218773 : ℝ) ^ p + (821196533/832218773 : ℝ) ^ p := by
    exact cert_lt (x := (784169740/832218773 : ℝ)) (y := (821196533/832218773 : ℝ)) (X := (13020403034991/50000000000000 : ℝ)) (Y := (14791838969549/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (921389067/1000000000 : ℝ)) (n' := (832218773/1000000000 : ℝ)) (Ab := (39208487/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921401327/1000000000 : ℝ) ^ p + (124060547/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (921401327/1000000000 : ℝ)) (y := (124060547/125000000 : ℝ)) (X := (3922788234401/25000000000000 : ℝ)) (Y := (42154431301183/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124060547/125000000 : ℝ) ^ p + (921401327/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124060547/125000000 : ℝ)) (y := (921401327/1000000000 : ℝ)) (X := (42154431301183/50000000000000 : ℝ)) (Y := (3922788234401/25000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1913885703/1000000000 : ℝ)) (τ := (921401327/1000000000 : ℝ)) (σ := (124060547/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784182919/832233314 : ℝ) ^ p + (410605537/416116657 : ℝ) ^ p := by
    exact cert_lt (x := (784182919/832233314 : ℝ)) (y := (410605537/416116657 : ℝ)) (X := (26040413537843/100000000000000 : ℝ)) (Y := (73959587270153/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921401327/1000000000 : ℝ)) (n' := (416116657/500000000 : ℝ)) (Ab := (784182919/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (28793809/31250000 : ℝ) ^ p + (124060533/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (28793809/31250000 : ℝ)) (y := (124060533/125000000 : ℝ)) (X := (7845684545069/50000000000000 : ℝ)) (Y := (16861729469237/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124060533/125000000 : ℝ) ^ p + (28793809/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (124060533/125000000 : ℝ)) (y := (28793809/31250000 : ℝ)) (X := (16861729469237/20000000000000 : ℝ)) (Y := (7845684545069/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239235769/125000000 : ℝ)) (τ := (28793809/31250000 : ℝ)) (σ := (124060533/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784183522/832233979 : ℝ) ^ p + (821211739/832233979 : ℝ) ^ p := by
    exact cert_lt (x := (784183522/832233979 : ℝ)) (y := (821211739/832233979 : ℝ)) (X := (26040395803117/100000000000000 : ℝ)) (Y := (73959605216431/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (28793809/31250000 : ℝ)) (n' := (832233979/1000000000 : ℝ)) (Ab := (392091761/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (921401913/1000000000 : ℝ) ^ p + (992484259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921401913/1000000000 : ℝ)) (y := (992484259/1000000000 : ℝ)) (X := (1569137872267/10000000000000 : ℝ)) (Y := (42154318868273/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992484259/1000000000 : ℝ) ^ p + (921401913/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992484259/1000000000 : ℝ)) (y := (921401913/1000000000 : ℝ)) (X := (42154318868273/50000000000000 : ℝ)) (Y := (1569137872267/10000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478471543/250000000 : ℝ)) (τ := (921401913/1000000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784183549/832234009 : ℝ) ^ p + (821211769/832234009 : ℝ) ^ p := by
    exact cert_lt (x := (784183549/832234009 : ℝ)) (y := (821211769/832234009 : ℝ)) (X := (13020197425267/50000000000000 : ℝ)) (Y := (73959606026037/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (921401913/1000000000 : ℝ)) (n' := (832234009/1000000000 : ℝ)) (Ab := (784183549/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (460700957/500000000 : ℝ) ^ p + (992484259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460700957/500000000 : ℝ)) (y := (992484259/1000000000 : ℝ)) (X := (15691379107971/100000000000000 : ℝ)) (Y := (42154318868273/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992484259/1000000000 : ℝ) ^ p + (460700957/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992484259/1000000000 : ℝ)) (y := (460700957/500000000 : ℝ)) (X := (42154318868273/50000000000000 : ℝ)) (Y := (15691379107971/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (78418355/83223401 : ℝ) ^ p + (82121177/83223401 : ℝ) ^ p := by
    exact cert_lt (x := (78418355/83223401 : ℝ)) (y := (82121177/83223401 : ℝ)) (X := (3255049361739/12500000000000 : ℝ)) (Y := (73959606053023/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1650756146/1806977469 : ℝ) ^ p + (598651743/602325823 : ℝ) ^ p := by
    exact cert_lt (x := (1650756146/1806977469 : ℝ)) (y := (598651743/602325823 : ℝ)) (X := (12927675614201/100000000000000 : ℝ)) (Y := (87072324702549/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108438021/1193022531 : ℝ) ^ p + (394000097/397674177 : ℝ) ^ p := by
    exact cert_lt (x := (1108438021/1193022531 : ℝ)) (y := (394000097/397674177 : ℝ)) (X := (378835034317/2000000000000 : ℝ)) (Y := (40529124446547/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992484259/1000000000 : ℝ)) (U := (1193022531/1000000000 : ℝ)) (Ab := (825378073/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ)) (Ab := (1108438021/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab051 (p : ℝ) (hpa : (723/32 : ℝ) ≤ p) (hpb : p ≤ (181/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193022531/1000000000 : ℝ)) ∧ coordinateBox (4517/10000 : ℝ) (2217/2000 : ℝ) (1917/2500 : ℝ) (11841/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (316659403879961/197379000000000 : ℝ) ≤ X j i + X k i) ∧
    (114427399407863/19737900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (484893551/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(723/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (484893551/500000000 : ℝ))
      (by norm_num) 32 723 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(723/32 : ℝ)) ≤ (969787103/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969787103/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 723 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(181/8 : ℝ)) ≤ (484914099/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (484914099/500000000 : ℝ))
      (by norm_num) (by norm_num) 8 181 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (527457192449/24672375000000 : ℝ) (68889/6250000 : ℝ) (4000000592137/19737900000000 : ℝ) (3033/2500 : ℝ) (484914099/250000000 : ℝ) (484893551/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (723/32 : ℝ)) (β := (181/8 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (527457192449/24672375000000 : ℝ)) (δ := (68889/6250000 : ℝ)) (h := (4000000592137/19737900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (484893551/500000000 : ℝ)) (thia := (969787103/1000000000 : ℝ)) (thib := (484914099/500000000 : ℝ))
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
  have hh := contract21_slab051 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 52, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab052 (p : ℝ) (hpa : (181/8 : ℝ) ≤ p) (hpb : p ≤ (725/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527362984517/24706500000000 : ℝ) (1375573/125000000 : ℝ) (1000000148239/4941300000000 : ℝ) (3033/2500 : ℝ) (969869181/500000000 : ℝ) (969828197/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193035119/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5543/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4519/10000 : ℝ)
      else (767/1000 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527362984517/24706500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1375573/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (457733309/500000000 : ℝ) ^ p + (993609387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (457733309/500000000 : ℝ)) (y := (993609387/1000000000 : ℝ)) (X := (844973703961/6250000000000 : ℝ)) (Y := (86480438148751/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993609387/1000000000 : ℝ) ^ p + (457733309/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993609387/1000000000 : ℝ)) (y := (457733309/500000000 : ℝ)) (X := (86480438148751/100000000000000 : ℝ)) (Y := (844973703961/6250000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381815201/200000000 : ℝ)) (τ := (457733309/500000000 : ℝ)) (σ := (993609387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (388905212/412570613 : ℝ) ^ p + (407068321/412570613 : ℝ) ^ p := by
    exact cert_lt (x := (388905212/412570613 : ℝ)) (y := (407068321/412570613 : ℝ)) (X := (26227966796301/100000000000000 : ℝ)) (Y := (73772034032797/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457733309/500000000 : ℝ)) (n' := (412570613/500000000 : ℝ)) (Ab := (97226303/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921240323/1000000000 : ℝ) ^ p + (992547637/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921240323/1000000000 : ℝ)) (y := (992547637/1000000000 : ℝ)) (X := (1558922041323/10000000000000 : ℝ)) (Y := (21102698940919/25000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992547637/1000000000 : ℝ) ^ p + (921240323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992547637/1000000000 : ℝ)) (y := (921240323/1000000000 : ℝ)) (X := (21102698940919/25000000000000 : ℝ)) (Y := (1558922041323/10000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (47844699/25000000 : ℝ)) (τ := (921240323/1000000000 : ℝ)) (σ := (992547637/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784038753/832010948 : ℝ) ^ p + (205251591/208002737 : ℝ) ^ p := by
    exact cert_lt (x := (784038753/832010948 : ℝ)) (y := (205251591/208002737 : ℝ)) (X := (26041204172357/100000000000000 : ℝ)) (Y := (73958797169251/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921240323/1000000000 : ℝ)) (n' := (208002737/250000000 : ℝ)) (Ab := (784038753/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (921507217/1000000000 : ℝ) ^ p + (992494333/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921507217/1000000000 : ℝ)) (y := (992494333/1000000000 : ℝ)) (X := (490370819831/3125000000000 : ℝ)) (Y := (4215407489319/5000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992494333/1000000000 : ℝ) ^ p + (921507217/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992494333/1000000000 : ℝ)) (y := (921507217/1000000000 : ℝ)) (X := (4215407489319/5000000000000 : ℝ)) (Y := (490370819831/3125000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (38280031/20000000 : ℝ)) (τ := (921507217/1000000000 : ℝ)) (σ := (992494333/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784325683/832327487 : ℝ) ^ p + (821322903/832327487 : ℝ) ^ p := by
    exact cert_lt (x := (784325683/832327487 : ℝ)) (y := (821322903/832327487 : ℝ)) (X := (26032661802933/100000000000000 : ℝ)) (Y := (73967339215817/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (921507217/1000000000 : ℝ)) (n' := (832327487/1000000000 : ℝ)) (Ab := (784325683/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921519419/1000000000 : ℝ) ^ p + (992491887/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921519419/1000000000 : ℝ)) (y := (992491887/1000000000 : ℝ)) (X := (7848287229613/50000000000000 : ℝ)) (Y := (84303442458881/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992491887/1000000000 : ℝ) ^ p + (921519419/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992491887/1000000000 : ℝ)) (y := (921519419/1000000000 : ℝ)) (X := (84303442458881/100000000000000 : ℝ)) (Y := (7848287229613/50000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957005653/500000000 : ℝ)) (τ := (921519419/1000000000 : ℝ)) (σ := (992491887/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784338799/832341956 : ℝ) ^ p + (205334343/208085489 : ℝ) ^ p := by
    exact cert_lt (x := (784338799/832341956 : ℝ)) (y := (205334343/208085489 : ℝ)) (X := (26032271871987/100000000000000 : ℝ)) (Y := (36983864770039/50000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921519419/1000000000 : ℝ)) (n' := (208085489/250000000 : ℝ)) (Ab := (784338799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921519977/1000000000 : ℝ) ^ p + (39699671/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (921519977/1000000000 : ℝ)) (y := (39699671/40000000 : ℝ)) (X := (15696789799603/100000000000000 : ℝ)) (Y := (84303226920873/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39699671/40000000 : ℝ) ^ p + (921519977/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39699671/40000000 : ℝ)) (y := (921519977/1000000000 : ℝ)) (X := (84303226920873/100000000000000 : ℝ)) (Y := (15696789799603/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239251469/125000000 : ℝ)) (τ := (921519977/1000000000 : ℝ)) (σ := (39699671/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784339399/832342618 : ℝ) ^ p + (410669017/416171309 : ℝ) ^ p := by
    exact cert_lt (x := (784339399/832342618 : ℝ)) (y := (410669017/416171309 : ℝ)) (X := (6508063489899/25000000000000 : ℝ)) (Y := (36983873699151/50000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921519977/1000000000 : ℝ)) (n' := (416171309/500000000 : ℝ)) (Ab := (784339399/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (460760001/500000000 : ℝ) ^ p + (99249177/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (460760001/500000000 : ℝ)) (y := (99249177/100000000 : ℝ)) (X := (3139359889507/20000000000000 : ℝ)) (Y := (84303217298653/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99249177/100000000 : ℝ) ^ p + (460760001/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99249177/100000000 : ℝ)) (y := (460760001/500000000 : ℝ)) (X := (84303217298653/100000000000000 : ℝ)) (Y := (3139359889507/20000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478502943/250000000 : ℝ)) (τ := (460760001/500000000 : ℝ)) (σ := (99249177/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392169713/416171324 : ℝ) ^ p + (102667258/104042831 : ℝ) ^ p := by
    exact cert_lt (x := (392169713/416171324 : ℝ)) (y := (102667258/104042831 : ℝ)) (X := (13016126502367/50000000000000 : ℝ)) (Y := (73967748207587/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (460760001/500000000 : ℝ)) (n' := (104042831/125000000 : ℝ)) (Ab := (392169713/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (230380001/250000000 : ℝ) ^ p + (992491769/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230380001/250000000 : ℝ)) (y := (992491769/1000000000 : ℝ)) (X := (1569680021937/10000000000000 : ℝ)) (Y := (84303215374209/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992491769/1000000000 : ℝ) ^ p + (230380001/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992491769/1000000000 : ℝ)) (y := (230380001/250000000 : ℝ)) (X := (84303215374209/100000000000000 : ℝ)) (Y := (1569680021937/10000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (130723238/138723775 : ℝ) ^ p + (410669033/416171325 : ℝ) ^ p := by
    exact cert_lt (x := (130723238/138723775 : ℝ)) (y := (410669033/416171325 : ℝ)) (X := (26032253091469/100000000000000 : ℝ)) (Y := (73967748261539/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (550311846/602321627 : ℝ) ^ p + (1795960297/1806964881 : ℝ) ^ p := by
    exact cert_lt (x := (550311846/602321627 : ℝ)) (y := (1795960297/1806964881 : ℝ)) (X := (2585002871503/20000000000000 : ℝ)) (Y := (21768746457181/25000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108551560/1193035119 : ℝ) ^ p + (1182030535/1193035119 : ℝ) ^ p := by
    exact cert_lt (x := (1108551560/1193035119 : ℝ)) (y := (1182030535/1193035119 : ℝ)) (X := (18937650780571/100000000000000 : ℝ)) (Y := (20265587434503/25000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992491769/1000000000 : ℝ)) (U := (1193035119/1000000000 : ℝ)) (Ab := (825467769/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ)) (Ab := (27713789/25000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab052 (p : ℝ) (hpa : (181/8 : ℝ) ≤ p) (hpb : p ≤ (725/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193035119/1000000000 : ℝ)) ∧ coordinateBox (4519/10000 : ℝ) (5543/5000 : ℝ) (767/1000 : ℝ) (11841/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (79287555170723/49413000000000 : ℝ) ≤ X j i + X k i) ∧
    (28647799851761/4941300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (969828197/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(181/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (969828197/1000000000 : ℝ))
      (by norm_num) 8 181 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(181/8 : ℝ)) ≤ (484914099/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (484914099/500000000 : ℝ))
      (by norm_num) (by norm_num) 8 181 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(725/32 : ℝ)) ≤ (969869181/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969869181/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 725 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (527362984517/24706500000000 : ℝ) (1375573/125000000 : ℝ) (1000000148239/4941300000000 : ℝ) (3033/2500 : ℝ) (969869181/500000000 : ℝ) (969828197/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (181/8 : ℝ)) (β := (725/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (527362984517/24706500000000 : ℝ)) (δ := (1375573/125000000 : ℝ)) (h := (1000000148239/4941300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (969828197/1000000000 : ℝ)) (thia := (484914099/500000000 : ℝ)) (thib := (969869181/1000000000 : ℝ))
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
  have hh := contract21_slab052 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 53, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab053 (p : ℝ) (hpa : (725/32 : ℝ) ≤ p) (hpb : p ≤ (363/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (42181518343/1979250000000 : ℝ) (5493491/500000000 : ℝ) (160000023751/791700000000 : ℝ) (3033/2500 : ℝ) (242477513/125000000 : ℝ) (48493459/50000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298261927/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11087/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4521/10000 : ℝ)
      else (959/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (42181518343/1979250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5493491/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (915589363/1000000000 : ℝ) ^ p + (124202029/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (915589363/1000000000 : ℝ)) (y := (124202029/125000000 : ℝ)) (X := (2704677582929/20000000000000 : ℝ)) (Y := (43238314242269/50000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124202029/125000000 : ℝ) ^ p + (915589363/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124202029/125000000 : ℝ)) (y := (915589363/1000000000 : ℝ)) (X := (43238314242269/50000000000000 : ℝ)) (Y := (2704677582929/20000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381841119/200000000 : ℝ)) (τ := (915589363/1000000000 : ℝ)) (σ := (124202029/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (155594325/165051346 : ℝ) ^ p + (407134874/412628365 : ℝ) ^ p := by
    exact cert_lt (x := (155594325/165051346 : ℝ)) (y := (407134874/412628365 : ℝ)) (X := (2621957270841/10000000000000 : ℝ)) (Y := (36890214406941/50000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915589363/1000000000 : ℝ)) (n' := (82525673/100000000 : ℝ)) (Ab := (6223773/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921358829/1000000000 : ℝ) ^ p + (992554997/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921358829/1000000000 : ℝ)) (y := (992554997/1000000000 : ℝ)) (X := (243667982953/1562500000000 : ℝ)) (Y := (84405264898711/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992554997/1000000000 : ℝ) ^ p + (921358829/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992554997/1000000000 : ℝ)) (y := (921358829/1000000000 : ℝ)) (X := (84405264898711/100000000000000 : ℝ)) (Y := (243667982953/1562500000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956956913/500000000 : ℝ)) (τ := (921358829/1000000000 : ℝ)) (σ := (992554997/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (392097511/416060094 : ℝ) ^ p + (410566603/416060094 : ℝ) ^ p := by
    exact cert_lt (x := (392097511/416060094 : ℝ)) (y := (410566603/416060094 : ℝ)) (X := (6508263773853/25000000000000 : ℝ)) (Y := (18491736521849/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921358829/1000000000 : ℝ)) (n' := (208030047/250000000 : ℝ)) (Ab := (392097511/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (921625011/1000000000 : ℝ) ^ p + (49625091/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (921625011/1000000000 : ℝ)) (y := (49625091/50000000 : ℝ)) (X := (15697286843351/100000000000000 : ℝ)) (Y := (8430272966091/10000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (49625091/50000000 : ℝ) ^ p + (921625011/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49625091/50000000 : ℝ)) (y := (921625011/1000000000 : ℝ)) (X := (8430272966091/10000000000000 : ℝ)) (Y := (15697286843351/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914126831/1000000000 : ℝ)) (τ := (921625011/1000000000 : ℝ)) (σ := (49625091/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (196120293/208108957 : ℝ) ^ p + (410724423/416217914 : ℝ) ^ p := by
    exact cert_lt (x := (196120293/208108957 : ℝ)) (y := (410724423/416217914 : ℝ)) (X := (6506135160767/25000000000000 : ℝ)) (Y := (14795092098433/20000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (921625011/1000000000 : ℝ)) (n' := (208108957/250000000 : ℝ)) (Ab := (196120293/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (460818579/500000000 : ℝ) ^ p + (124062423/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (460818579/500000000 : ℝ)) (y := (124062423/125000000 : ℝ)) (X := (15701981329769/100000000000000 : ℝ)) (Y := (4214901772449/5000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124062423/125000000 : ℝ) ^ p + (460818579/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124062423/125000000 : ℝ)) (y := (460818579/500000000 : ℝ)) (X := (4214901772449/5000000000000 : ℝ)) (Y := (15701981329769/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957068271/500000000 : ℝ)) (τ := (460818579/500000000 : ℝ)) (σ := (124062423/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (130749038/138741705 : ℝ) ^ p + (410731624/416225115 : ℝ) ^ p := by
    exact cert_lt (x := (130749038/138741705 : ℝ)) (y := (410731624/416225115 : ℝ)) (X := (26024152038361/100000000000000 : ℝ)) (Y := (18493962213787/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (460818579/500000000 : ℝ)) (n' := (83245023/100000000 : ℝ)) (Ab := (196123557/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921637713/1000000000 : ℝ) ^ p + (124062409/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (921637713/1000000000 : ℝ)) (y := (124062409/125000000 : ℝ)) (X := (15702195854291/100000000000000 : ℝ)) (Y := (2634306863411/3125000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124062409/125000000 : ℝ) ^ p + (921637713/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124062409/125000000 : ℝ)) (y := (921637713/1000000000 : ℝ)) (X := (2634306863411/3125000000000 : ℝ)) (Y := (15702195854291/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (382827397/200000000 : ℝ)) (τ := (921637713/1000000000 : ℝ)) (σ := (124062409/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784494825/832450888 : ℝ) ^ p + (4066653/4121044 : ℝ) ^ p := by
    exact cert_lt (x := (784494825/832450888 : ℝ)) (y := (4066653/4121044 : ℝ)) (X := (13012067328819/50000000000000 : ℝ)) (Y := (73975866598439/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921637713/1000000000 : ℝ)) (n' := (104056361/125000000 : ℝ)) (Ab := (31379793/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (921637739/1000000000 : ℝ) ^ p + (992499267/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921637739/1000000000 : ℝ)) (y := (992499267/1000000000 : ℝ)) (X := (15702205904157/100000000000000 : ℝ)) (Y := (84297809994351/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992499267/1000000000 : ℝ) ^ p + (921637739/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992499267/1000000000 : ℝ)) (y := (921637739/1000000000 : ℝ)) (X := (84297809994351/100000000000000 : ℝ)) (Y := (15702205904157/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392247426/416225459 : ℝ) ^ p + (410731968/416225459 : ℝ) ^ p := by
    exact cert_lt (x := (392247426/416225459 : ℝ)) (y := (410731968/416225459 : ℝ)) (X := (26024133700499/100000000000000 : ℝ)) (Y := (18493966851851/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (825557227/903476146 : ℝ) ^ p + (897982655/903476146 : ℝ) ^ p := by
    exact cert_lt (x := (825557227/903476146 : ℝ)) (y := (897982655/903476146 : ℝ)) (X := (6461179617289/50000000000000 : ℝ)) (Y := (87077640980407/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1108664851/1193047708 : ℝ) ^ p + (591030363/596523854 : ℝ) ^ p := by
    exact cert_lt (x := (1108664851/1193047708 : ℝ)) (y := (591030363/596523854 : ℝ)) (X := (18933558546649/100000000000000 : ℝ)) (Y := (20266610491329/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992499267/1000000000 : ℝ)) (U := (298261927/250000000 : ℝ)) (Ab := (825557227/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ)) (Ab := (1108664851/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab053 (p : ℝ) (hpa : (725/32 : ℝ) ≤ p) (hpb : p ≤ (363/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (298261927/250000000 : ℝ)) ∧ coordinateBox (4521/10000 : ℝ) (11087/10000 : ℝ) (959/1250 : ℝ) (11841/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (6352820608297/3958500000000 : ℝ) ≤ X j i + X k i) ∧
    (4590199976249/791700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (48493459/50000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(725/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (48493459/50000000 : ℝ))
      (by norm_num) 32 725 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(725/32 : ℝ)) ≤ (969869181/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969869181/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 725 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(363/16 : ℝ)) ≤ (242477513/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (242477513/250000000 : ℝ))
      (by norm_num) (by norm_num) 16 363 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (42181518343/1979250000000 : ℝ) (5493491/500000000 : ℝ) (160000023751/791700000000 : ℝ) (3033/2500 : ℝ) (242477513/125000000 : ℝ) (48493459/50000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (725/32 : ℝ)) (β := (363/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (42181518343/1979250000000 : ℝ)) (δ := (5493491/500000000 : ℝ)) (h := (160000023751/791700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (48493459/50000000 : ℝ)) (thia := (969869181/1000000000 : ℝ)) (thib := (242477513/250000000 : ℝ))
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
  have hh := contract21_slab053 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 54, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab054 (p : ℝ) (hpa : (363/16 : ℝ) ≤ p) (hpb : p ≤ (727/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1054350215929/49549500000000 : ℝ) (10969433/1000000000 : ℝ) (2000000297297/9909900000000 : ℝ) (3033/2500 : ℝ) (969950813/500000000 : ℝ) (969910051/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149132537/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(693/625 : ℝ) ≤ X j i ∧ X j i ≤ -(4523/10000 : ℝ)
      else (3837/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1054350215929/49549500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10969433/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (457855879/500000000 : ℝ) ^ p + (993623063/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (457855879/500000000 : ℝ)) (y := (993623063/1000000000 : ℝ)) (X := (6763594001043/50000000000000 : ℝ)) (Y := (432364142233/500000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993623063/1000000000 : ℝ) ^ p + (457855879/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993623063/1000000000 : ℝ)) (y := (457855879/500000000 : ℝ)) (X := (432364142233/500000000000 : ℝ)) (Y := (6763594001043/50000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1909334821/1000000000 : ℝ)) (τ := (457855879/500000000 : ℝ)) (σ := (993623063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778132373/825371862 : ℝ) ^ p + (814402429/825371862 : ℝ) ^ p := by
    exact cert_lt (x := (778132373/825371862 : ℝ)) (y := (814402429/825371862 : ℝ)) (X := (26211199304917/100000000000000 : ℝ)) (Y := (73788801739121/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457855879/500000000 : ℝ)) (n' := (412685931/500000000 : ℝ)) (Ab := (778132373/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921476983/1000000000 : ℝ) ^ p + (124070293/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (921476983/1000000000 : ℝ)) (y := (124070293/125000000 : ℝ)) (X := (15600267532841/100000000000000 : ℝ)) (Y := (84399748292229/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124070293/125000000 : ℝ) ^ p + (921476983/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124070293/125000000 : ℝ)) (y := (921476983/1000000000 : ℝ)) (X := (84399748292229/100000000000000 : ℝ)) (Y := (15600267532841/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1914039327/1000000000 : ℝ)) (τ := (921476983/1000000000 : ℝ)) (σ := (124070293/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (392175421/416114531 : ℝ) ^ p + (821259629/832229062 : ℝ) ^ p := by
    exact cert_lt (x := (392175421/416114531 : ℝ)) (y := (821259629/832229062 : ℝ)) (X := (26024927455549/100000000000000 : ℝ)) (Y := (73975073680111/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921476983/1000000000 : ℝ)) (n' := (416114531/500000000 : ℝ)) (Ab := (392175421/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115217807/125000000 : ℝ) ^ p + (992509293/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115217807/125000000 : ℝ)) (y := (992509293/1000000000 : ℝ)) (X := (15702693866383/100000000000000 : ℝ)) (Y := (84297322504777/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992509293/1000000000 : ℝ) ^ p + (115217807/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992509293/1000000000 : ℝ)) (y := (115217807/125000000 : ℝ)) (X := (84297322504777/100000000000000 : ℝ)) (Y := (15702693866383/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914251749/1000000000 : ℝ)) (τ := (115217807/125000000 : ℝ)) (σ := (992509293/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (392318107/416271903 : ℝ) ^ p + (821574373/832543806 : ℝ) ^ p := by
    exact cert_lt (x := (392318107/416271903 : ℝ)) (y := (821574373/832543806 : ℝ)) (X := (26016440477107/100000000000000 : ℝ)) (Y := (73983560553531/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115217807/125000000 : ℝ)) (n' := (416271903/500000000 : ℝ)) (Ab := (392318107/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921754549/1000000000 : ℝ) ^ p + (992506867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921754549/1000000000 : ℝ)) (y := (992506867/1000000000 : ℝ)) (X := (7853687467103/50000000000000 : ℝ)) (Y := (10536580182359/12500000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992506867/1000000000 : ℝ) ^ p + (921754549/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992506867/1000000000 : ℝ)) (y := (921754549/1000000000 : ℝ)) (X := (10536580182359/12500000000000 : ℝ)) (Y := (7853687467103/50000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239282677/125000000 : ℝ)) (τ := (921754549/1000000000 : ℝ)) (σ := (992506867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784649211/832558141 : ℝ) ^ p + (821588708/832558141 : ℝ) ^ p := by
    exact cert_lt (x := (784649211/832558141 : ℝ)) (y := (821588708/832558141 : ℝ)) (X := (5203210792549/20000000000000 : ℝ)) (Y := (73983946957133/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921754549/1000000000 : ℝ)) (n' := (832558141/1000000000 : ℝ)) (Ab := (784649211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (9217551/10000000 : ℝ) ^ p + (248126689/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (9217551/10000000 : ℝ)) (y := (248126689/250000000 : ℝ)) (X := (15707588252043/100000000000000 : ℝ)) (Y := (42146213643353/50000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248126689/250000000 : ℝ) ^ p + (9217551/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (248126689/250000000 : ℝ)) (y := (9217551/10000000 : ℝ)) (X := (42146213643353/50000000000000 : ℝ)) (Y := (15707588252043/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (59820683/31250000 : ℝ)) (τ := (9217551/10000000 : ℝ)) (σ := (248126689/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784649803/832558794 : ℝ) ^ p + (821589361/832558794 : ℝ) ^ p := by
    exact cert_lt (x := (784649803/832558794 : ℝ)) (y := (821589361/832558794 : ℝ)) (X := (13008018159239/50000000000000 : ℝ)) (Y := (14796792911729/20000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (9217551/10000000 : ℝ)) (n' := (416279397/500000000 : ℝ)) (Ab := (784649803/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (7374041/8000000 : ℝ) ^ p + (992506751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7374041/8000000 : ℝ)) (y := (992506751/1000000000 : ℝ)) (X := (1963449741347/12500000000000 : ℝ)) (Y := (21073104409831/25000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992506751/1000000000 : ℝ) ^ p + (7374041/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992506751/1000000000 : ℝ)) (y := (7374041/8000000 : ℝ)) (X := (21073104409831/25000000000000 : ℝ)) (Y := (1963449741347/12500000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478565469/250000000 : ℝ)) (τ := (7374041/8000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784649831/832558824 : ℝ) ^ p + (821589391/832558824 : ℝ) ^ p := by
    exact cert_lt (x := (784649831/832558824 : ℝ)) (y := (821589391/832558824 : ℝ)) (X := (2601603611233/10000000000000 : ℝ)) (Y := (7398396536729/10000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (7374041/8000000 : ℝ)) (n' := (104069853/125000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (460877563/500000000 : ℝ) ^ p + (992506751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460877563/500000000 : ℝ)) (y := (992506751/1000000000 : ℝ)) (X := (628303932717/4000000000000 : ℝ)) (Y := (21073104409831/25000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992506751/1000000000 : ℝ) ^ p + (460877563/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992506751/1000000000 : ℝ)) (y := (460877563/500000000 : ℝ)) (X := (21073104409831/25000000000000 : ℝ)) (Y := (628303932717/4000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (112092833/118936975 : ℝ) ^ p + (821589392/832558825 : ℝ) ^ p := by
    exact cert_lt (x := (112092833/118936975 : ℝ)) (y := (821589392/832558825 : ℝ)) (X := (3252004425301/12500000000000 : ℝ)) (Y := (18495991348561/25000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (412823223/451734926 : ℝ) ^ p + (1795970271/1806939704 : ℝ) ^ p := by
    exact cert_lt (x := (412823223/451734926 : ℝ)) (y := (1795970271/1806939704 : ℝ)) (X := (12919709226957/100000000000000 : ℝ)) (Y := (5442518189209/6250000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (554388945/596530148 : ℝ) ^ p + (1182090863/1193060296 : ℝ) ^ p := by
    exact cert_lt (x := (554388945/596530148 : ℝ)) (y := (1182090863/1193060296 : ℝ)) (X := (4732368447961/25000000000000 : ℝ)) (Y := (8107052675829/10000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992506751/1000000000 : ℝ)) (U := (149132537/125000000 : ℝ)) (Ab := (412823223/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ)) (Ab := (110877789/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab054 (p : ℝ) (hpa : (363/16 : ℝ) ≤ p) (hpb : p ≤ (727/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (149132537/125000000 : ℝ)) ∧ coordinateBox (4523/10000 : ℝ) (693/625 : ℝ) (3837/5000 : ℝ) (5921/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (79532958367853/49549500000000 : ℝ) ≤ X j i + X k i) ∧
    (57459399702703/9909900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (969910051/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(363/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (969910051/1000000000 : ℝ))
      (by norm_num) 16 363 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(363/16 : ℝ)) ≤ (242477513/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (242477513/250000000 : ℝ))
      (by norm_num) (by norm_num) 16 363 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(727/32 : ℝ)) ≤ (969950813/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969950813/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 727 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (1054350215929/49549500000000 : ℝ) (10969433/1000000000 : ℝ) (2000000297297/9909900000000 : ℝ) (3033/2500 : ℝ) (969950813/500000000 : ℝ) (969910051/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (363/16 : ℝ)) (β := (727/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1054350215929/49549500000000 : ℝ)) (δ := (10969433/1000000000 : ℝ)) (h := (2000000297297/9909900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (969910051/1000000000 : ℝ)) (thia := (242477513/250000000 : ℝ)) (thib := (969950813/1000000000 : ℝ))
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
  have hh := contract21_slab054 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 55, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab055 (p : ℝ) (hpa : (727/32 : ℝ) ≤ p) (hpb : p ≤ (91/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1054163198917/49617750000000 : ℝ) (10951941/1000000000 : ℝ) (4000000595413/19847100000000 : ℝ) (3033/2500 : ℝ) (121248933/62500000 : ℝ) (242487703/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193072899/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11089/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(181/400 : ℝ)
      else (1919/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1054163198917/49617750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10951941/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (457916897/500000000 : ℝ) ^ p + (496814941/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (457916897/500000000 : ℝ)) (y := (496814941/500000000 : ℝ)) (X := (13530976033807/100000000000000 : ℝ)) (Y := (43234520939609/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496814941/500000000 : ℝ) ^ p + (457916897/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496814941/500000000 : ℝ)) (y := (457916897/500000000 : ℝ)) (X := (43234520939609/50000000000000 : ℝ)) (Y := (13530976033807/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (477365919/250000000 : ℝ)) (τ := (457916897/500000000 : ℝ)) (σ := (496814941/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778292668/825486607 : ℝ) ^ p + (74048606/75044237 : ℝ) ^ p := by
    exact cert_lt (x := (778292668/825486607 : ℝ)) (y := (74048606/75044237 : ℝ)) (X := (13101428564727/50000000000000 : ℝ)) (Y := (36898571860721/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457916897/500000000 : ℝ)) (n' := (825486607/1000000000 : ℝ)) (Ab := (194573167/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (115199347/125000000 : ℝ) ^ p + (12407121/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (115199347/125000000 : ℝ)) (y := (12407121/12500000 : ℝ)) (X := (15605766272143/100000000000000 : ℝ)) (Y := (10549281213333/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (12407121/12500000 : ℝ) ^ p + (115199347/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (12407121/12500000 : ℝ)) (y := (115199347/125000000 : ℝ)) (X := (10549281213333/12500000000000 : ℝ)) (Y := (15605766272143/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (239270557/125000000 : ℝ)) (τ := (115199347/125000000 : ℝ)) (σ := (12407121/12500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784506207/832337551 : ℝ) ^ p + (821385610/832337551 : ℝ) ^ p := by
    exact cert_lt (x := (784506207/832337551 : ℝ)) (y := (821385610/832337551 : ℝ)) (X := (26016829946591/100000000000000 : ℝ)) (Y := (73983170807913/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (115199347/125000000 : ℝ)) (n' := (832337551/1000000000 : ℝ)) (Ab := (784506207/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115232443/125000000 : ℝ) ^ p + (496258377/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115232443/125000000 : ℝ)) (y := (496258377/500000000 : ℝ)) (X := (15708083658727/100000000000000 : ℝ)) (Y := (3371677282737/4000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496258377/500000000 : ℝ) ^ p + (115232443/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496258377/500000000 : ℝ)) (y := (115232443/125000000 : ℝ)) (X := (3371677282737/4000000000000 : ℝ)) (Y := (15708083658727/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (957188149/500000000 : ℝ)) (τ := (115232443/125000000 : ℝ)) (σ := (496258377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (392395403/416325702 : ℝ) ^ p + (21069217/21350036 : ℝ) ^ p := by
    exact cert_lt (x := (392395403/416325702 : ℝ)) (y := (21069217/21350036 : ℝ)) (X := (13004185415567/50000000000000 : ℝ)) (Y := (7399163031677/10000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115232443/125000000 : ℝ)) (n' := (208162851/250000000 : ℝ)) (Ab := (392395403/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (46093579/50000000 : ℝ) ^ p + (992514339/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46093579/50000000 : ℝ)) (y := (992514339/1000000000 : ℝ)) (X := (15712750077327/100000000000000 : ℝ)) (Y := (42143633085397/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992514339/1000000000 : ℝ) ^ p + (46093579/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992514339/1000000000 : ℝ)) (y := (46093579/50000000 : ℝ)) (X := (42143633085397/50000000000000 : ℝ)) (Y := (15712750077327/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1914385919/1000000000 : ℝ)) (τ := (46093579/50000000 : ℝ)) (σ := (992514339/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261601247/277555223 : ℝ) ^ p + (24900416/25232293 : ℝ) ^ p := by
    exact cert_lt (x := (261601247/277555223 : ℝ)) (y := (24900416/25232293 : ℝ)) (X := (26007986288941/100000000000000 : ℝ)) (Y := (73992014682169/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (46093579/50000000 : ℝ)) (n' := (832665669/1000000000 : ℝ)) (Ab := (784803741/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921872127/1000000000 : ℝ) ^ p + (992514229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921872127/1000000000 : ℝ)) (y := (992514229/1000000000 : ℝ)) (X := (15712962183499/100000000000000 : ℝ)) (Y := (21071763412829/25000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992514229/1000000000 : ℝ) ^ p + (921872127/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992514229/1000000000 : ℝ)) (y := (921872127/1000000000 : ℝ)) (X := (21071763412829/25000000000000 : ℝ)) (Y := (15712962183499/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (478596589/250000000 : ℝ)) (τ := (921872127/1000000000 : ℝ)) (σ := (992514229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (392402165/416333159 : ℝ) ^ p + (74701307/75696938 : ℝ) ^ p := by
    exact cert_lt (x := (392402165/416333159 : ℝ)) (y := (74701307/75696938 : ℝ)) (X := (6501992294623/25000000000000 : ℝ)) (Y := (36996016084489/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921872127/1000000000 : ℝ)) (n' := (416333159/500000000 : ℝ)) (Ab := (78480433/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (115234019/125000000 : ℝ) ^ p + (62032139/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (115234019/125000000 : ℝ)) (y := (62032139/62500000 : ℝ)) (X := (1571297187763/10000000000000 : ℝ)) (Y := (10535880498919/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (62032139/62500000 : ℝ) ^ p + (115234019/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (62032139/62500000 : ℝ)) (y := (115234019/125000000 : ℝ)) (X := (10535880498919/12500000000000 : ℝ)) (Y := (1571297187763/10000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (239298297/125000000 : ℝ)) (τ := (115234019/125000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (87200484/92518483 : ℝ) ^ p + (273904802/277555449 : ℝ) ^ p := by
    exact cert_lt (x := (87200484/92518483 : ℝ)) (y := (273904802/277555449 : ℝ)) (X := (13003984086731/50000000000000 : ℝ)) (Y := (1849800823759/2500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (115234019/125000000 : ℝ)) (n' := (832666347/1000000000 : ℝ)) (Ab := (196201089/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (921872153/1000000000 : ℝ) ^ p + (62032139/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (921872153/1000000000 : ℝ)) (y := (62032139/62500000 : ℝ)) (X := (3928243066349/25000000000000 : ℝ)) (Y := (10535880498919/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (62032139/62500000 : ℝ) ^ p + (921872153/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62032139/62500000 : ℝ)) (y := (921872153/1000000000 : ℝ)) (X := (10535880498919/12500000000000 : ℝ)) (Y := (3928243066349/25000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (784804357/832666348 : ℝ) ^ p + (821714407/832666348 : ℝ) ^ p := by
    exact cert_lt (x := (784804357/832666348 : ℝ)) (y := (821714407/832666348 : ℝ)) (X := (13003984108399/50000000000000 : ℝ)) (Y := (9249004122163/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1651470866/1806927101 : ℝ) ^ p + (256567880/258132443 : ℝ) ^ p := by
    exact cert_lt (x := (1651470866/1806927101 : ℝ)) (y := (256567880/258132443 : ℝ)) (X := (1614633635993/12500000000000 : ℝ)) (Y := (43541465604793/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108890709/1193072899 : ℝ) ^ p + (1182120958/1193072899 : ℝ) ^ p := by
    exact cert_lt (x := (1108890709/1193072899 : ℝ)) (y := (1182120958/1193072899 : ℝ)) (X := (18925402773153/100000000000000 : ℝ)) (Y := (81074597765303/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (62032139/62500000 : ℝ)) (U := (1193072899/1000000000 : ℝ)) (Ab := (825735433/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ)) (Ab := (1108890709/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab055 (p : ℝ) (hpa : (727/32 : ℝ) ≤ p) (hpb : p ≤ (91/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193072899/1000000000 : ℝ)) ∧ coordinateBox (181/400 : ℝ) (11089/10000 : ℝ) (1919/2500 : ℝ) (5921/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (318622626677861/198471000000000 : ℝ) ≤ X j i + X k i) ∧
    (115082599404587/19847100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (242487703/250000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(727/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (242487703/250000000 : ℝ))
      (by norm_num) 32 727 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(727/32 : ℝ)) ≤ (969950813/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969950813/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 727 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(91/4 : ℝ)) ≤ (121248933/125000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (121248933/125000000 : ℝ))
      (by norm_num) (by norm_num) 4 91 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (1054163198917/49617750000000 : ℝ) (10951941/1000000000 : ℝ) (4000000595413/19847100000000 : ℝ) (3033/2500 : ℝ) (121248933/62500000 : ℝ) (242487703/250000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (727/32 : ℝ)) (β := (91/4 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1054163198917/49617750000000 : ℝ)) (δ := (10951941/1000000000 : ℝ)) (h := (4000000595413/19847100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (242487703/250000000 : ℝ)) (thia := (969950813/1000000000 : ℝ)) (thib := (121248933/125000000 : ℝ))
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
  have hh := contract21_slab055 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 56, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab056 (p : ℝ) (hpa : (91/4 : ℝ) ≤ p) (hpb : p ≤ (729/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (263494193101/12421500000000 : ℝ) (2186901/200000000 : ℝ) (500000074529/2484300000000 : ℝ) (3033/2500 : ℝ) (194006401/100000000 : ℝ) (969991463/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149135689/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11091/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4527/10000 : ℝ)
      else (3839/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (263494193101/12421500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2186901/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (457977739/500000000 : ℝ) ^ p + (496818343/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (457977739/500000000 : ℝ)) (y := (496818343/500000000 : ℝ)) (X := (422961058913/3125000000000 : ℝ)) (Y := (86465262735641/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496818343/500000000 : ℝ) ^ p + (457977739/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496818343/500000000 : ℝ)) (y := (457977739/500000000 : ℝ)) (X := (86465262735641/100000000000000 : ℝ)) (Y := (422961058913/3125000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (477398041/250000000 : ℝ)) (τ := (457977739/500000000 : ℝ)) (σ := (496818343/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778452517/825600974 : ℝ) ^ p + (814666469/825600974 : ℝ) ^ p := by
    exact cert_lt (x := (778452517/825600974 : ℝ)) (y := (814666469/825600974 : ℝ)) (X := (818579524527/3125000000000 : ℝ)) (Y := (73805456606259/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457977739/500000000 : ℝ)) (n' := (412800487/500000000 : ℝ)) (Ab := (778452517/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921712211/1000000000 : ℝ) ^ p + (198515401/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (921712211/1000000000 : ℝ)) (y := (198515401/200000000 : ℝ)) (X := (390281193043/2500000000000 : ℝ)) (Y := (10548596131363/12500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198515401/200000000 : ℝ) ^ p + (921712211/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198515401/200000000 : ℝ)) (y := (921712211/1000000000 : ℝ)) (X := (10548596131363/12500000000000 : ℝ)) (Y := (390281193043/2500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (29910769/15625000 : ℝ)) (τ := (921712211/1000000000 : ℝ)) (σ := (198515401/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784661121/832445660 : ℝ) ^ p + (164302231/166489132 : ℝ) ^ p := by
    exact cert_lt (x := (784661121/832445660 : ℝ)) (y := (164302231/166489132 : ℝ)) (X := (13004380883189/50000000000000 : ℝ)) (Y := (369956195973/500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921712211/1000000000 : ℝ)) (n' := (41622283/50000000 : ℝ)) (Ab := (784661121/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (230494069/250000000 : ℝ) ^ p + (248131051/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (230494069/250000000 : ℝ)) (y := (248131051/250000000 : ℝ)) (X := (7856728024761/50000000000000 : ℝ)) (Y := (84286560187847/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248131051/250000000 : ℝ) ^ p + (230494069/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248131051/250000000 : ℝ)) (y := (230494069/250000000 : ℝ)) (X := (84286560187847/100000000000000 : ℝ)) (Y := (7856728024761/50000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (2991407/1562500 : ℝ)) (τ := (230494069/250000000 : ℝ)) (σ := (248131051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784944949/832758626 : ℝ) ^ p + (821824121/832758626 : ℝ) ^ p := by
    exact cert_lt (x := (784944949/832758626 : ℝ)) (y := (821824121/832758626 : ℝ)) (X := (26000329350827/100000000000000 : ℝ)) (Y := (73999671477959/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (230494069/250000000 : ℝ)) (n' := (416379313/500000000 : ℝ)) (Ab := (784944949/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921988257/1000000000 : ℝ) ^ p + (992521799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921988257/1000000000 : ℝ)) (y := (992521799/1000000000 : ℝ)) (X := (1964763565569/12500000000000 : ℝ)) (Y := (42140953779581/50000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992521799/1000000000 : ℝ) ^ p + (921988257/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992521799/1000000000 : ℝ)) (y := (921988257/1000000000 : ℝ)) (X := (42140953779581/50000000000000 : ℝ)) (Y := (1964763565569/12500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239313757/125000000 : ℝ)) (τ := (921988257/1000000000 : ℝ)) (σ := (992521799/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784957825/832772823 : ℝ) ^ p + (273946106/277590941 : ℝ) ^ p := by
    exact cert_lt (x := (784957825/832772823 : ℝ)) (y := (273946106/277590941 : ℝ)) (X := (25999947633997/100000000000000 : ℝ)) (Y := (14800010772213/20000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921988257/1000000000 : ℝ)) (n' := (832772823/1000000000 : ℝ)) (Ab := (31398313/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921988801/1000000000 : ℝ) ^ p + (99252169/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (921988801/1000000000 : ℝ)) (y := (99252169/100000000 : ℝ)) (X := (15718319802483/100000000000000 : ℝ)) (Y := (421408483487/500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99252169/100000000 : ℝ) ^ p + (921988801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99252169/100000000 : ℝ)) (y := (921988801/1000000000 : ℝ)) (X := (421408483487/500000000000 : ℝ)) (Y := (15718319802483/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1914510491/1000000000 : ℝ)) (τ := (921988801/1000000000 : ℝ)) (σ := (99252169/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (261652803/277591156 : ℝ) ^ p + (273946321/277591156 : ℝ) ^ p := by
    exact cert_lt (x := (261652803/277591156 : ℝ)) (y := (273946321/277591156 : ℝ)) (X := (12999964774803/50000000000000 : ℝ)) (Y := (57812555651/78125000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921988801/1000000000 : ℝ)) (n' := (208193367/250000000 : ℝ)) (Ab := (784958409/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (36879553/40000000 : ℝ) ^ p + (198504337/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (36879553/40000000 : ℝ)) (y := (198504337/200000000 : ℝ)) (X := (1571832912363/10000000000000 : ℝ)) (Y := (16856337404971/20000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198504337/200000000 : ℝ) ^ p + (36879553/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (198504337/200000000 : ℝ)) (y := (36879553/40000000 : ℝ)) (X := (16856337404971/20000000000000 : ℝ)) (Y := (1571832912363/10000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (191451051/100000000 : ℝ)) (τ := (36879553/40000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784958435/832773496 : ℝ) ^ p + (821838991/832773496 : ℝ) ^ p := by
    exact cert_lt (x := (784958435/832773496 : ℝ)) (y := (821838991/832773496 : ℝ)) (X := (649998231339/2500000000000 : ℝ)) (Y := (74000071987423/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (36879553/40000000 : ℝ)) (n' := (104096687/125000000 : ℝ)) (Ab := (156991687/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (460994413/500000000 : ℝ) ^ p + (198504337/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (460994413/500000000 : ℝ)) (y := (198504337/200000000 : ℝ)) (X := (3929582378003/25000000000000 : ℝ)) (Y := (16856337404971/20000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198504337/200000000 : ℝ) ^ p + (460994413/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198504337/200000000 : ℝ)) (y := (460994413/500000000 : ℝ)) (X := (16856337404971/20000000000000 : ℝ)) (Y := (3929582378003/25000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (784958437/832773498 : ℝ) ^ p + (273946331/277591166 : ℝ) ^ p := by
    exact cert_lt (x := (784958437/832773498 : ℝ)) (y := (273946331/277591166 : ℝ)) (X := (25999929340211/100000000000000 : ℝ)) (Y := (7400007204129/10000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1651648377/1806914488 : ℝ) ^ p + (1795979983/1806914488 : ℝ) ^ p := by
    exact cert_lt (x := (1651648377/1806914488 : ℝ)) (y := (1795979983/1806914488 : ℝ)) (X := (12914437859043/100000000000000 : ℝ)) (Y := (87085562406101/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (554501651/596542756 : ℝ) ^ p + (1182151007/1193085512 : ℝ) ^ p := by
    exact cert_lt (x := (554501651/596542756 : ℝ)) (y := (1182151007/1193085512 : ℝ)) (X := (9460672295579/50000000000000 : ℝ)) (Y := (8107865611121/10000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198504337/200000000 : ℝ)) (U := (149135689/125000000 : ℝ)) (Ab := (1651648377/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ)) (Ab := (554501651/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab056 (p : ℝ) (hpa : (91/4 : ℝ) ≤ p) (hpb : p ≤ (729/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (149135689/125000000 : ℝ)) ∧ coordinateBox (4527/10000 : ℝ) (11091/10000 : ℝ) (3839/5000 : ℝ) (5921/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (19944588188477/12421500000000 : ℝ) ≤ X j i + X k i) ∧
    (14405799925471/2484300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (969991463/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(91/4 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (969991463/1000000000 : ℝ))
      (by norm_num) 4 91 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(91/4 : ℝ)) ≤ (121248933/125000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (121248933/125000000 : ℝ))
      (by norm_num) (by norm_num) 4 91 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(729/32 : ℝ)) ≤ (194006401/200000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (194006401/200000000 : ℝ))
      (by norm_num) (by norm_num) 32 729 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (263494193101/12421500000000 : ℝ) (2186901/200000000 : ℝ) (500000074529/2484300000000 : ℝ) (3033/2500 : ℝ) (194006401/100000000 : ℝ) (969991463/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (91/4 : ℝ)) (β := (729/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (263494193101/12421500000000 : ℝ)) (δ := (2186901/200000000 : ℝ)) (h := (500000074529/2484300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (969991463/1000000000 : ℝ)) (thia := (121248933/125000000 : ℝ)) (thib := (194006401/200000000 : ℝ))
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
  have hh := contract21_slab056 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 57, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab057 (p : ℝ) (hpa : (729/32 : ℝ) ≤ p) (hpb : p ≤ (365/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (210758160251/9950850000000 : ℝ) (5458561/500000000 : ℝ) (4000000597051/19901700000000 : ℝ) (3033/2500 : ℝ) (970072437/500000000 : ℝ) (242508001/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193098127/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2773/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(4529/10000 : ℝ)
      else (96/125 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (210758160251/9950850000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5458561/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (229019203/250000000 : ℝ) ^ p + (993643477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229019203/250000000 : ℝ)) (y := (993643477/1000000000 : ℝ)) (X := (2707704351987/20000000000000 : ℝ)) (Y := (86461494862819/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993643477/1000000000 : ℝ) ^ p + (229019203/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993643477/1000000000 : ℝ)) (y := (229019203/250000000 : ℝ)) (X := (86461494862819/100000000000000 : ℝ)) (Y := (2707704351987/20000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1909720289/1000000000 : ℝ)) (τ := (229019203/250000000 : ℝ)) (σ := (993643477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778611917/825714970 : ℝ) ^ p + (407398924/412857485 : ℝ) ^ p := by
    exact cert_lt (x := (778611917/825714970 : ℝ)) (y := (407398924/412857485 : ℝ)) (X := (13093127321829/50000000000000 : ℝ)) (Y := (738137463281/1000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (229019203/250000000 : ℝ)) (n' := (82571497/100000000 : ℝ)) (Ab := (778611917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (184365859/200000000 : ℝ) ^ p + (992584317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184365859/200000000 : ℝ)) (y := (992584317/1000000000 : ℝ)) (X := (15616714029061/100000000000000 : ℝ)) (Y := (84383302355121/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992584317/1000000000 : ℝ) ^ p + (184365859/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992584317/1000000000 : ℝ)) (y := (184365859/200000000 : ℝ)) (X := (84383302355121/100000000000000 : ℝ)) (Y := (15616714029061/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (478603403/250000000 : ℝ)) (τ := (184365859/200000000 : ℝ)) (σ := (992584317/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (392407794/416276701 : ℝ) ^ p + (410818140/416276701 : ℝ) ^ p := by
    exact cert_lt (x := (392407794/416276701 : ℝ)) (y := (410818140/416276701 : ℝ)) (X := (26000716411071/100000000000000 : ℝ)) (Y := (73999284899331/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (184365859/200000000 : ℝ)) (n' := (416276701/500000000 : ℝ)) (Ab := (196203897/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922092659/1000000000 : ℝ) ^ p + (992531641/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922092659/1000000000 : ℝ)) (y := (992531641/1000000000 : ℝ)) (X := (3143762640619/20000000000000 : ℝ)) (Y := (4214060144887/5000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992531641/1000000000 : ℝ) ^ p + (922092659/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992531641/1000000000 : ℝ)) (y := (922092659/1000000000 : ℝ)) (X := (4214060144887/5000000000000 : ℝ)) (Y := (3143762640619/20000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (19146243/10000000 : ℝ)) (τ := (922092659/1000000000 : ℝ)) (σ := (992531641/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785098647/832865483 : ℝ) ^ p + (821948361/832865483 : ℝ) ^ p := by
    exact cert_lt (x := (785098647/832865483 : ℝ)) (y := (821948361/832865483 : ℝ)) (X := (203064929349/781250000000 : ℝ)) (Y := (74007690040423/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922092659/1000000000 : ℝ)) (n' := (832865483/1000000000 : ℝ)) (Ab := (785098647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (461052293/500000000 : ℝ) ^ p + (496264623/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461052293/500000000 : ℝ)) (y := (496264623/500000000 : ℝ)) (X := (3930863013879/25000000000000 : ℝ)) (Y := (2106914089709/2500000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496264623/500000000 : ℝ) ^ p + (461052293/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496264623/500000000 : ℝ)) (y := (461052293/500000000 : ℝ)) (X := (2106914089709/2500000000000 : ℝ)) (Y := (3930863013879/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239329229/125000000 : ℝ)) (τ := (461052293/500000000 : ℝ)) (σ := (496264623/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (392555732/416439807 : ℝ) ^ p + (410981246/416439807 : ℝ) ^ p := by
    exact cert_lt (x := (392555732/416439807 : ℝ)) (y := (410981246/416439807 : ℝ)) (X := (25991930654761/100000000000000 : ℝ)) (Y := (18502017624249/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (461052293/500000000 : ℝ)) (n' := (416439807/500000000 : ℝ)) (Ab := (98138933/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (461052563/500000000 : ℝ) ^ p + (496264569/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461052563/500000000 : ℝ)) (y := (496264569/500000000 : ℝ)) (X := (1965457764063/12500000000000 : ℝ)) (Y := (84276354389349/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496264569/500000000 : ℝ) ^ p + (461052563/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496264569/500000000 : ℝ)) (y := (461052563/500000000 : ℝ)) (X := (84276354389349/100000000000000 : ℝ)) (Y := (1965457764063/12500000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239329283/125000000 : ℝ)) (τ := (461052563/500000000 : ℝ)) (σ := (496264569/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (392556022/416440127 : ℝ) ^ p + (410981566/416440127 : ℝ) ^ p := by
    exact cert_lt (x := (392556022/416440127 : ℝ)) (y := (410981566/416440127 : ℝ)) (X := (25991913062361/100000000000000 : ℝ)) (Y := (37004043863901/50000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (461052563/500000000 : ℝ)) (n' := (416440127/500000000 : ℝ)) (Ab := (196278011/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (18442103/20000000 : ℝ) ^ p + (992529133/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18442103/20000000 : ℝ)) (y := (992529133/1000000000 : ℝ)) (X := (15723671448433/100000000000000 : ℝ)) (Y := (84276344704221/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992529133/1000000000 : ℝ) ^ p + (18442103/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (992529133/1000000000 : ℝ)) (y := (18442103/20000000 : ℝ)) (X := (84276344704221/100000000000000 : ℝ)) (Y := (15723671448433/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1914634283/1000000000 : ℝ)) (τ := (18442103/20000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392556035/416440141 : ℝ) ^ p + (410981580/416440141 : ℝ) ^ p := by
    exact cert_lt (x := (392556035/416440141 : ℝ)) (y := (410981580/416440141 : ℝ)) (X := (25991912764713/100000000000000 : ℝ)) (Y := (74008088481649/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (18442103/20000000 : ℝ)) (n' := (416440141/500000000 : ℝ)) (Ab := (78511207/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (922105151/1000000000 : ℝ) ^ p + (992529133/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922105151/1000000000 : ℝ)) (y := (992529133/1000000000 : ℝ)) (X := (1572367183743/10000000000000 : ℝ)) (Y := (84276344704221/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992529133/1000000000 : ℝ) ^ p + (922105151/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992529133/1000000000 : ℝ)) (y := (922105151/1000000000 : ℝ)) (X := (84276344704221/100000000000000 : ℝ)) (Y := (1572367183743/10000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785112071/832880283 : ℝ) ^ p + (821963161/832880283 : ℝ) ^ p := by
    exact cert_lt (x := (785112071/832880283 : ℝ)) (y := (821963161/832880283 : ℝ)) (X := (6497978202007/25000000000000 : ℝ)) (Y := (18502022127143/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1651825417/1806901873 : ℝ) ^ p + (1795984751/1806901873 : ℝ) ^ p := by
    exact cert_lt (x := (1651825417/1806901873 : ℝ)) (y := (1795984751/1806901873 : ℝ)) (X := (1291181248513/10000000000000 : ℝ)) (Y := (8708818773441/10000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109115651/1193098127 : ℝ) ^ p + (1182181005/1193098127 : ℝ) ^ p := by
    exact cert_lt (x := (1109115651/1193098127 : ℝ)) (y := (1182181005/1193098127 : ℝ)) (X := (1891729476129/10000000000000 : ℝ)) (Y := (20270676503989/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992529133/1000000000 : ℝ)) (U := (1193098127/1000000000 : ℝ)) (Ab := (1651825417/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ)) (Ab := (1109115651/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab057 (p : ℝ) (hpa : (729/32 : ℝ) ≤ p) (hpb : p ≤ (365/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193098127/1000000000 : ℝ)) ∧ coordinateBox (4529/10000 : ℝ) (2773/2500 : ℝ) (96/125 : ℝ) (5921/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (319604188068671/199017000000000 : ℝ) ≤ X j i + X k i) ∧
    (115410199402949/19901700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (242508001/250000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(729/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (242508001/250000000 : ℝ))
      (by norm_num) 32 729 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(729/32 : ℝ)) ≤ (194006401/200000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (194006401/200000000 : ℝ))
      (by norm_num) (by norm_num) 32 729 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(365/16 : ℝ)) ≤ (970072437/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970072437/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 365 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (210758160251/9950850000000 : ℝ) (5458561/500000000 : ℝ) (4000000597051/19901700000000 : ℝ) (3033/2500 : ℝ) (970072437/500000000 : ℝ) (242508001/250000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (729/32 : ℝ)) (β := (365/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (210758160251/9950850000000 : ℝ)) (δ := (5458561/500000000 : ℝ)) (h := (4000000597051/19901700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (242508001/250000000 : ℝ)) (thia := (194006401/200000000 : ℝ)) (thib := (970072437/1000000000 : ℝ))
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
  have hh := contract21_slab057 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 58, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab058 (p : ℝ) (hpa : (365/16 : ℝ) ≤ p) (hpb : p ≤ (731/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (105360544927/4982250000000 : ℝ) (2724949/250000000 : ℝ) (400000059787/1992900000000 : ℝ) (3033/2500 : ℝ) (970112759/500000000 : ℝ) (242518109/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298277689/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11093/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4531/10000 : ℝ)
      else (7681/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (105360544927/4982250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2724949/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (183239559/200000000 : ℝ) ^ p + (198730051/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (183239559/200000000 : ℝ)) (y := (198730051/200000000 : ℝ)) (X := (1354227885233/10000000000000 : ℝ)) (Y := (432288690767/500000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198730051/200000000 : ℝ) ^ p + (183239559/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198730051/200000000 : ℝ)) (y := (183239559/200000000 : ℝ)) (X := (432288690767/500000000000 : ℝ)) (Y := (1354227885233/10000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (38196961/20000000 : ℝ)) (τ := (183239559/200000000 : ℝ)) (σ := (198730051/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (389385437/412914293 : ℝ) ^ p + (407464395/412914293 : ℝ) ^ p := by
    exact cert_lt (x := (389385437/412914293 : ℝ)) (y := (407464395/412914293 : ℝ)) (X := (13088998774773/50000000000000 : ℝ)) (Y := (73822003931519/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (183239559/200000000 : ℝ)) (n' := (412914293/500000000 : ℝ)) (Ab := (389385437/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (36877841/40000000 : ℝ) ^ p + (496295809/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (36877841/40000000 : ℝ)) (y := (496295809/500000000 : ℝ)) (X := (15622163487477/100000000000000 : ℝ)) (Y := (42188926698479/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496295809/500000000 : ℝ) ^ p + (36877841/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496295809/500000000 : ℝ)) (y := (36877841/40000000 : ℝ)) (X := (42188926698479/50000000000000 : ℝ)) (Y := (15622163487477/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1914537643/1000000000 : ℝ)) (τ := (36877841/40000000 : ℝ)) (σ := (496295809/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784969609/832660766 : ℝ) ^ p + (410880485/416330383 : ℝ) ^ p := by
    exact cert_lt (x := (784969609/832660766 : ℝ)) (y := (410880485/416330383 : ℝ)) (X := (6498175549631/25000000000000 : ℝ)) (Y := (3700364948301/5000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (36877841/40000000 : ℝ)) (n' := (416330383/500000000 : ℝ)) (Ab := (784969609/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922208689/1000000000 : ℝ) ^ p + (992539067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922208689/1000000000 : ℝ)) (y := (992539067/1000000000 : ℝ)) (X := (15724153015973/100000000000000 : ℝ)) (Y := (42137931985651/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992539067/1000000000 : ℝ) ^ p + (922208689/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992539067/1000000000 : ℝ)) (y := (922208689/1000000000 : ℝ)) (X := (42137931985651/50000000000000 : ℝ)) (Y := (15724153015973/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478686939/250000000 : ℝ)) (τ := (922208689/1000000000 : ℝ)) (σ := (992539067/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785251901/832971964 : ℝ) ^ p + (205518042/208242991 : ℝ) ^ p := by
    exact cert_lt (x := (785251901/832971964 : ℝ)) (y := (205518042/208242991 : ℝ)) (X := (25984323960559/100000000000000 : ℝ)) (Y := (37007838525203/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922208689/1000000000 : ℝ)) (n' := (208242991/250000000 : ℝ)) (Ab := (785251901/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922220563/1000000000 : ℝ) ^ p + (496268341/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922220563/1000000000 : ℝ)) (y := (496268341/500000000 : ℝ)) (X := (3932194641997/25000000000000 : ℝ)) (Y := (10533904753923/12500000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496268341/500000000 : ℝ) ^ p + (922220563/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496268341/500000000 : ℝ)) (y := (922220563/1000000000 : ℝ)) (X := (10533904753923/12500000000000 : ℝ)) (Y := (3932194641997/25000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (382951449/200000000 : ℝ)) (τ := (922220563/1000000000 : ℝ)) (σ := (496268341/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (13776573/14613790 : ℝ) ^ p + (411043117/416493015 : ℝ) ^ p := by
    exact cert_lt (x := (13776573/14613790 : ℝ)) (y := (411043117/416493015 : ℝ)) (X := (25983945883223/100000000000000 : ℝ)) (Y := (74016055609337/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922220563/1000000000 : ℝ)) (n' := (83298603/100000000 : ℝ)) (Ab := (785264661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922221099/1000000000 : ℝ) ^ p + (496268287/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922221099/1000000000 : ℝ)) (y := (496268287/500000000 : ℝ)) (X := (15728987399071/100000000000000 : ℝ)) (Y := (42135514280303/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496268287/500000000 : ℝ) ^ p + (922221099/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496268287/500000000 : ℝ)) (y := (922221099/1000000000 : ℝ)) (X := (42135514280303/50000000000000 : ℝ)) (Y := (15728987399071/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1914757673/1000000000 : ℝ)) (τ := (922221099/1000000000 : ℝ)) (σ := (496268287/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785265237/832986665 : ℝ) ^ p + (822086869/832986665 : ℝ) ^ p := by
    exact cert_lt (x := (785265237/832986665 : ℝ)) (y := (822086869/832986665 : ℝ)) (X := (25983928784221/100000000000000 : ℝ)) (Y := (4626004543679/6250000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922221099/1000000000 : ℝ)) (n' := (166597333/200000000 : ℝ)) (Ab := (785265237/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (230555281/250000000 : ℝ) ^ p + (992536569/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230555281/250000000 : ℝ)) (y := (992536569/1000000000 : ℝ)) (X := (245765580303/1562500000000 : ℝ)) (Y := (84271018862897/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992536569/1000000000 : ℝ) ^ p + (230555281/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992536569/1000000000 : ℝ)) (y := (230555281/250000000 : ℝ)) (X := (84271018862897/100000000000000 : ℝ)) (Y := (245765580303/1562500000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1914757693/1000000000 : ℝ)) (τ := (230555281/250000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (785265264/832986695 : ℝ) ^ p + (822086899/832986695 : ℝ) ^ p := by
    exact cert_lt (x := (785265264/832986695 : ℝ)) (y := (822086899/832986695 : ℝ)) (X := (5196785563139/20000000000000 : ℝ)) (Y := (74016073506243/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (230555281/250000000 : ℝ)) (n' := (166597339/200000000 : ℝ)) (Ab := (49079079/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (7377769/8000000 : ℝ) ^ p + (992536569/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7377769/8000000 : ℝ)) (y := (992536569/1000000000 : ℝ)) (X := (3145799505801/20000000000000 : ℝ)) (Y := (84271018862897/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992536569/1000000000 : ℝ) ^ p + (7377769/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992536569/1000000000 : ℝ)) (y := (7377769/8000000 : ℝ)) (X := (84271018862897/100000000000000 : ℝ)) (Y := (3145799505801/20000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785265265/832986696 : ℝ) ^ p + (205521725/208246674 : ℝ) ^ p := by
    exact cert_lt (x := (785265265/832986696 : ℝ)) (y := (205521725/208246674 : ℝ)) (X := (25983927858999/100000000000000 : ℝ)) (Y := (14803214706631/20000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (413000501/451722311 : ℝ) ^ p + (448997362/451722311 : ℝ) ^ p := by
    exact cert_lt (x := (413000501/451722311 : ℝ)) (y := (448997362/451722311 : ℝ)) (X := (12909197804557/100000000000000 : ℝ)) (Y := (87090802442723/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (277306946/298277689 : ℝ) ^ p + (295552740/298277689 : ℝ) ^ p := by
    exact cert_lt (x := (277306946/298277689 : ℝ)) (y := (295552740/298277689 : ℝ)) (X := (4728314864483/25000000000000 : ℝ)) (Y := (40543370522091/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992536569/1000000000 : ℝ)) (U := (298277689/250000000 : ℝ)) (Ab := (413000501/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ)) (Ab := (138653473/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab058 (p : ℝ) (hpa : (365/16 : ℝ) ≤ p) (hpb : p ≤ (731/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (298277689/250000000 : ℝ)) ∧ coordinateBox (4531/10000 : ℝ) (11093/10000 : ℝ) (7681/10000 : ℝ) (11843/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (16004747772193/9964500000000 : ℝ) ≤ X j i + X k i) ∧
    (11557399940213/1992900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (242518109/250000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(365/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (242518109/250000000 : ℝ))
      (by norm_num) 16 365 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(365/16 : ℝ)) ≤ (970072437/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970072437/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 365 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(731/32 : ℝ)) ≤ (970112759/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970112759/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 731 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (105360544927/4982250000000 : ℝ) (2724949/250000000 : ℝ) (400000059787/1992900000000 : ℝ) (3033/2500 : ℝ) (970112759/500000000 : ℝ) (242518109/250000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (365/16 : ℝ)) (β := (731/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (105360544927/4982250000000 : ℝ)) (δ := (2724949/250000000 : ℝ)) (h := (400000059787/1992900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (242518109/250000000 : ℝ)) (thia := (970072437/1000000000 : ℝ)) (thib := (970112759/1000000000 : ℝ))
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
  have hh := contract21_slab058 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 59, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab059 (p : ℝ) (hpa : (731/32 : ℝ) ≤ p) (hpb : p ≤ (183/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (526710141599/24945375000000 : ℝ) (10882519/1000000000 : ℝ) (4000000598689/19956300000000 : ℝ) (3033/2500 : ℝ) (970152973/500000000 : ℝ) (485056379/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193123373/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5547/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4533/10000 : ℝ)
      else (7683/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (526710141599/24945375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10882519/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (916318439/1000000000 : ℝ) ^ p + (496828509/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (916318439/1000000000 : ℝ)) (y := (496828509/500000000 : ℝ)) (X := (6773014375233/50000000000000 : ℝ)) (Y := (5403374282471/6250000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496828509/500000000 : ℝ) ^ p + (916318439/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496828509/500000000 : ℝ)) (y := (916318439/1000000000 : ℝ)) (X := (5403374282471/6250000000000 : ℝ)) (Y := (6773014375233/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1909975457/1000000000 : ℝ)) (τ := (916318439/1000000000 : ℝ)) (σ := (496828509/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778929390/825941849 : ℝ) ^ p + (815059330/825941849 : ℝ) ^ p := by
    exact cert_lt (x := (778929390/825941849 : ℝ)) (y := (815059330/825941849 : ℝ)) (X := (26169755219857/100000000000000 : ℝ)) (Y := (73830246265591/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916318439/1000000000 : ℝ)) (n' := (825941849/1000000000 : ℝ)) (Ab := (77892939/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (922062413/1000000000 : ℝ) ^ p + (198519781/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (922062413/1000000000 : ℝ)) (y := (198519781/200000000 : ℝ)) (X := (15627600197779/100000000000000 : ℝ)) (Y := (42186208126091/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198519781/200000000 : ℝ) ^ p + (922062413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198519781/200000000 : ℝ)) (y := (922062413/1000000000 : ℝ)) (X := (42186208126091/50000000000000 : ℝ)) (Y := (15627600197779/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957330659/500000000 : ℝ)) (τ := (922062413/1000000000 : ℝ)) (σ := (198519781/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785123188/832767779 : ℝ) ^ p + (821885260/832767779 : ℝ) ^ p := by
    exact cert_lt (x := (785123188/832767779 : ℝ)) (y := (821885260/832767779 : ℝ)) (X := (12992351313613/50000000000000 : ℝ)) (Y := (74015298138651/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (922062413/1000000000 : ℝ)) (n' := (832767779/1000000000 : ℝ)) (Ab := (196280797/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922324381/1000000000 : ℝ) ^ p + (496273239/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922324381/1000000000 : ℝ)) (y := (496273239/500000000 : ℝ)) (X := (3145896157287/20000000000000 : ℝ)) (Y := (84270535548907/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496273239/500000000 : ℝ) ^ p + (922324381/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496273239/500000000 : ℝ)) (y := (922324381/1000000000 : ℝ)) (X := (84270535548907/100000000000000 : ℝ)) (Y := (3145896157287/20000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914870859/1000000000 : ℝ)) (τ := (922324381/1000000000 : ℝ)) (σ := (496273239/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (112200674/119011157 : ℝ) ^ p + (822195580/833078099 : ℝ) ^ p := by
    exact cert_lt (x := (112200674/119011157 : ℝ)) (y := (822195580/833078099 : ℝ)) (X := (1298817600111/5000000000000 : ℝ)) (Y := (14804729865543/20000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922324381/1000000000 : ℝ)) (n' := (833078099/1000000000 : ℝ)) (Ab := (392702359/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922336201/1000000000 : ℝ) ^ p + (992544103/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922336201/1000000000 : ℝ)) (y := (992544103/1000000000 : ℝ)) (X := (25174548133/160000000000 : ℝ)) (Y := (42132961514509/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992544103/1000000000 : ℝ) ^ p + (922336201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992544103/1000000000 : ℝ)) (y := (922336201/1000000000 : ℝ)) (X := (42132961514509/50000000000000 : ℝ)) (Y := (25174548133/160000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (119680019/62500000 : ℝ)) (τ := (922336201/1000000000 : ℝ)) (σ := (992544103/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (785417419/833092099 : ℝ) ^ p + (822209580/833092099 : ℝ) ^ p := by
    exact cert_lt (x := (785417419/833092099 : ℝ)) (y := (822209580/833092099 : ℝ)) (X := (811749230059/3125000000000 : ℝ)) (Y := (14804805192767/20000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922336201/1000000000 : ℝ)) (n' := (833092099/1000000000 : ℝ)) (Ab := (785417419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (461168367/500000000 : ℝ) ^ p + (248135999/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (461168367/500000000 : ℝ)) (y := (248135999/250000000 : ℝ)) (X := (15734300573627/100000000000000 : ℝ)) (Y := (42132857614271/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248135999/250000000 : ℝ) ^ p + (461168367/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248135999/250000000 : ℝ)) (y := (461168367/500000000 : ℝ)) (X := (42132857614271/50000000000000 : ℝ)) (Y := (15734300573627/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (191488073/100000000 : ℝ)) (τ := (461168367/500000000 : ℝ)) (σ := (248135999/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785417991/833092730 : ℝ) ^ p + (822210211/833092730 : ℝ) ^ p := by
    exact cert_lt (x := (785417991/833092730 : ℝ)) (y := (822210211/833092730 : ℝ)) (X := (25975958044473/100000000000000 : ℝ)) (Y := (18506010734777/25000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (461168367/500000000 : ℝ)) (n' := (83309273/100000000 : ℝ)) (Ab := (785417991/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (922336757/1000000000 : ℝ) ^ p + (124067999/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (922336757/1000000000 : ℝ)) (y := (124067999/125000000 : ℝ)) (X := (7867154774443/50000000000000 : ℝ)) (Y := (8426570746031/10000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124067999/125000000 : ℝ) ^ p + (922336757/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124067999/125000000 : ℝ)) (y := (922336757/1000000000 : ℝ)) (X := (8426570746031/10000000000000 : ℝ)) (Y := (7867154774443/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1914880749/1000000000 : ℝ)) (τ := (922336757/1000000000 : ℝ)) (σ := (124067999/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (785418017/833092758 : ℝ) ^ p + (822210239/833092758 : ℝ) ^ p := by
    exact cert_lt (x := (785418017/833092758 : ℝ)) (y := (822210239/833092758 : ℝ)) (X := (25975957743623/100000000000000 : ℝ)) (Y := (74024043692369/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (922336757/1000000000 : ℝ)) (n' := (416546379/500000000 : ℝ)) (Ab := (785418017/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (922336759/1000000000 : ℝ) ^ p + (992543991/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922336759/1000000000 : ℝ)) (y := (992543991/1000000000 : ℝ)) (X := (15365537431/97656250000 : ℝ)) (Y := (21066426379563/25000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992543991/1000000000 : ℝ) ^ p + (922336759/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992543991/1000000000 : ℝ)) (y := (922336759/1000000000 : ℝ)) (X := (21066426379563/25000000000000 : ℝ)) (Y := (15365537431/97656250000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (392709009/416546380 : ℝ) ^ p + (26522911/26873960 : ℝ) ^ p := by
    exact cert_lt (x := (392709009/416546380 : ℝ)) (y := (26522911/26873960 : ℝ)) (X := (25975957073671/100000000000000 : ℝ)) (Y := (74024043746173/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (550726038/602292209 : ℝ) ^ p + (1795994108/1806876627 : ℝ) ^ p := by
    exact cert_lt (x := (550726038/602292209 : ℝ)) (y := (1795994108/1806876627 : ℝ)) (X := (12906584964481/100000000000000 : ℝ)) (Y := (21773353829949/25000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (369779883/397707791 : ℝ) ^ p + (1182240854/1193123373 : ℝ) ^ p := by
    exact cert_lt (x := (369779883/397707791 : ℝ)) (y := (1182240854/1193123373 : ℝ)) (X := (18909227465057/100000000000000 : ℝ)) (Y := (5068173313111/6250000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992543991/1000000000 : ℝ)) (U := (1193123373/1000000000 : ℝ)) (Ab := (826089057/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ)) (Ab := (1109339649/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab059 (p : ℝ) (hpa : (731/32 : ℝ) ≤ p) (hpb : p ≤ (183/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193123373/1000000000 : ℝ)) ∧ coordinateBox (4533/10000 : ℝ) (5547/5000 : ℝ) (7683/10000 : ℝ) (11843/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (320585718318371/199563000000000 : ℝ) ≤ X j i + X k i) ∧
    (115737799401311/19956300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (485056379/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(731/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (485056379/500000000 : ℝ))
      (by norm_num) 32 731 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(731/32 : ℝ)) ≤ (970112759/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970112759/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 731 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(183/8 : ℝ)) ≤ (970152973/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970152973/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 183 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (526710141599/24945375000000 : ℝ) (10882519/1000000000 : ℝ) (4000000598689/19956300000000 : ℝ) (3033/2500 : ℝ) (970152973/500000000 : ℝ) (485056379/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (731/32 : ℝ)) (β := (183/8 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (526710141599/24945375000000 : ℝ)) (δ := (10882519/1000000000 : ℝ)) (h := (4000000598689/19956300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (485056379/500000000 : ℝ)) (thia := (970112759/1000000000 : ℝ)) (thib := (970152973/1000000000 : ℝ))
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
  have hh := contract21_slab059 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 60, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab060 (p : ℝ) (hpa : (183/8 : ℝ) ≤ p) (hpb : p ≤ (733/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (263308941853/12489750000000 : ℝ) (10865299/1000000000 : ℝ) (1000000149877/4995900000000 : ℝ) (3033/2500 : ℝ) (970193079/500000000 : ℝ) (242538243/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149142001/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2219/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(907/2000 : ℝ)
      else (1537/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (263308941853/12489750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10865299/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (916438733/1000000000 : ℝ) ^ p + (124207971/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (916438733/1000000000 : ℝ)) (y := (124207971/125000000 : ℝ)) (X := (3387441819261/25000000000000 : ℝ)) (Y := (43225124911983/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124207971/125000000 : ℝ) ^ p + (916438733/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124207971/125000000 : ℝ)) (y := (916438733/1000000000 : ℝ)) (X := (43225124911983/50000000000000 : ℝ)) (Y := (3387441819261/25000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1910102501/1000000000 : ℝ)) (τ := (916438733/1000000000 : ℝ)) (σ := (124207971/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779087464/826054733 : ℝ) ^ p + (815189434/826054733 : ℝ) ^ p := by
    exact cert_lt (x := (779087464/826054733 : ℝ)) (y := (815189434/826054733 : ℝ)) (X := (6540386361883/25000000000000 : ℝ)) (Y := (9229806952781/12500000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916438733/1000000000 : ℝ)) (n' := (826054733/1000000000 : ℝ)) (Ab := (97385933/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (57636153/62500000 : ℝ) ^ p + (992606181/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57636153/62500000 : ℝ)) (y := (992606181/1000000000 : ℝ)) (X := (7816509679269/50000000000000 : ℝ)) (Y := (1687339932959/2000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992606181/1000000000 : ℝ) ^ p + (57636153/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992606181/1000000000 : ℝ)) (y := (57636153/62500000 : ℝ)) (X := (1687339932959/2000000000000 : ℝ)) (Y := (7816509679269/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1914784629/1000000000 : ℝ)) (τ := (57636153/62500000 : ℝ)) (σ := (992606181/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (52351755/55524961 : ℝ) ^ p + (822009116/832874415 : ℝ) ^ p := by
    exact cert_lt (x := (52351755/55524961 : ℝ)) (y := (822009116/832874415 : ℝ)) (X := (5195347193761/20000000000000 : ℝ)) (Y := (14804652963431/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (57636153/62500000 : ℝ)) (n' := (166574883/200000000 : ℝ)) (Ab := (31411053/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922439723/1000000000 : ℝ) ^ p + (496276939/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922439723/1000000000 : ℝ)) (y := (496276939/500000000 : ℝ)) (X := (3146958259889/20000000000000 : ℝ)) (Y := (84265225288153/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496276939/500000000 : ℝ) ^ p + (922439723/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496276939/500000000 : ℝ)) (y := (922439723/1000000000 : ℝ)) (X := (84265225288153/100000000000000 : ℝ)) (Y := (3146958259889/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914993601/1000000000 : ℝ)) (τ := (922439723/1000000000 : ℝ)) (σ := (496276939/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (392778548/416591931 : ℝ) ^ p + (822318563/833183862 : ℝ) ^ p := by
    exact cert_lt (x := (392778548/416591931 : ℝ)) (y := (822318563/833183862 : ℝ)) (X := (25968411825879/100000000000000 : ℝ)) (Y := (74031589276953/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922439723/1000000000 : ℝ)) (n' := (416591931/500000000 : ℝ)) (Ab := (98194637/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (28826609/31250000 : ℝ) ^ p + (496275757/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (28826609/31250000 : ℝ)) (y := (496275757/500000000 : ℝ)) (X := (3934847220641/25000000000000 : ℝ)) (Y := (42130314091517/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496275757/500000000 : ℝ) ^ p + (28826609/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (496275757/500000000 : ℝ)) (y := (28826609/31250000 : ℝ)) (X := (42130314091517/50000000000000 : ℝ)) (Y := (3934847220641/25000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957501501/500000000 : ℝ)) (τ := (28826609/31250000 : ℝ)) (σ := (496275757/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261856579/277732598 : ℝ) ^ p + (822332495/833197794 : ℝ) ^ p := by
    exact cert_lt (x := (261856579/277732598 : ℝ)) (y := (822332495/833197794 : ℝ)) (X := (3246004662953/12500000000000 : ℝ)) (Y := (74031963938449/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (28826609/31250000 : ℝ)) (n' := (416598897/500000000 : ℝ)) (Ab := (785569737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (461226009/500000000 : ℝ) ^ p + (992551407/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461226009/500000000 : ℝ)) (y := (992551407/1000000000 : ℝ)) (X := (1967449503593/12500000000000 : ℝ)) (Y := (84260420113307/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992551407/1000000000 : ℝ) ^ p + (461226009/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992551407/1000000000 : ℝ)) (y := (461226009/500000000 : ℝ)) (X := (84260420113307/100000000000000 : ℝ)) (Y := (1967449503593/12500000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (76600137/40000000 : ℝ)) (τ := (461226009/500000000 : ℝ)) (σ := (992551407/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785570307/833198422 : ℝ) ^ p + (822333123/833198422 : ℝ) ^ p := by
    exact cert_lt (x := (785570307/833198422 : ℝ)) (y := (822333123/833198422 : ℝ)) (X := (25968020568353/100000000000000 : ℝ)) (Y := (74031980826469/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (461226009/500000000 : ℝ)) (n' := (416599211/500000000 : ℝ)) (Ab := (785570307/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461226021/500000000 : ℝ) ^ p + (496275701/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461226021/500000000 : ℝ)) (y := (496275701/500000000 : ℝ)) (X := (1573960540901/10000000000000 : ℝ)) (Y := (42130205195217/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496275701/500000000 : ℝ) ^ p + (461226021/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496275701/500000000 : ℝ)) (y := (461226021/500000000 : ℝ)) (X := (42130205195217/50000000000000 : ℝ)) (Y := (1573960540901/10000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478750861/250000000 : ℝ)) (τ := (461226021/500000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392785166/416599225 : ℝ) ^ p + (822333151/833198450 : ℝ) ^ p := by
    exact cert_lt (x := (392785166/416599225 : ℝ)) (y := (822333151/833198450 : ℝ)) (X := (25968019508707/100000000000000 : ℝ)) (Y := (37015990789719/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461226021/500000000 : ℝ)) (n' := (16663969/20000000 : ℝ)) (Ab := (196392583/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (922452043/1000000000 : ℝ) ^ p + (496275701/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922452043/1000000000 : ℝ)) (y := (496275701/500000000 : ℝ)) (X := (3147921159971/20000000000000 : ℝ)) (Y := (42130205195217/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496275701/500000000 : ℝ) ^ p + (922452043/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496275701/500000000 : ℝ)) (y := (922452043/1000000000 : ℝ)) (X := (42130205195217/50000000000000 : ℝ)) (Y := (3147921159971/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785570333/833198451 : ℝ) ^ p + (822333152/833198451 : ℝ) ^ p := by
    exact cert_lt (x := (785570333/833198451 : ℝ)) (y := (822333152/833198451 : ℝ)) (X := (2596801955199/10000000000000 : ℝ)) (Y := (7403198160633/10000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652353773/1806863992 : ℝ) ^ p + (1795998693/1806863992 : ℝ) ^ p := by
    exact cert_lt (x := (1652353773/1806863992 : ℝ)) (y := (1795998693/1806863992 : ℝ)) (X := (806498948723/6250000000000 : ℝ)) (Y := (17419203411279/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109451307/1193136008 : ℝ) ^ p + (1182270709/1193136008 : ℝ) ^ p := by
    exact cert_lt (x := (1109451307/1193136008 : ℝ)) (y := (1182270709/1193136008 : ℝ)) (X := (9452605653227/50000000000000 : ℝ)) (Y := (81094789458841/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496275701/500000000 : ℝ)) (U := (149142001/125000000 : ℝ)) (Ab := (1652353773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ)) (Ab := (1109451307/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab060 (p : ℝ) (hpa : (183/8 : ℝ) ≤ p) (hpb : p ≤ (733/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (149142001/125000000 : ℝ)) ∧ coordinateBox (907/2000 : ℝ) (2219/2000 : ℝ) (1537/2000 : ℝ) (11843/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (40134558838369/24979500000000 : ℝ) ≤ X j i + X k i) ∧
    (28975399850123/4995900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (242538243/250000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(183/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (242538243/250000000 : ℝ))
      (by norm_num) 8 183 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(183/8 : ℝ)) ≤ (970152973/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970152973/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 183 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(733/32 : ℝ)) ≤ (970193079/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970193079/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 733 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (263308941853/12489750000000 : ℝ) (10865299/1000000000 : ℝ) (1000000149877/4995900000000 : ℝ) (3033/2500 : ℝ) (970193079/500000000 : ℝ) (242538243/250000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (183/8 : ℝ)) (β := (733/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (263308941853/12489750000000 : ℝ)) (δ := (10865299/1000000000 : ℝ)) (h := (1000000149877/4995900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (242538243/250000000 : ℝ)) (thia := (970152973/1000000000 : ℝ)) (thib := (970193079/1000000000 : ℝ))
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
  have hh := contract21_slab060 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 61, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab061 (p : ℝ) (hpa : (733/32 : ℝ) ≤ p) (hpb : p ≤ (367/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (526525884617/25013625000000 : ℝ) (2712033/250000000 : ℝ) (4000000600327/20010900000000 : ℝ) (3033/2500 : ℝ) (485116539/250000000 : ℝ) (485096539/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193148647/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1387/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(4537/10000 : ℝ)
      else (7687/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (526525884617/25013625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2712033/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (916558683/1000000000 : ℝ) ^ p + (198734101/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (916558683/1000000000 : ℝ)) (y := (198734101/200000000 : ℝ)) (X := (6776747999027/50000000000000 : ℝ)) (Y := (86446521959411/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198734101/200000000 : ℝ) ^ p + (916558683/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198734101/200000000 : ℝ)) (y := (916558683/1000000000 : ℝ)) (X := (86446521959411/100000000000000 : ℝ)) (Y := (6776747999027/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (477557297/250000000 : ℝ)) (τ := (916558683/1000000000 : ℝ)) (σ := (198734101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779245099/826167251 : ℝ) ^ p + (815319119/826167251 : ℝ) ^ p := by
    exact cert_lt (x := (779245099/826167251 : ℝ)) (y := (815319119/826167251 : ℝ)) (X := (13076680426681/50000000000000 : ℝ)) (Y := (73846640201579/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916558683/1000000000 : ℝ)) (n' := (826167251/1000000000 : ℝ)) (Ab := (779245099/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (922294137/1000000000 : ℝ) ^ p + (198522689/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (922294137/1000000000 : ℝ)) (y := (198522689/200000000 : ℝ)) (X := (7819211570693/50000000000000 : ℝ)) (Y := (21090398135971/25000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198522689/200000000 : ℝ) ^ p + (922294137/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198522689/200000000 : ℝ)) (y := (922294137/1000000000 : ℝ)) (X := (21090398135971/25000000000000 : ℝ)) (Y := (7819211570693/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957453791/500000000 : ℝ)) (τ := (922294137/1000000000 : ℝ)) (σ := (198522689/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785429024/832980689 : ℝ) ^ p + (1476001/1495477 : ℝ) ^ p := by
    exact cert_lt (x := (785429024/832980689 : ℝ)) (y := (1476001/1495477 : ℝ)) (X := (1623049642457/6250000000000 : ℝ)) (Y := (74031207203861/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (922294137/1000000000 : ℝ)) (n' := (832980689/1000000000 : ℝ)) (Ab := (24544657/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (5765967/6250000 : ℝ) ^ p + (496280633/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (5765967/6250000 : ℝ)) (y := (496280633/500000000 : ℝ)) (X := (7870042981363/50000000000000 : ℝ)) (Y := (84259931150949/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496280633/500000000 : ℝ) ^ p + (5765967/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (496280633/500000000 : ℝ)) (y := (5765967/6250000 : ℝ)) (X := (84259931150949/100000000000000 : ℝ)) (Y := (7870042981363/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (957557993/500000000 : ℝ)) (τ := (5765967/6250000 : ℝ)) (σ := (496280633/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785709035/833289263 : ℝ) ^ p + (822441131/833289263 : ℝ) ^ p := by
    exact cert_lt (x := (785709035/833289263 : ℝ)) (y := (822441131/833289263 : ℝ)) (X := (25960496030471/100000000000000 : ℝ)) (Y := (37019752481727/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (5765967/6250000 : ℝ)) (n' := (833289263/1000000000 : ℝ)) (Ab := (157141807/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922566433/1000000000 : ℝ) ^ p + (992558911/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922566433/1000000000 : ℝ)) (y := (992558911/1000000000 : ℝ)) (X := (15744670438389/100000000000000 : ℝ)) (Y := (42127672810853/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992558911/1000000000 : ℝ) ^ p + (922566433/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992558911/1000000000 : ℝ)) (y := (922566433/1000000000 : ℝ)) (X := (42127672810853/50000000000000 : ℝ)) (Y := (15744670438389/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (59847667/31250000 : ℝ)) (τ := (922566433/1000000000 : ℝ)) (σ := (992558911/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (785721619/833303131 : ℝ) ^ p + (822454999/833303131 : ℝ) ^ p := by
    exact cert_lt (x := (785721619/833303131 : ℝ)) (y := (822454999/833303131 : ℝ)) (X := (6490030763389/25000000000000 : ℝ)) (Y := (37019938879877/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922566433/1000000000 : ℝ)) (n' := (833303131/1000000000 : ℝ)) (Ab := (785721619/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922566959/1000000000 : ℝ) ^ p + (198511761/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (922566959/1000000000 : ℝ)) (y := (198511761/200000000 : ℝ)) (X := (3936219086271/25000000000000 : ℝ)) (Y := (3370205569193/4000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198511761/200000000 : ℝ) ^ p + (922566959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198511761/200000000 : ℝ)) (y := (922566959/1000000000 : ℝ)) (X := (3370205569193/4000000000000 : ℝ)) (Y := (3936219086271/25000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (478781441/250000000 : ℝ)) (τ := (922566959/1000000000 : ℝ)) (σ := (198511761/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (87302465/92589306 : ℝ) ^ p + (45691979/46294653 : ℝ) ^ p := by
    exact cert_lt (x := (87302465/92589306 : ℝ)) (y := (45691979/46294653 : ℝ)) (X := (25960106815261/100000000000000 : ℝ)) (Y := (74039894506843/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922566959/1000000000 : ℝ)) (n' := (416651877/500000000 : ℝ)) (Ab := (157144437/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461283491/500000000 : ℝ) ^ p + (992558801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461283491/500000000 : ℝ)) (y := (992558801/1000000000 : ℝ)) (X := (15744885348667/100000000000000 : ℝ)) (Y := (84255131441461/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992558801/1000000000 : ℝ) ^ p + (461283491/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992558801/1000000000 : ℝ)) (y := (461283491/500000000 : ℝ)) (X := (84255131441461/100000000000000 : ℝ)) (Y := (15744885348667/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1915125783/1000000000 : ℝ)) (τ := (461283491/500000000 : ℝ)) (σ := (992558801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (261907403/277767927 : ℝ) ^ p + (91383961/92589309 : ℝ) ^ p := by
    exact cert_lt (x := (261907403/277767927 : ℝ)) (y := (91383961/92589309 : ℝ)) (X := (12980052855043/50000000000000 : ℝ)) (Y := (115687336301/156250000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461283491/500000000 : ℝ)) (n' := (833303781/1000000000 : ℝ)) (Ab := (785722209/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (115320873/125000000 : ℝ) ^ p + (2481397/2500000 : ℝ) ^ p := by
    exact cert_lt (x := (115320873/125000000 : ℝ)) (y := (2481397/2500000 : ℝ)) (X := (3936221532897/25000000000000 : ℝ)) (Y := (84255129494371/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (2481397/2500000 : ℝ) ^ p + (115320873/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (2481397/2500000 : ℝ)) (y := (115320873/125000000 : ℝ)) (X := (84255129494371/100000000000000 : ℝ)) (Y := (3936221532897/25000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785722211/833303783 : ℝ) ^ p + (822455651/833303783 : ℝ) ^ p := by
    exact cert_lt (x := (785722211/833303783 : ℝ)) (y := (822455651/833303783 : ℝ)) (X := (3245013224579/12500000000000 : ℝ)) (Y := (37019947643201/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652528973/1806851353 : ℝ) ^ p + (1796003221/1806851353 : ℝ) ^ p := by
    exact cert_lt (x := (1652528973/1806851353 : ℝ)) (y := (1796003221/1806851353 : ℝ)) (X := (12901388412607/100000000000000 : ℝ)) (Y := (43549305968133/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109562729/1193148647 : ℝ) ^ p + (1182300515/1193148647 : ℝ) ^ p := by
    exact cert_lt (x := (1109562729/1193148647 : ℝ)) (y := (1182300515/1193148647 : ℝ)) (X := (18901204378481/100000000000000 : ℝ)) (Y := (16219759223673/20000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (2481397/2500000 : ℝ)) (U := (1193148647/1000000000 : ℝ)) (Ab := (1652528973/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ)) (Ab := (1109562729/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab061 (p : ℝ) (hpa : (733/32 : ℝ) ≤ p) (hpb : p ≤ (367/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193148647/1000000000 : ℝ)) ∧ coordinateBox (4537/10000 : ℝ) (1387/1250 : ℝ) (7687/10000 : ℝ) (11843/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (321567215396387/200109000000000 : ℝ) ≤ X j i + X k i) ∧
    (116065399399673/20010900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (485096539/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(733/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (485096539/500000000 : ℝ))
      (by norm_num) 32 733 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(733/32 : ℝ)) ≤ (970193079/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970193079/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 733 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(367/16 : ℝ)) ≤ (485116539/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (485116539/500000000 : ℝ))
      (by norm_num) (by norm_num) 16 367 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (526525884617/25013625000000 : ℝ) (2712033/250000000 : ℝ) (4000000600327/20010900000000 : ℝ) (3033/2500 : ℝ) (485116539/250000000 : ℝ) (485096539/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (733/32 : ℝ)) (β := (367/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (526525884617/25013625000000 : ℝ)) (δ := (2712033/250000000 : ℝ)) (h := (4000000600327/20010900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (485096539/500000000 : ℝ)) (thia := (970193079/1000000000 : ℝ)) (thib := (485116539/500000000 : ℝ))
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
  have hh := contract21_slab061 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 62, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab062 (p : ℝ) (hpa : (367/16 : ℝ) ≤ p) (hpb : p ≤ (735/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1052868456559/50095500000000 : ℝ) (541551/50000000 : ℝ) (2000000300573/10019100000000 : ℝ) (3033/2500 : ℝ) (970272969/500000000 : ℝ) (970233077/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596580649/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11097/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4539/10000 : ℝ)
      else (7689/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1052868456559/50095500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (541551/50000000 : ℝ) := by norm_num
  have pc0 : 1 < (183335657/200000000 : ℝ) ^ p + (993677229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183335657/200000000 : ℝ)) (y := (993677229/1000000000 : ℝ)) (X := (6778606547207/50000000000000 : ℝ)) (Y := (17288560963723/20000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993677229/1000000000 : ℝ) ^ p + (183335657/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993677229/1000000000 : ℝ)) (y := (183335657/200000000 : ℝ)) (X := (17288560963723/20000000000000 : ℝ)) (Y := (6778606547207/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (955177757/500000000 : ℝ)) (τ := (183335657/200000000 : ℝ)) (σ := (993677229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779402294/826279395 : ℝ) ^ p + (54363225/55085293 : ℝ) ^ p := by
    exact cert_lt (x := (779402294/826279395 : ℝ)) (y := (54363225/55085293 : ℝ)) (X := (5229041242497/20000000000000 : ℝ)) (Y := (36927397596271/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (183335657/200000000 : ℝ)) (n' := (165255879/200000000 : ℝ)) (Ab := (389701147/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (461204737/500000000 : ℝ) ^ p + (992620699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461204737/500000000 : ℝ)) (y := (992620699/1000000000 : ℝ)) (X := (312876173411/2000000000000 : ℝ)) (Y := (84356207745457/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992620699/1000000000 : ℝ) ^ p + (461204737/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992620699/1000000000 : ℝ)) (y := (461204737/500000000 : ℝ)) (X := (84356207745457/100000000000000 : ℝ)) (Y := (312876173411/2000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1915030173/1000000000 : ℝ)) (τ := (461204737/500000000 : ℝ)) (σ := (992620699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785581277/833086588 : ℝ) ^ p + (205563892/208271647 : ℝ) ^ p := by
    exact cert_lt (x := (785581277/833086588 : ℝ)) (y := (205563892/208271647 : ℝ)) (X := (25960880518743/100000000000000 : ℝ)) (Y := (74039120382019/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (461204737/500000000 : ℝ)) (n' := (208271647/250000000 : ℝ)) (Ab := (785581277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (92266937/100000000 : ℝ) ^ p + (496284321/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (92266937/100000000 : ℝ)) (y := (496284321/500000000 : ℝ)) (X := (393634086301/2500000000000 : ℝ)) (Y := (21063663259721/25000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496284321/500000000 : ℝ) ^ p + (92266937/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496284321/500000000 : ℝ)) (y := (92266937/100000000 : ℝ)) (X := (21063663259721/25000000000000 : ℝ)) (Y := (393634086301/2500000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478809503/250000000 : ℝ)) (τ := (92266937/100000000 : ℝ)) (σ := (496284321/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785860537/833394297 : ℝ) ^ p + (274187759/277798099 : ℝ) ^ p := by
    exact cert_lt (x := (785860537/833394297 : ℝ)) (y := (274187759/277798099 : ℝ)) (X := (25952609434967/100000000000000 : ℝ)) (Y := (18511847921691/25000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (92266937/100000000 : ℝ)) (n' := (833394297/1000000000 : ℝ)) (Ab := (785860537/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922681029/1000000000 : ℝ) ^ p + (496283149/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922681029/1000000000 : ℝ)) (y := (496283149/500000000 : ℝ)) (X := (492185436599/3125000000000 : ℝ)) (Y := (84250083029977/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496283149/500000000 : ℝ) ^ p + (922681029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496283149/500000000 : ℝ)) (y := (922681029/1000000000 : ℝ)) (X := (84250083029977/100000000000000 : ℝ)) (Y := (492185436599/3125000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1915247327/1000000000 : ℝ)) (τ := (922681029/1000000000 : ℝ)) (σ := (496283149/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (785873063/833408099 : ℝ) ^ p + (822577079/833408099 : ℝ) ^ p := by
    exact cert_lt (x := (785873063/833408099 : ℝ)) (y := (822577079/833408099 : ℝ)) (X := (25952238685849/100000000000000 : ℝ)) (Y := (14809552513199/20000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922681029/1000000000 : ℝ)) (n' := (833408099/1000000000 : ℝ)) (Ab := (785873063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922681553/1000000000 : ℝ) ^ p + (62035387/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (922681553/1000000000 : ℝ)) (y := (62035387/62500000 : ℝ)) (X := (15750139417553/100000000000000 : ℝ)) (Y := (16849975274271/20000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62035387/62500000 : ℝ) ^ p + (922681553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62035387/62500000 : ℝ)) (y := (922681553/1000000000 : ℝ)) (X := (16849975274271/20000000000000 : ℝ)) (Y := (15750139417553/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383049549/200000000 : ℝ)) (τ := (922681553/1000000000 : ℝ)) (σ := (62035387/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785873626/833408719 : ℝ) ^ p + (822577699/833408719 : ℝ) ^ p := by
    exact cert_lt (x := (785873626/833408719 : ℝ)) (y := (822577699/833408719 : ℝ)) (X := (25952222273963/100000000000000 : ℝ)) (Y := (9255972403253/12500000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922681553/1000000000 : ℝ)) (n' := (833408719/1000000000 : ℝ)) (Ab := (392936813/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (36907263/40000000 : ℝ) ^ p + (248141547/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (36907263/40000000 : ℝ)) (y := (248141547/250000000 : ℝ)) (X := (787507402161/5000000000000 : ℝ)) (Y := (42124934286463/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248141547/250000000 : ℝ) ^ p + (36907263/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (248141547/250000000 : ℝ)) (y := (36907263/40000000 : ℝ)) (X := (42124934286463/50000000000000 : ℝ)) (Y := (787507402161/5000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1915247763/1000000000 : ℝ)) (τ := (36907263/40000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (261957883/277802915 : ℝ) ^ p + (54838515/55560583 : ℝ) ^ p := by
    exact cert_lt (x := (261957883/277802915 : ℝ)) (y := (54838515/55560583 : ℝ)) (X := (25952221123279/100000000000000 : ℝ)) (Y := (74047779924669/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (36907263/40000000 : ℝ)) (n' := (166681749/200000000 : ℝ)) (Ab := (785873649/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (115335197/125000000 : ℝ) ^ p + (248141547/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115335197/125000000 : ℝ)) (y := (248141547/250000000 : ℝ)) (X := (492192138603/3125000000000 : ℝ)) (Y := (42124934286463/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248141547/250000000 : ℝ) ^ p + (115335197/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248141547/250000000 : ℝ)) (y := (115335197/125000000 : ℝ)) (X := (42124934286463/50000000000000 : ℝ)) (Y := (492192138603/3125000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (392936825/416704373 : ℝ) ^ p + (411288863/416704373 : ℝ) ^ p := by
    exact cert_lt (x := (392936825/416704373 : ℝ)) (y := (411288863/416704373 : ℝ)) (X := (12976110583271/50000000000000 : ℝ)) (Y := (3702388997577/5000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652703721/1806838702 : ℝ) ^ p + (898003841/903419351 : ℝ) ^ p := by
    exact cert_lt (x := (1652703721/1806838702 : ℝ)) (y := (898003841/903419351 : ℝ)) (X := (6449401453137/50000000000000 : ℝ)) (Y := (1360956209959/1562500000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (554836967/596580649 : ℝ) ^ p + (591165139/596580649 : ℝ) ^ p := by
    exact cert_lt (x := (554836967/596580649 : ℝ)) (y := (591165139/596580649 : ℝ)) (X := (18897210825433/100000000000000 : ℝ)) (Y := (40551394805833/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248141547/250000000 : ℝ)) (U := (596580649/500000000 : ℝ)) (Ab := (1652703721/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ)) (Ab := (554836967/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab062 (p : ℝ) (hpa : (367/16 : ℝ) ≤ p) (hpb : p ≤ (735/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (596580649/500000000 : ℝ)) ∧ coordinateBox (4539/10000 : ℝ) (11097/10000 : ℝ) (7689/10000 : ℝ) (11843/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (40257243847543/25047750000000 : ℝ) ≤ X j i + X k i) ∧
    (58114599699427/10019100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (970233077/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(367/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (970233077/1000000000 : ℝ))
      (by norm_num) 16 367 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(367/16 : ℝ)) ≤ (485116539/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (485116539/500000000 : ℝ))
      (by norm_num) (by norm_num) 16 367 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(735/32 : ℝ)) ≤ (970272969/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970272969/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 735 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (1052868456559/50095500000000 : ℝ) (541551/50000000 : ℝ) (2000000300573/10019100000000 : ℝ) (3033/2500 : ℝ) (970272969/500000000 : ℝ) (970233077/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (367/16 : ℝ)) (β := (735/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1052868456559/50095500000000 : ℝ)) (δ := (541551/50000000 : ℝ)) (h := (2000000300573/10019100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (970233077/1000000000 : ℝ)) (thia := (485116539/500000000 : ℝ)) (thib := (970272969/1000000000 : ℝ))
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
  have hh := contract21_slab062 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 63, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab063 (p : ℝ) (hpa : (735/32 : ℝ) ≤ p) (hpb : p ≤ (23 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (210537079391/10032750000000 : ℝ) (5406979/500000000 : ℝ) (800000120393/4013100000000 : ℝ) (3033/2500 : ℝ) (970312753/500000000 : ℝ) (121284121/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193173941/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5549/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4541/10000 : ℝ)
      else (7691/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2961/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (210537079391/10032750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5406979/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (916797553/1000000000 : ℝ) ^ p + (496841969/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (916797553/1000000000 : ℝ)) (y := (496841969/500000000 : ℝ)) (X := (847557678889/6250000000000 : ℝ)) (Y := (86439094292877/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496841969/500000000 : ℝ) ^ p + (916797553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496841969/500000000 : ℝ)) (y := (916797553/1000000000 : ℝ)) (X := (86439094292877/100000000000000 : ℝ)) (Y := (847557678889/6250000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1910481491/1000000000 : ℝ)) (τ := (916797553/1000000000 : ℝ)) (σ := (496841969/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779559057/826391189 : ℝ) ^ p + (815577231/826391189 : ℝ) ^ p := by
    exact cert_lt (x := (779559057/826391189 : ℝ)) (y := (815577231/826391189 : ℝ)) (X := (5227413996281/20000000000000 : ℝ)) (Y := (73862931215859/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916797553/1000000000 : ℝ)) (n' := (826391189/1000000000 : ℝ)) (Ab := (779559057/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (36900979/40000000 : ℝ) ^ p + (992627939/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (36900979/40000000 : ℝ)) (y := (992627939/1000000000 : ℝ)) (X := (7824590819209/50000000000000 : ℝ)) (Y := (84350834351443/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992627939/1000000000 : ℝ) ^ p + (36900979/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (992627939/1000000000 : ℝ)) (y := (36900979/40000000 : ℝ)) (X := (84350834351443/100000000000000 : ℝ)) (Y := (7824590819209/50000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957576207/500000000 : ℝ)) (τ := (36900979/40000000 : ℝ)) (σ := (992627939/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785733100/833192141 : ℝ) ^ p + (822378183/833192141 : ℝ) ^ p := by
    exact cert_lt (x := (785733100/833192141 : ℝ)) (y := (822378183/833192141 : ℝ)) (X := (25952985804243/100000000000000 : ℝ)) (Y := (74047015038967/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (36900979/40000000 : ℝ)) (n' := (833192141/1000000000 : ℝ)) (Ab := (7857331/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184556737/200000000 : ℝ) ^ p + (198515201/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (184556737/200000000 : ℝ)) (y := (198515201/200000000 : ℝ)) (X := (49220712293/312500000000 : ℝ)) (Y := (21062347225339/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198515201/200000000 : ℝ) ^ p + (184556737/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198515201/200000000 : ℝ)) (y := (184556737/200000000 : ℝ)) (X := (21062347225339/25000000000000 : ℝ)) (Y := (49220712293/312500000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (191535969/100000000 : ℝ)) (τ := (184556737/200000000 : ℝ)) (σ := (198515201/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (786011608/833498985 : ℝ) ^ p + (822685027/833498985 : ℝ) ^ p := by
    exact cert_lt (x := (786011608/833498985 : ℝ)) (y := (822685027/833498985 : ℝ)) (X := (25944741300011/100000000000000 : ℝ)) (Y := (14811051983177/20000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184556737/200000000 : ℝ)) (n' := (166699797/200000000 : ℝ)) (Ab := (98251451/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (230698823/250000000 : ℝ) ^ p + (99257367/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (230698823/250000000 : ℝ)) (y := (99257367/100000000 : ℝ)) (X := (3938796303869/25000000000000 : ℝ)) (Y := (84244830563933/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99257367/100000000 : ℝ) ^ p + (230698823/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (99257367/100000000 : ℝ)) (y := (230698823/250000000 : ℝ)) (X := (84244830563933/100000000000000 : ℝ)) (Y := (3938796303869/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957684481/500000000 : ℝ)) (τ := (230698823/250000000 : ℝ)) (σ := (99257367/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (786024077/833512723 : ℝ) ^ p + (13486865/13664143 : ℝ) ^ p := by
    exact cert_lt (x := (786024077/833512723 : ℝ)) (y := (13486865/13664143 : ℝ)) (X := (25944372118189/100000000000000 : ℝ)) (Y := (74055628933541/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (230698823/250000000 : ℝ)) (n' := (833512723/1000000000 : ℝ)) (Ab := (786024077/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922795811/1000000000 : ℝ) ^ p + (496286783/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922795811/1000000000 : ℝ)) (y := (496286783/500000000 : ℝ)) (X := (7877694510517/50000000000000 : ℝ)) (Y := (21061156885707/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496286783/500000000 : ℝ) ^ p + (922795811/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496286783/500000000 : ℝ)) (y := (922795811/1000000000 : ℝ)) (X := (21061156885707/25000000000000 : ℝ)) (Y := (7877694510517/50000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1915369377/1000000000 : ℝ)) (τ := (922795811/1000000000 : ℝ)) (σ := (496286783/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (786024634/833513337 : ℝ) ^ p + (822699379/833513337 : ℝ) ^ p := by
    exact cert_lt (x := (786024634/833513337 : ℝ)) (y := (822699379/833513337 : ℝ)) (X := (2594435540303/10000000000000 : ℝ)) (Y := (74055645426007/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922795811/1000000000 : ℝ)) (n' := (833513337/1000000000 : ℝ)) (Ab := (393012317/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461397917/500000000 : ℝ) ^ p + (992573561/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461397917/500000000 : ℝ)) (y := (992573561/1000000000 : ℝ)) (X := (15755398052937/100000000000000 : ℝ)) (Y := (8424461778221/10000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992573561/1000000000 : ℝ) ^ p + (461397917/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992573561/1000000000 : ℝ)) (y := (461397917/500000000 : ℝ)) (X := (8424461778221/10000000000000 : ℝ)) (Y := (15755398052937/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383073879/200000000 : ℝ)) (τ := (461397917/500000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (786024659/833513364 : ℝ) ^ p + (411349703/416756682 : ℝ) ^ p := by
    exact cert_lt (x := (786024659/833513364 : ℝ)) (y := (411349703/416756682 : ℝ)) (X := (12972177526263/50000000000000 : ℝ)) (Y := (37027823075623/50000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461397917/500000000 : ℝ)) (n' := (208378341/250000000 : ℝ)) (Ab := (786024659/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (184559167/200000000 : ℝ) ^ p + (992573561/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184559167/200000000 : ℝ)) (y := (992573561/1000000000 : ℝ)) (X := (15755398445629/100000000000000 : ℝ)) (Y := (8424461778221/10000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992573561/1000000000 : ℝ) ^ p + (184559167/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992573561/1000000000 : ℝ)) (y := (184559167/200000000 : ℝ)) (X := (8424461778221/10000000000000 : ℝ)) (Y := (15755398445629/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (786024661/833513366 : ℝ) ^ p + (411349704/416756683 : ℝ) ^ p := by
    exact cert_lt (x := (786024661/833513366 : ℝ)) (y := (411349704/416756683 : ℝ)) (X := (25944355139031/100000000000000 : ℝ)) (Y := (74055646204967/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652878007/1806826059 : ℝ) ^ p + (1796012101/1806826059 : ℝ) ^ p := by
    exact cert_lt (x := (1652878007/1806826059 : ℝ)) (y := (1796012101/1806826059 : ℝ)) (X := (2579244253551/20000000000000 : ℝ)) (Y := (21775944755129/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109784886/1193173941 : ℝ) ^ p + (1182359983/1193173941 : ℝ) ^ p := by
    exact cert_lt (x := (1109784886/1193173941 : ℝ)) (y := (1182359983/1193173941 : ℝ)) (X := (9446611735843/50000000000000 : ℝ)) (Y := (81106777188273/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992573561/1000000000 : ℝ)) (U := (1193173941/1000000000 : ℝ)) (Ab := (1652878007/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ)) (Ab := (554892443/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab063 (p : ℝ) (hpa : (735/32 : ℝ) ≤ p) (hpb : p ≤ (23 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193173941/1000000000 : ℝ)) ∧ coordinateBox (4541/10000 : ℝ) (5549/5000 : ℝ) (7691/10000 : ℝ) (2961/2500 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (64509736172419/40131000000000 : ℝ) ≤ X j i + X k i) ∧
    (23278599879607/4013100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (121284121/125000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(735/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (121284121/125000000 : ℝ))
      (by norm_num) 32 735 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(735/32 : ℝ)) ≤ (970272969/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970272969/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 735 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(23 : ℝ)) ≤ (970312753/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970312753/1000000000 : ℝ))
      (by norm_num) (by norm_num) 1 23 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (210537079391/10032750000000 : ℝ) (5406979/500000000 : ℝ) (800000120393/4013100000000 : ℝ) (3033/2500 : ℝ) (970312753/500000000 : ℝ) (121284121/125000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (735/32 : ℝ)) (β := (23 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (210537079391/10032750000000 : ℝ)) (δ := (5406979/500000000 : ℝ)) (h := (800000120393/4013100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (121284121/125000000 : ℝ)) (thia := (970272969/1000000000 : ℝ)) (thib := (970312753/1000000000 : ℝ))
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
  have hh := contract21_slab063 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Finite interval decisions and all domain inclusions are Lean proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localized_nonneg21_chunk03 (p : ℝ) (hpa : (45/2 : ℝ) ≤ p)
    (hpb : p ≤ (23 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (91/4 : ℝ) with hl | hr
  ·
    rcases le_total p (181/8 : ℝ) with hll | hlr
    ·
      rcases le_total p (361/16 : ℝ) with hlll | hllr
      ·
        rcases le_total p (721/32 : ℝ) with hllll | hlllr
        ·
          have hh := localize21_slab048 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab049 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (723/32 : ℝ) with hllrl | hllrr
        ·
          have hh := localize21_slab050 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab051 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (363/16 : ℝ) with hlrl | hlrr
      ·
        rcases le_total p (725/32 : ℝ) with hlrll | hlrlr
        ·
          have hh := localize21_slab052 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab053 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (727/32 : ℝ) with hlrrl | hlrrr
        ·
          have hh := localize21_slab054 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab055 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
  ·
    rcases le_total p (183/8 : ℝ) with hrl | hrr
    ·
      rcases le_total p (365/16 : ℝ) with hrll | hrlr
      ·
        rcases le_total p (729/32 : ℝ) with hrlll | hrllr
        ·
          have hh := localize21_slab056 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab057 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (731/32 : ℝ) with hrlrl | hrlrr
        ·
          have hh := localize21_slab058 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab059 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (367/16 : ℝ) with hrrl | hrrr
      ·
        rcases le_total p (733/32 : ℝ) with hrrll | hrrlr
        ·
          have hh := localize21_slab060 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab061 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (735/32 : ℝ) with hrrrl | hrrrr
        ·
          have hh := localize21_slab062 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab063 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD

end HlawkaSchatten.DiagonalRealBundle
theorem solution :
    ∀ p : ℝ, (45/2 : ℝ) ≤ p → p ≤ (23 : ℝ) →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : HlawkaSchatten.DiagonalRealBundle.coordinateBox (189/500 : ℝ) (607/500 : ℝ)
      (349/500 : ℝ) (607/500 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox, hji] using ho j i hji
  exact HlawkaSchatten.DiagonalRealBundle.localized_nonneg21_chunk03 p hp hpmax X hB hS hT hG

#print axioms solution
