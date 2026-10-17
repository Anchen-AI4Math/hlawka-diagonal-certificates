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


/- Exact grouped numeric margins for all real p in this interval.
   The geometric/Hessian implication is a separate proof obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalRealBundle

theorem grouped_curvature_numeric01 (p : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ)) :
    p * (199510924132807956593645943815347701385438272000000/13395456032083073088062671920178417732217198614403 : ℝ) * (1415548968439149180000000000/2103874688790506220457872649 : ℝ) ^ (p - 2) < 1 ∧
    (39655345362958446107199973703409056335840135271525439312292463392711972086491265/737677061871138959562468658665502734463746253252266779117320603951206151308376 : ℝ) * (270810043198878456/379743463347292411 : ℝ) ^ (p - 2) < 2 * (273/625 : ℝ) - 1/p := by
  have hpn : 23 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hrt : (1415548968439149180000000000/2103874688790506220457872649 : ℝ) ^ (p - 2) ≤ (1415548968439149180000000000/2103874688790506220457872649 : ℝ) ^ (21 : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' (x := (1415548968439149180000000000/2103874688790506220457872649 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 21) (by linarith : (21 : ℝ) ≤ p - 2)
    calc _ ≤ (1415548968439149180000000000/2103874688790506220457872649 : ℝ) ^ ((21 : ℕ) : ℝ) := hh
         _ = _ := Real.rpow_natCast _ _
  have hrc : (270810043198878456/379743463347292411 : ℝ) ^ (p - 2) ≤ (270810043198878456/379743463347292411 : ℝ) ^ (21 : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' (x := (270810043198878456/379743463347292411 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 21) (by linarith : (21 : ℝ) ≤ p - 2)
    calc _ ≤ (270810043198878456/379743463347292411 : ℝ) ^ ((21 : ℕ) : ℝ) := hh
         _ = _ := Real.rpow_natCast _ _
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrt (show 0 ≤ p * (199510924132807956593645943815347701385438272000000/13395456032083073088062671920178417732217198614403 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (199510924132807956593645943815347701385438272000000/13395456032083073088062671920178417732217198614403 : ℝ) * (1415548968439149180000000000/2103874688790506220457872649 : ℝ) ^ (21 : ℕ) by norm_num)
    have hend : (32 : ℝ) * (199510924132807956593645943815347701385438272000000/13395456032083073088062671920178417732217198614403 : ℝ) * (1415548968439149180000000000/2103874688790506220457872649 : ℝ) ^ (21 : ℕ) < 1 := by norm_num
    nlinarith only [h1, h2, hend]
  · have h1 := mul_le_mul_of_nonneg_left hrc (show 0 ≤ (39655345362958446107199973703409056335840135271525439312292463392711972086491265/737677061871138959562468658665502734463746253252266779117320603951206151308376 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(23 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpn
    have hend : (39655345362958446107199973703409056335840135271525439312292463392711972086491265/737677061871138959562468658665502734463746253252266779117320603951206151308376 : ℝ) * (270810043198878456/379743463347292411 : ℝ) ^ (21 : ℕ) < 2 * (273/625 : ℝ) - 1/(23 : ℝ) := by norm_num
    linarith only [h1, hinv, hend]

end HlawkaSchatten.DiagonalRealBundle



/- The actual original deficit Hessian is nonnegative on this
   norm-capped convex domain for every real p in the group. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem grouped_deficit_hessian01 (p K : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ))
    (hKlo : (273/625 : ℝ)*p ≤ K) (hKhi : K ≤ p/2) :
    ∀ X : Triple, X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ)
      (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) →
    ∀ Z : Triple, 0 ≤ deficitHessian p K X Z := by
  let GT : ℝ := pairTotalFactor (4577/10000 : ℝ) (1483/1250 : ℝ) (25357735892843/51460500000000 : ℝ) (3033/2500 : ℝ) (1 : ℝ) (1/4 : ℝ)
  let GC : ℝ := pairColumnFactor (4577/10000 : ℝ) (1483/1250 : ℝ) (25357735892843/51460500000000 : ℝ) (3033/2500 : ℝ) (2203/5000 : ℝ) (82967765642843/51460500000000 : ℝ) (1 : ℝ) (1/4 : ℝ)
  have hmarg := grouped_curvature_numeric01 p hpa hpb
  have hNT : (p/2) * GT * ((3033/2500 : ℝ)/(82967765642843/51460500000000 : ℝ)) *
      (((2203/5000 : ℝ)*(3033/2500 : ℝ))/((82967765642843/51460500000000 : ℝ)*(25357735892843/51460500000000 : ℝ))) ^ (p-2) ≤ 1 := by
    have hbase : (((2203/5000 : ℝ)*(3033/2500 : ℝ))/((82967765642843/51460500000000 : ℝ)*(25357735892843/51460500000000 : ℝ))) = (1415548968439149180000000000/2103874688790506220457872649 : ℝ) := by norm_num
    have hconst : GT * ((3033/2500 : ℝ)/(82967765642843/51460500000000 : ℝ)) / 2 = (199510924132807956593645943815347701385438272000000/13395456032083073088062671920178417732217198614403 : ℝ) := by
      norm_num [GT, pairTotalFactor, shapeFactor]
    have hprod : (p/2) * GT * ((3033/2500 : ℝ)/(82967765642843/51460500000000 : ℝ)) = p * (199510924132807956593645943815347701385438272000000/13395456032083073088062671920178417732217198614403 : ℝ) := by
      calc _ = p * (GT * ((3033/2500 : ℝ)/(82967765642843/51460500000000 : ℝ)) / 2) := by ring
           _ = _ := by rw [hconst]
    rw [hbase, hprod]
    exact hmarg.1.le
  have hNC : (GC/2) * ((149298789/125000000 : ℝ)/(82967765642843/51460500000000 : ℝ)) *
      (((2203/5000 : ℝ)*(149298789/125000000 : ℝ))/((82967765642843/51460500000000 : ℝ)*(4577/10000 : ℝ))) ^ (p-2) ≤ 2*(273/625 : ℝ)-1/p := by
    have hbase : (((2203/5000 : ℝ)*(149298789/125000000 : ℝ))/((82967765642843/51460500000000 : ℝ)*(4577/10000 : ℝ))) = (270810043198878456/379743463347292411 : ℝ) := by norm_num
    have hconst : (GC/2) * ((149298789/125000000 : ℝ)/(82967765642843/51460500000000 : ℝ)) = (39655345362958446107199973703409056335840135271525439312292463392711972086491265/737677061871138959562468658665502734463746253252266779117320603951206151308376 : ℝ) := by
      norm_num [GC, pairColumnFactor, shapeFactor]
    rw [hbase, hconst]
    exact hmarg.2.le
  have hcoef := curvature_coefficients_from_ratios (p := p) (K := K) (c := (273/625 : ℝ))
    (m := (4577/10000 : ℝ)) (s := (25357735892843/51460500000000 : ℝ)) (U := (149298789/125000000 : ℝ)) (A := (3033/2500 : ℝ))
    (eta := (2203/5000 : ℝ)) (L := (82967765642843/51460500000000 : ℝ)) (gT := GT) (gC := GC)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num [GT, pairTotalFactor, shapeFactor])
    (by norm_num [GC, pairColumnFactor, shapeFactor])
    hKlo hKhi hNT hNC
  intro X hX Z
  exact deficit_hessian_domain_nonneg (m := (4577/10000 : ℝ)) (M := (1483/1250 : ℝ))
    (L := (82967765642843/51460500000000 : ℝ)) (s := (25357735892843/51460500000000 : ℝ)) (t := (3033/2500 : ℝ)) (eta := (2203/5000 : ℝ))
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

theorem grouped_deficit_convex01 (p K : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ))
    (hKlo : (273/625 : ℝ)*p ≤ K) (hKhi : K ≤ p/2) :
    ConvexOn ℝ (normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ))
      (tripleDeficit p K) := by
  exact normCappedDomain_deficit_convex (L := (82967765642843/51460500000000 : ℝ)) (s := (25357735892843/51460500000000 : ℝ)) (t := (3033/2500 : ℝ)) (eta := (2203/5000 : ℝ))
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (grouped_deficit_hessian01 p K hpa hpb hKlo hKhi)

end HlawkaSchatten.DiagonalRealBundle


set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem grouped_deficit_nonneg01 (p : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ))
    (X : Triple) (hX : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hK := cyclicConstant_bounds_window (p := p) (by linarith) (by linarith)
  exact normDomain_deficit_nonneg_of_convex (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
    (grouped_deficit_convex01 p (cyclicConstant p) hpa hpb hK.1.le hK.2) hX

end HlawkaSchatten.DiagonalRealBundle


/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 80, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab080 (p : ℝ) (hpa : (47/2 : ℝ) ≤ p) (hpb : p ≤ (753/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (131205997583/6415500000000 : ℝ) (10531809/1000000000 : ℝ) (250000038493/1283100000000 : ℝ) (3033/2500 : ℝ) (970973159/500000000 : ℝ) (7767481/8000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149173699/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11117/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4573/10000 : ℝ)
      else (7723/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (131205997583/6415500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10531809/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (918774257/1000000000 : ℝ) ^ p + (993795983/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918774257/1000000000 : ℝ)) (y := (993795983/1000000000 : ℝ)) (X := (13622521584217/100000000000000 : ℝ)) (Y := (21594373857181/25000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993795983/1000000000 : ℝ) ^ p + (918774257/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993795983/1000000000 : ℝ)) (y := (918774257/1000000000 : ℝ)) (X := (21594373857181/25000000000000 : ℝ)) (Y := (13622521584217/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (2988391/1562500 : ℝ)) (τ := (918774257/1000000000 : ℝ)) (σ := (993795983/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782159155/828237652 : ℝ) ^ p + (817705843/828237652 : ℝ) ^ p := by
    exact cert_lt (x := (782159155/828237652 : ℝ)) (y := (817705843/828237652 : ℝ)) (X := (5200522270717/20000000000000 : ℝ)) (Y := (73997389864723/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (918774257/1000000000 : ℝ)) (n' := (207059413/250000000 : ℝ)) (Ab := (156431831/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (184885669/200000000 : ℝ) ^ p + (496374613/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184885669/200000000 : ℝ)) (y := (496374613/500000000 : ℝ)) (X := (1573819763849/10000000000000 : ℝ)) (Y := (16852363748263/20000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496374613/500000000 : ℝ) ^ p + (184885669/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496374613/500000000 : ℝ)) (y := (184885669/200000000 : ℝ)) (X := (16852363748263/20000000000000 : ℝ)) (Y := (1573819763849/10000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917177571/1000000000 : ℝ)) (τ := (184885669/200000000 : ℝ)) (σ := (496374613/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394124585/417466473 : ℝ) ^ p + (274800379/278310982 : ℝ) ^ p := by
    exact cert_lt (x := (394124585/417466473 : ℝ)) (y := (274800379/278310982 : ℝ)) (X := (129112810263/500000000000 : ℝ)) (Y := (18544359717167/25000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (184885669/200000000 : ℝ)) (n' := (417466473/500000000 : ℝ)) (Ab := (78824917/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (46233813/50000000 : ℝ) ^ p + (24817483/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (46233813/50000000 : ℝ)) (y := (24817483/25000000 : ℝ)) (X := (15837816642099/100000000000000 : ℝ)) (Y := (42081099765173/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24817483/25000000 : ℝ) ^ p + (46233813/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (24817483/25000000 : ℝ)) (y := (46233813/50000000 : ℝ)) (X := (42081099765173/50000000000000 : ℝ)) (Y := (15837816642099/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (95868779/50000000 : ℝ)) (τ := (46233813/50000000 : ℝ)) (σ := (24817483/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (197128829/208806399 : ℝ) ^ p + (91632643/92802844 : ℝ) ^ p := by
    exact cert_lt (x := (197128829/208806399 : ℝ)) (y := (91632643/92802844 : ℝ)) (X := (5162949707309/20000000000000 : ℝ)) (Y := (74185252408999/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (46233813/50000000 : ℝ)) (n' := (208806399/250000000 : ℝ)) (Ab := (197128829/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (115585877/125000000 : ℝ) ^ p + (992697147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115585877/125000000 : ℝ)) (y := (992697147/1000000000 : ℝ)) (X := (792107616647/5000000000000 : ℝ)) (Y := (21039466121943/25000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992697147/1000000000 : ℝ) ^ p + (115585877/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992697147/1000000000 : ℝ)) (y := (115585877/125000000 : ℝ)) (X := (21039466121943/25000000000000 : ℝ)) (Y := (792107616647/5000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1917384163/1000000000 : ℝ)) (τ := (115585877/125000000 : ℝ)) (σ := (992697147/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (788526861/835238291 : ℝ) ^ p + (824706482/835238291 : ℝ) ^ p := by
    exact cert_lt (x := (788526861/835238291 : ℝ)) (y := (824706482/835238291 : ℝ)) (X := (6453602389251/25000000000000 : ℝ)) (Y := (74185591250103/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (115585877/125000000 : ℝ)) (n' := (835238291/1000000000 : ℝ)) (Ab := (788526861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (462343741/500000000 : ℝ) ^ p + (992697053/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462343741/500000000 : ℝ)) (y := (992697053/1000000000 : ℝ)) (X := (7921170100469/50000000000000 : ℝ)) (Y := (42078838483297/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992697053/1000000000 : ℝ) ^ p + (462343741/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992697053/1000000000 : ℝ)) (y := (462343741/500000000 : ℝ)) (X := (42078838483297/50000000000000 : ℝ)) (Y := (7921170100469/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383476907/200000000 : ℝ)) (τ := (462343741/500000000 : ℝ)) (σ := (992697053/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (262842454/278412947 : ℝ) ^ p + (274902344/278412947 : ℝ) ^ p := by
    exact cert_lt (x := (262842454/278412947 : ℝ)) (y := (274902344/278412947 : ℝ)) (X := (5162879101031/20000000000000 : ℝ)) (Y := (4636600370619/6250000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (462343741/500000000 : ℝ)) (n' := (835238841/1000000000 : ℝ)) (Ab := (394263681/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (462343751/500000000 : ℝ) ^ p + (992697049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462343751/500000000 : ℝ)) (y := (992697049/1000000000 : ℝ)) (X := (1584234826399/10000000000000 : ℝ)) (Y := (42078834493489/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992697049/1000000000 : ℝ) ^ p + (462343751/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992697049/1000000000 : ℝ)) (y := (462343751/500000000 : ℝ)) (X := (42078834493489/50000000000000 : ℝ)) (Y := (1584234826399/10000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917384551/1000000000 : ℝ)) (τ := (462343751/500000000 : ℝ)) (σ := (992697049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (262842461/278412955 : ℝ) ^ p + (274902352/278412955 : ℝ) ^ p := by
    exact cert_lt (x := (262842461/278412955 : ℝ)) (y := (274902352/278412955 : ℝ)) (X := (25814394228079/100000000000000 : ℝ)) (Y := (74185606570477/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (462343751/500000000 : ℝ)) (n' := (167047773/200000000 : ℝ)) (Ab := (788527383/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (57792969/62500000 : ℝ) ^ p + (124087131/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (57792969/62500000 : ℝ)) (y := (124087131/125000000 : ℝ)) (X := (3168469814059/20000000000000 : ℝ)) (Y := (3366306679683/4000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124087131/125000000 : ℝ) ^ p + (57792969/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (124087131/125000000 : ℝ)) (y := (57792969/62500000 : ℝ)) (X := (3366306679683/4000000000000 : ℝ)) (Y := (3168469814059/20000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (788527385/835238867 : ℝ) ^ p + (824707058/835238867 : ℝ) ^ p := by
    exact cert_lt (x := (788527385/835238867 : ℝ)) (y := (824707058/835238867 : ℝ)) (X := (6453598578561/25000000000000 : ℝ)) (Y := (37092803311929/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1655773071/1806610408 : ℝ) ^ p + (1796078599/1806610408 : ℝ) ^ p := by
    exact cert_lt (x := (1655773071/1806610408 : ℝ)) (y := (1796078599/1806610408 : ℝ)) (X := (2570691573043/20000000000000 : ℝ)) (Y := (87146542359111/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1111636723/1193389592 : ℝ) ^ p + (1182857783/1193389592 : ℝ) ^ p := by
    exact cert_lt (x := (1111636723/1193389592 : ℝ)) (y := (1182857783/1193389592 : ℝ)) (X := (30123255391/160000000000 : ℝ)) (Y := (81172966114103/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124087131/125000000 : ℝ)) (U := (149173699/125000000 : ℝ)) (Ab := (1655773071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ)) (Ab := (1111636723/1000000000 : ℝ))
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

theorem localize21_slab080 (p : ℝ) (hpa : (47/2 : ℝ) ≤ p) (hpb : p ≤ (753/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (149173699/125000000 : ℝ)) ∧ coordinateBox (4573/10000 : ℝ) (11117/10000 : ℝ) (7723/10000 : ℝ) (11847/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (10340309008369/6415500000000 : ℝ) ≤ X j i + X k i) ∧
    (7448599961507/1283100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (7767481/8000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(47/2 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (7767481/8000000 : ℝ))
      (by norm_num) 2 47 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(47/2 : ℝ)) ≤ (485467563/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (485467563/500000000 : ℝ))
      (by norm_num) (by norm_num) 2 47 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(753/32 : ℝ)) ≤ (970973159/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970973159/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 753 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (131205997583/6415500000000 : ℝ) (10531809/1000000000 : ℝ) (250000038493/1283100000000 : ℝ) (3033/2500 : ℝ) (970973159/500000000 : ℝ) (7767481/8000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (47/2 : ℝ)) (β := (753/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (131205997583/6415500000000 : ℝ)) (δ := (10531809/1000000000 : ℝ)) (h := (250000038493/1283100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (7767481/8000000 : ℝ)) (thia := (485467563/500000000 : ℝ)) (thib := (970973159/1000000000 : ℝ))
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
  have hh := contract21_slab080 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 81, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab081 (p : ℝ) (hpa : (753/32 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524736762737/25696125000000 : ℝ) (10515663/1000000000 : ℝ) (4000000616707/20556900000000 : ℝ) (3033/2500 : ℝ) (971011093/500000000 : ℝ) (485486579/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193402307/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5559/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(183/400 : ℝ)
      else (309/400 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524736762737/25696125000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10515663/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (114860953/125000000 : ℝ) ^ p + (993802457/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114860953/125000000 : ℝ)) (y := (993802457/1000000000 : ℝ)) (X := (2725212357493/20000000000000 : ℝ)) (Y := (269918610639/312500000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993802457/1000000000 : ℝ) ^ p + (114860953/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993802457/1000000000 : ℝ)) (y := (114860953/125000000 : ℝ)) (X := (269918610639/312500000000 : ℝ)) (Y := (2725212357493/20000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1912690081/1000000000 : ℝ)) (τ := (114860953/125000000 : ℝ)) (σ := (993802457/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782308386/828343187 : ℝ) ^ p + (817827524/828343187 : ℝ) ^ p := by
    exact cert_lt (x := (782308386/828343187 : ℝ)) (y := (817827524/828343187 : ℝ)) (X := (25994920080693/100000000000000 : ℝ)) (Y := (37002540486539/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (114860953/125000000 : ℝ)) (n' := (828343187/1000000000 : ℝ)) (Ab := (391154193/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924537413/1000000000 : ℝ) ^ p + (31023633/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (924537413/1000000000 : ℝ)) (y := (31023633/31250000 : ℝ)) (X := (1967912644871/12500000000000 : ℝ)) (Y := (21064179030813/25000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (31023633/31250000 : ℝ) ^ p + (924537413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31023633/31250000 : ℝ)) (y := (924537413/1000000000 : ℝ)) (X := (21064179030813/25000000000000 : ℝ)) (Y := (1967912644871/12500000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917293669/1000000000 : ℝ)) (τ := (924537413/1000000000 : ℝ)) (σ := (31023633/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (788393459/835032294 : ℝ) ^ p + (30537653/30927122 : ℝ) ^ p := by
    exact cert_lt (x := (788393459/835032294 : ℝ)) (y := (30537653/30927122 : ℝ)) (X := (12907552371539/50000000000000 : ℝ)) (Y := (18546224150263/25000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924537413/1000000000 : ℝ)) (n' := (417516147/500000000 : ℝ)) (Ab := (788393459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184956937/200000000 : ℝ) ^ p + (496353233/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184956937/200000000 : ℝ)) (y := (496353233/500000000 : ℝ)) (X := (15842813863173/100000000000000 : ℝ)) (Y := (10519650394139/12500000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496353233/500000000 : ℝ) ^ p + (184956937/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496353233/500000000 : ℝ)) (y := (184956937/200000000 : ℝ)) (X := (10519650394139/12500000000000 : ℝ)) (Y := (15842813863173/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1917491151/1000000000 : ℝ)) (τ := (184956937/200000000 : ℝ)) (σ := (496353233/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (394329451/417662069 : ℝ) ^ p + (824808475/835324138 : ℝ) ^ p := by
    exact cert_lt (x := (394329451/417662069 : ℝ)) (y := (824808475/835324138 : ℝ)) (X := (25807315596639/100000000000000 : ℝ)) (Y := (7419268577983/10000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184956937/200000000 : ℝ)) (n' := (417662069/500000000 : ℝ)) (Ab := (394329451/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (924795393/1000000000 : ℝ) ^ p + (496352151/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924795393/1000000000 : ℝ)) (y := (496352151/500000000 : ℝ)) (X := (15847136792657/100000000000000 : ℝ)) (Y := (4207644030971/5000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496352151/500000000 : ℝ) ^ p + (924795393/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496352151/500000000 : ℝ)) (y := (924795393/1000000000 : ℝ)) (X := (4207644030971/5000000000000 : ℝ)) (Y := (15847136792657/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (383499939/200000000 : ℝ)) (τ := (924795393/1000000000 : ℝ)) (σ := (496352151/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (157734079/167067355 : ℝ) ^ p + (824821112/835336775 : ℝ) ^ p := by
    exact cert_lt (x := (157734079/167067355 : ℝ)) (y := (824821112/835336775 : ℝ)) (X := (2580697786191/10000000000000 : ℝ)) (Y := (18548255737537/25000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (924795393/1000000000 : ℝ)) (n' := (33413471/40000000 : ℝ)) (Ab := (157734079/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (924795857/1000000000 : ℝ) ^ p + (62044013/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (924795857/1000000000 : ℝ)) (y := (62044013/62500000 : ℝ)) (X := (15847324139749/100000000000000 : ℝ)) (Y := (84152692861683/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62044013/62500000 : ℝ) ^ p + (924795857/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62044013/62500000 : ℝ)) (y := (924795857/1000000000 : ℝ)) (X := (84152692861683/100000000000000 : ℝ)) (Y := (15847324139749/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383500013/200000000 : ℝ)) (τ := (924795857/1000000000 : ℝ)) (σ := (62044013/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (788670893/835337322 : ℝ) ^ p + (91646851/92815258 : ℝ) ^ p := by
    exact cert_lt (x := (788670893/835337322 : ℝ)) (y := (91646851/92815258 : ℝ)) (X := (12903481821563/50000000000000 : ℝ)) (Y := (37096518772283/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (924795857/1000000000 : ℝ)) (n' := (417668661/500000000 : ℝ)) (Ab := (788670893/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924795877/1000000000 : ℝ) ^ p + (248176051/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (924795877/1000000000 : ℝ)) (y := (248176051/250000000 : ℝ)) (X := (7923666107551/50000000000000 : ℝ)) (Y := (84152684872001/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248176051/250000000 : ℝ) ^ p + (924795877/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248176051/250000000 : ℝ)) (y := (924795877/1000000000 : ℝ)) (X := (84152684872001/100000000000000 : ℝ)) (Y := (7923666107551/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917500081/1000000000 : ℝ)) (τ := (924795877/1000000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (262890305/278445782 : ℝ) ^ p + (274940561/278445782 : ℝ) ^ p := by
    exact cert_lt (x := (262890305/278445782 : ℝ)) (y := (274940561/278445782 : ℝ)) (X := (516139262697/2000000000000 : ℝ)) (Y := (37096519092453/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924795877/1000000000 : ℝ)) (n' := (417668673/500000000 : ℝ)) (Ab := (157734183/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (462397939/500000000 : ℝ) ^ p + (248176051/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (462397939/500000000 : ℝ)) (y := (248176051/250000000 : ℝ)) (X := (1584733261887/10000000000000 : ℝ)) (Y := (84152684872001/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248176051/250000000 : ℝ) ^ p + (462397939/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248176051/250000000 : ℝ)) (y := (462397939/500000000 : ℝ)) (X := (84152684872001/100000000000000 : ℝ)) (Y := (1584733261887/10000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (788670916/835337347 : ℝ) ^ p + (824821684/835337347 : ℝ) ^ p := by
    exact cert_lt (x := (788670916/835337347 : ℝ)) (y := (824821684/835337347 : ℝ)) (X := (25806963177923/100000000000000 : ℝ)) (Y := (74193038211587/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (183993275/200733077 : ℝ) ^ p + (199564670/200733077 : ℝ) ^ p := by
    exact cert_lt (x := (183993275/200733077 : ℝ)) (y := (199564670/200733077 : ℝ)) (X := (1285100589099/10000000000000 : ℝ)) (Y := (87148994457979/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1111743665/1193402307 : ℝ) ^ p + (394295548/397800769 : ℝ) ^ p := by
    exact cert_lt (x := (1111743665/1193402307 : ℝ)) (y := (394295548/397800769 : ℝ)) (X := (1176451973209/6250000000000 : ℝ)) (Y := (10147096127623/12500000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248176051/250000000 : ℝ)) (U := (1193402307/1000000000 : ℝ)) (Ab := (66237579/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ)) (Ab := (222348733/200000000 : ℝ))
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

theorem localize21_slab081 (p : ℝ) (hpa : (753/32 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193402307/1000000000 : ℝ)) ∧ coordinateBox (183/400 : ℝ) (5559/5000 : ℝ) (309/400 : ℝ) (11847/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (331380479096627/205569000000000 : ℝ) ≤ X j i + X k i) ∧
    (119341399383293/20556900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (485486579/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(753/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (485486579/500000000 : ℝ))
      (by norm_num) 32 753 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(753/32 : ℝ)) ≤ (970973159/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (970973159/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 753 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(377/16 : ℝ)) ≤ (971011093/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971011093/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 377 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (524736762737/25696125000000 : ℝ) (10515663/1000000000 : ℝ) (4000000616707/20556900000000 : ℝ) (3033/2500 : ℝ) (971011093/500000000 : ℝ) (485486579/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (753/32 : ℝ)) (β := (377/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (524736762737/25696125000000 : ℝ)) (δ := (10515663/1000000000 : ℝ)) (h := (4000000616707/20556900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (485486579/500000000 : ℝ)) (thia := (970973159/1000000000 : ℝ)) (thib := (971011093/1000000000 : ℝ))
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
  have hh := contract21_slab081 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 82, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab082 (p : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (755/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524649825887/25730250000000 : ℝ) (5249783/500000000 : ℝ) (2000000308763/10292100000000 : ℝ) (3033/2500 : ℝ) (30345279/15625000 : ℝ) (242752773/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (74588439/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(11119/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4577/10000 : ℝ)
      else (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524649825887/25730250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5249783/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (28718771/31250000 : ℝ) ^ p + (993808919/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28718771/31250000 : ℝ)) (y := (993808919/1000000000 : ℝ)) (X := (13629591495481/100000000000000 : ℝ)) (Y := (43185212999281/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993808919/1000000000 : ℝ) ^ p + (28718771/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (993808919/1000000000 : ℝ)) (y := (28718771/31250000 : ℝ)) (X := (43185212999281/50000000000000 : ℝ)) (Y := (13629591495481/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1912809591/1000000000 : ℝ)) (τ := (28718771/31250000 : ℝ)) (σ := (993808919/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782457212/828448385 : ℝ) ^ p + (817948819/828448385 : ℝ) ^ p := by
    exact cert_lt (x := (782457212/828448385 : ℝ)) (y := (817948819/828448385 : ℝ)) (X := (25987253692531/100000000000000 : ℝ)) (Y := (37006373878639/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (28718771/31250000 : ℝ)) (n' := (165689677/200000000 : ℝ)) (Ab := (195614303/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924646163/1000000000 : ℝ) ^ p + (496381637/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924646163/1000000000 : ℝ)) (y := (496381637/500000000 : ℝ)) (X := (1968548687373/12500000000000 : ℝ)) (Y := (84251626975181/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496381637/500000000 : ℝ) ^ p + (924646163/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496381637/500000000 : ℝ)) (y := (924646163/1000000000 : ℝ)) (X := (84251626975181/100000000000000 : ℝ)) (Y := (1968548687373/12500000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917409437/1000000000 : ℝ)) (τ := (924646163/1000000000 : ℝ)) (σ := (496381637/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (112648192/119304473 : ℝ) ^ p + (117804535/119304473 : ℝ) ^ p := by
    exact cert_lt (x := (112648192/119304473 : ℝ)) (y := (117804535/119304473 : ℝ)) (X := (25807670494197/100000000000000 : ℝ)) (Y := (1483846610407/2000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924646163/1000000000 : ℝ)) (n' := (835131311/1000000000 : ℝ)) (Ab := (1540112/1953125 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184978559/200000000 : ℝ) ^ p + (310223/312500 : ℝ) ^ p := by
    exact cert_lt (x := (184978559/200000000 : ℝ)) (y := (310223/312500 : ℝ)) (X := (3169559262067/20000000000000 : ℝ)) (Y := (84152220829893/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (310223/312500 : ℝ) ^ p + (184978559/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (310223/312500 : ℝ)) (y := (184978559/200000000 : ℝ)) (X := (84152220829893/100000000000000 : ℝ)) (Y := (3169559262067/20000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (383521279/200000000 : ℝ)) (τ := (184978559/200000000 : ℝ)) (σ := (310223/312500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (788802088/835422353 : ℝ) ^ p + (824922787/835422353 : ℝ) ^ p := by
    exact cert_lt (x := (788802088/835422353 : ℝ)) (y := (824922787/835422353 : ℝ)) (X := (12899953021659/50000000000000 : ℝ)) (Y := (74200095469613/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184978559/200000000 : ℝ)) (n' := (835422353/1000000000 : ℝ)) (Ab := (98600261/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (924903457/1000000000 : ℝ) ^ p + (248177861/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (924903457/1000000000 : ℝ)) (y := (248177861/250000000 : ℝ)) (X := (15852107227663/100000000000000 : ℝ)) (Y := (84147908850421/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248177861/250000000 : ℝ) ^ p + (924903457/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248177861/250000000 : ℝ)) (y := (924903457/1000000000 : ℝ)) (X := (84147908850421/100000000000000 : ℝ)) (Y := (15852107227663/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1917614901/1000000000 : ℝ)) (τ := (924903457/1000000000 : ℝ)) (σ := (248177861/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (788813531/835434933 : ℝ) ^ p + (824935367/835434933 : ℝ) ^ p := by
    exact cert_lt (x := (788813531/835434933 : ℝ)) (y := (824935367/835434933 : ℝ)) (X := (6449892594319/25000000000000 : ℝ)) (Y := (18550107749339/25000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (924903457/1000000000 : ℝ)) (n' := (835434933/1000000000 : ℝ)) (Ab := (788813531/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (924903917/1000000000 : ℝ) ^ p + (992711351/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924903917/1000000000 : ℝ)) (y := (992711351/1000000000 : ℝ)) (X := (15852293242611/100000000000000 : ℝ)) (Y := (84147722856067/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992711351/1000000000 : ℝ) ^ p + (924903917/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992711351/1000000000 : ℝ)) (y := (924903917/1000000000 : ℝ)) (X := (84147722856067/100000000000000 : ℝ)) (Y := (15852293242611/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479403817/250000000 : ℝ)) (τ := (924903917/1000000000 : ℝ)) (σ := (992711351/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (788814025/835435476 : ℝ) ^ p + (412467955/417717738 : ℝ) ^ p := by
    exact cert_lt (x := (788814025/835435476 : ℝ)) (y := (412467955/417717738 : ℝ)) (X := (12899777974277/50000000000000 : ℝ)) (Y := (74200445479797/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (924903917/1000000000 : ℝ)) (n' := (208858869/250000000 : ℝ)) (Ab := (31552561/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924903937/1000000000 : ℝ) ^ p + (992711347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924903937/1000000000 : ℝ)) (y := (992711347/1000000000 : ℝ)) (X := (3170460266053/20000000000000 : ℝ)) (Y := (42073857428159/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992711347/1000000000 : ℝ) ^ p + (924903937/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992711347/1000000000 : ℝ)) (y := (924903937/1000000000 : ℝ)) (X := (42073857428159/50000000000000 : ℝ)) (Y := (3170460266053/20000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (479403821/250000000 : ℝ)) (τ := (924903937/1000000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (788814046/835435499 : ℝ) ^ p + (824935933/835435499 : ℝ) ^ p := by
    exact cert_lt (x := (788814046/835435499 : ℝ)) (y := (824935933/835435499 : ℝ)) (X := (1289977769783/5000000000000 : ℝ)) (Y := (74200446093233/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924903937/1000000000 : ℝ)) (n' := (835435499/1000000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (462451969/500000000 : ℝ) ^ p + (992711347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462451969/500000000 : ℝ)) (y := (992711347/1000000000 : ℝ)) (X := (15852301734647/100000000000000 : ℝ)) (Y := (42073857428159/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992711347/1000000000 : ℝ) ^ p + (462451969/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992711347/1000000000 : ℝ)) (y := (462451969/500000000 : ℝ)) (X := (42073857428159/50000000000000 : ℝ)) (Y := (15852301734647/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (394407023/417717750 : ℝ) ^ p + (412467967/417717750 : ℝ) ^ p := by
    exact cert_lt (x := (394407023/417717750 : ℝ)) (y := (412467967/417717750 : ℝ)) (X := (3224944333381/12500000000000 : ℝ)) (Y := (14840089223981/20000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (118293247/129041784 : ℝ) ^ p + (128291815/129041784 : ℝ) ^ p := by
    exact cert_lt (x := (118293247/129041784 : ℝ)) (y := (128291815/129041784 : ℝ)) (X := (6424280481607/50000000000000 : ℝ)) (Y := (43575719675521/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (370616797/397805008 : ℝ) ^ p + (591457729/596707512 : ℝ) ^ p := by
    exact cert_lt (x := (370616797/397805008 : ℝ)) (y := (591457729/596707512 : ℝ)) (X := (18819438846113/100000000000000 : ℝ)) (Y := (81180561609109/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992711347/1000000000 : ℝ)) (U := (74588439/62500000 : ℝ)) (Ab := (828052729/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ)) (Ab := (1111850391/1000000000 : ℝ))
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

theorem localize21_slab082 (p : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (755/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (74588439/62500000 : ℝ)) ∧ coordinateBox (4577/10000 : ℝ) (11119/10000 : ℝ) (3863/5000 : ℝ) (1481/1250 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
    (59752599691237/10292100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (242752773/250000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(377/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (242752773/250000000 : ℝ))
      (by norm_num) 16 377 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(377/16 : ℝ)) ≤ (971011093/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971011093/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 377 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(755/32 : ℝ)) ≤ (30345279/31250000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (30345279/31250000 : ℝ))
      (by norm_num) (by norm_num) 32 755 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (524649825887/25730250000000 : ℝ) (5249783/500000000 : ℝ) (2000000308763/10292100000000 : ℝ) (3033/2500 : ℝ) (30345279/15625000 : ℝ) (242752773/250000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (377/16 : ℝ)) (β := (755/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (524649825887/25730250000000 : ℝ)) (δ := (5249783/500000000 : ℝ)) (h := (2000000308763/10292100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (242752773/250000000 : ℝ)) (thia := (971011093/1000000000 : ℝ)) (thib := (30345279/31250000 : ℝ))
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
  have hh := contract21_slab082 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 83, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab083 (p : ℝ) (hpa : (755/32 : ℝ) ≤ p) (hpb : p ≤ (189/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (419650495177/20611500000000 : ℝ) (5241759/500000000 : ℝ) (800000123669/4122300000000 : ℝ) (3033/2500 : ℝ) (121385833/62500000 : ℝ) (971048927/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238685549/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(139/125 : ℝ) ≤ X j i ∧ X j i ≤ -(4579/10000 : ℝ)
      else (483/625 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (419650495177/20611500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5241759/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (459556703/500000000 : ℝ) ^ p + (124226921/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (459556703/500000000 : ℝ)) (y := (124226921/125000000 : ℝ)) (X := (6816556015563/50000000000000 : ℝ)) (Y := (10795863132367/12500000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124226921/125000000 : ℝ) ^ p + (459556703/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124226921/125000000 : ℝ)) (y := (459556703/500000000 : ℝ)) (X := (10795863132367/12500000000000 : ℝ)) (Y := (6816556015563/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (956464387/500000000 : ℝ)) (τ := (459556703/500000000 : ℝ)) (σ := (124226921/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (391302818/414276625 : ℝ) ^ p + (409034866/414276625 : ℝ) ^ p := by
    exact cert_lt (x := (391302818/414276625 : ℝ)) (y := (409034866/414276625 : ℝ)) (X := (25979611331253/100000000000000 : ℝ)) (Y := (74020389925271/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459556703/500000000 : ℝ)) (n' := (3314213/4000000 : ℝ)) (Ab := (195651409/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924754599/1000000000 : ℝ) ^ p + (992770281/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924754599/1000000000 : ℝ)) (y := (992770281/1000000000 : ℝ)) (X := (7876731885243/50000000000000 : ℝ)) (Y := (16849310640833/20000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992770281/1000000000 : ℝ) ^ p + (924754599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992770281/1000000000 : ℝ)) (y := (924754599/1000000000 : ℝ)) (X := (16849310640833/20000000000000 : ℝ)) (Y := (7876731885243/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (23969061/12500000 : ℝ)) (τ := (924754599/1000000000 : ℝ)) (σ := (992770281/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (26289361/27841000 : ℝ) ^ p + (137457747/139205000 : ℝ) ^ p := by
    exact cert_lt (x := (26289361/27841000 : ℝ)) (y := (137457747/139205000 : ℝ)) (X := (12900130362629/50000000000000 : ℝ)) (Y := (74199740307691/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924754599/1000000000 : ℝ)) (n' := (83523/100000 : ℝ)) (Ab := (78868083/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (57812537/62500000 : ℝ) ^ p + (496360361/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (57812537/62500000 : ℝ)) (y := (496360361/500000000 : ℝ)) (X := (7926382148883/50000000000000 : ℝ)) (Y := (42073626231489/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496360361/500000000 : ℝ) ^ p + (57812537/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (496360361/500000000 : ℝ)) (y := (57812537/62500000 : ℝ)) (X := (42073626231489/50000000000000 : ℝ)) (Y := (7926382148883/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958860657/500000000 : ℝ)) (τ := (57812537/62500000 : ℝ)) (σ := (496360361/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (394472438/417760121 : ℝ) ^ p + (412518362/417760121 : ℝ) ^ p := by
    exact cert_lt (x := (394472438/417760121 : ℝ)) (y := (412518362/417760121 : ℝ)) (X := (5158504087269/20000000000000 : ℝ)) (Y := (74207481106001/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (57812537/62500000 : ℝ)) (n' := (417760121/500000000 : ℝ)) (Ab := (197236219/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462505603/500000000 : ℝ) ^ p + (62044911/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (462505603/500000000 : ℝ)) (y := (62044911/62500000 : ℝ)) (X := (1585706233593/10000000000000 : ℝ)) (Y := (84142955082891/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (62044911/62500000 : ℝ) ^ p + (462505603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62044911/62500000 : ℝ)) (y := (462505603/500000000 : ℝ)) (X := (84142955082891/100000000000000 : ℝ)) (Y := (1585706233593/10000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (958864891/500000000 : ℝ)) (τ := (462505603/500000000 : ℝ)) (σ := (62044911/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (262985422/278510921 : ℝ) ^ p + (275016415/278510921 : ℝ) ^ p := by
    exact cert_lt (x := (262985422/278510921 : ℝ)) (y := (275016415/278510921 : ℝ)) (X := (322402324887/1250000000000 : ℝ)) (Y := (14841562987873/20000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (462505603/500000000 : ℝ)) (n' := (835532763/1000000000 : ℝ)) (Ab := (394478133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (57813229/62500000 : ℝ) ^ p + (992718483/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57813229/62500000 : ℝ)) (y := (992718483/1000000000 : ℝ)) (X := (792862391189/5000000000000 : ℝ)) (Y := (84142768854489/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992718483/1000000000 : ℝ) ^ p + (57813229/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992718483/1000000000 : ℝ)) (y := (57813229/62500000 : ℝ)) (X := (84142768854489/100000000000000 : ℝ)) (Y := (792862391189/5000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1917730147/1000000000 : ℝ)) (τ := (57813229/62500000 : ℝ)) (σ := (992718483/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (262985586/278511101 : ℝ) ^ p + (275016595/278511101 : ℝ) ^ p := by
    exact cert_lt (x := (262985586/278511101 : ℝ)) (y := (275016595/278511101 : ℝ)) (X := (25792172167773/100000000000000 : ℝ)) (Y := (37103914668293/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (57813229/62500000 : ℝ)) (n' := (835533303/1000000000 : ℝ)) (Ab := (394478379/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (231252921/250000000 : ℝ) ^ p + (992718479/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231252921/250000000 : ℝ)) (y := (992718479/1000000000 : ℝ)) (X := (15857255923733/100000000000000 : ℝ)) (Y := (42071380422337/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992718479/1000000000 : ℝ) ^ p + (231252921/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992718479/1000000000 : ℝ)) (y := (231252921/250000000 : ℝ)) (X := (42071380422337/50000000000000 : ℝ)) (Y := (15857255923733/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (262985593/278511109 : ℝ) ^ p + (275016603/278511109 : ℝ) ^ p := by
    exact cert_lt (x := (262985593/278511109 : ℝ)) (y := (275016603/278511109 : ℝ)) (X := (25792170884051/100000000000000 : ℝ)) (Y := (37103914988231/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1656271022/1806572255 : ℝ) ^ p + (1796088737/1806572255 : ℝ) ^ p := by
    exact cert_lt (x := (1656271022/1806572255 : ℝ)) (y := (1796088737/1806572255 : ℝ)) (X := (6423061743699/50000000000000 : ℝ)) (Y := (680889662517/781250000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (222391381/238685549 : ℝ) ^ p + (1182944227/1193427745 : ℝ) ^ p := by
    exact cert_lt (x := (222391381/238685549 : ℝ)) (y := (1182944227/1193427745 : ℝ)) (X := (9407828477887/50000000000000 : ℝ)) (Y := (20296085898099/25000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992718479/1000000000 : ℝ)) (U := (238685549/200000000 : ℝ)) (Ab := (828135511/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ)) (Ab := (222391381/200000000 : ℝ))
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

theorem localize21_slab083 (p : ℝ) (hpa : (755/32 : ℝ) ≤ p) (hpb : p ≤ (189/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (238685549/200000000 : ℝ)) ∧ coordinateBox (4579/10000 : ℝ) (139/125 : ℝ) (483/625 : ℝ) (1481/1250 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (13294465531127/8244600000000 : ℝ) ≤ X j i + X k i) ∧
    (23933799876331/4122300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (971048927/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(755/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (971048927/1000000000 : ℝ))
      (by norm_num) 32 755 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(755/32 : ℝ)) ≤ (30345279/31250000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (30345279/31250000 : ℝ))
      (by norm_num) (by norm_num) 32 755 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(189/8 : ℝ)) ≤ (121385833/125000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (121385833/125000000 : ℝ))
      (by norm_num) (by norm_num) 8 189 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (419650495177/20611500000000 : ℝ) (5241759/500000000 : ℝ) (800000123669/4122300000000 : ℝ) (3033/2500 : ℝ) (121385833/62500000 : ℝ) (971048927/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (755/32 : ℝ)) (β := (189/8 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (419650495177/20611500000000 : ℝ)) (δ := (5241759/500000000 : ℝ)) (h := (800000123669/4122300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (971048927/1000000000 : ℝ)) (thia := (30345279/31250000 : ℝ)) (thib := (121385833/125000000 : ℝ))
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
  have hh := contract21_slab083 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 84, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab084 (p : ℝ) (hpa : (189/8 : ℝ) ≤ p) (hpb : p ≤ (757/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524476581179/25798500000000 : ℝ) (10467517/1000000000 : ℝ) (1000000154791/5159700000000 : ℝ) (3033/2500 : ℝ) (971124301/500000000 : ℝ) (971086663/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596720231/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11121/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(229/500 : ℝ)
      else (773/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524476581179/25798500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10467517/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (114903229/125000000 : ℝ) ^ p + (248455451/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (114903229/125000000 : ℝ)) (y := (248455451/250000000 : ℝ)) (X := (13636625078099/100000000000000 : ℝ)) (Y := (17272678495769/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248455451/250000000 : ℝ) ^ p + (114903229/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248455451/250000000 : ℝ)) (y := (114903229/125000000 : ℝ)) (X := (17272678495769/20000000000000 : ℝ)) (Y := (13636625078099/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (478261909/250000000 : ℝ)) (τ := (114903229/125000000 : ℝ)) (σ := (248455451/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782753664/828657793 : ℝ) ^ p + (818190276/828657793 : ℝ) ^ p := by
    exact cert_lt (x := (782753664/828657793 : ℝ)) (y := (818190276/828657793 : ℝ)) (X := (12985994650721/50000000000000 : ℝ)) (Y := (18507002913709/25000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (114903229/125000000 : ℝ)) (n' := (828657793/1000000000 : ℝ)) (Ab := (6115263/7812500 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (231215681/250000000 : ℝ) ^ p + (248194319/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (231215681/250000000 : ℝ)) (y := (248194319/250000000 : ℝ)) (X := (7879262345849/50000000000000 : ℝ)) (Y := (42120746356347/50000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248194319/250000000 : ℝ) ^ p + (231215681/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248194319/250000000 : ℝ)) (y := (231215681/250000000 : ℝ)) (X := (42120746356347/50000000000000 : ℝ)) (Y := (7879262345849/50000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (47941/25000 : ℝ)) (τ := (231215681/250000000 : ℝ)) (σ := (248194319/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394411959/417664184 : ℝ) ^ p + (824860851/835328368 : ℝ) ^ p := by
    exact cert_lt (x := (394411959/417664184 : ℝ)) (y := (824860851/835328368 : ℝ)) (X := (25792870845437/100000000000000 : ℝ)) (Y := (1484142600143/2000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (231215681/250000000 : ℝ)) (n' := (52208023/62500000 : ℝ)) (Ab := (394411959/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (11563851/12500000 : ℝ) ^ p + (124090979/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (11563851/12500000 : ℝ)) (y := (124090979/125000000 : ℝ)) (X := (495553717347/3125000000000 : ℝ)) (Y := (84142297954689/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124090979/125000000 : ℝ) ^ p + (11563851/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (124090979/125000000 : ℝ)) (y := (11563851/12500000 : ℝ)) (X := (84142297954689/100000000000000 : ℝ)) (Y := (495553717347/3125000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (239729489/125000000 : ℝ)) (τ := (11563851/12500000 : ℝ)) (σ := (124090979/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (789087267/835617812 : ℝ) ^ p + (825150295/835617812 : ℝ) ^ p := by
    exact cert_lt (x := (789087267/835617812 : ℝ)) (y := (825150295/835617812 : ℝ)) (X := (6446288546437/25000000000000 : ℝ)) (Y := (9276855841483/12500000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (11563851/12500000 : ℝ)) (n' := (208904453/250000000 : ℝ)) (Ab := (789087267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (115639831/125000000 : ℝ) ^ p + (496362847/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115639831/125000000 : ℝ)) (y := (496362847/500000000 : ℝ)) (X := (15862004866121/100000000000000 : ℝ)) (Y := (16827602242871/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496362847/500000000 : ℝ) ^ p + (115639831/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362847/500000000 : ℝ)) (y := (115639831/125000000 : ℝ)) (X := (16827602242871/20000000000000 : ℝ)) (Y := (15862004866121/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (958922171/500000000 : ℝ)) (τ := (115639831/125000000 : ℝ)) (σ := (496362847/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (789098608/835630277 : ℝ) ^ p + (825162760/835630277 : ℝ) ^ p := by
    exact cert_lt (x := (789098608/835630277 : ℝ)) (y := (825162760/835630277 : ℝ)) (X := (2578482187241/10000000000000 : ℝ)) (Y := (74215178952311/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (115639831/125000000 : ℝ)) (n' := (835630277/1000000000 : ℝ)) (Ab := (49318663/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925119103/1000000000 : ℝ) ^ p + (496362801/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925119103/1000000000 : ℝ)) (y := (496362801/500000000 : ℝ)) (X := (15862189418803/100000000000000 : ℝ)) (Y := (84137826756883/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496362801/500000000 : ℝ) ^ p + (925119103/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362801/500000000 : ℝ)) (y := (925119103/1000000000 : ℝ)) (X := (84137826756883/100000000000000 : ℝ)) (Y := (15862189418803/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383568941/200000000 : ℝ)) (τ := (925119103/1000000000 : ℝ)) (σ := (496362801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789099097/835630814 : ℝ) ^ p + (825163297/835630814 : ℝ) ^ p := by
    exact cert_lt (x := (789099097/835630814 : ℝ)) (y := (825163297/835630814 : ℝ)) (X := (5156961576629/20000000000000 : ℝ)) (Y := (14843038652877/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925119103/1000000000 : ℝ)) (n' := (417815407/500000000 : ℝ)) (Ab := (789099097/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925119123/1000000000 : ℝ) ^ p + (496362799/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925119123/1000000000 : ℝ)) (y := (496362799/500000000 : ℝ)) (X := (991387345691/6250000000000 : ℝ)) (Y := (84137818737001/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496362799/500000000 : ℝ) ^ p + (925119123/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362799/500000000 : ℝ)) (y := (925119123/1000000000 : ℝ)) (X := (84137818737001/100000000000000 : ℝ)) (Y := (991387345691/6250000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917844721/1000000000 : ℝ)) (τ := (925119123/1000000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789099119/835630838 : ℝ) ^ p + (825163321/835630838 : ℝ) ^ p := by
    exact cert_lt (x := (789099119/835630838 : ℝ)) (y := (825163321/835630838 : ℝ)) (X := (12892403685103/50000000000000 : ℝ)) (Y := (74215193904031/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925119123/1000000000 : ℝ)) (n' := (417815419/500000000 : ℝ)) (Ab := (789099119/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (231279781/250000000 : ℝ) ^ p + (496362799/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (231279781/250000000 : ℝ)) (y := (496362799/500000000 : ℝ)) (X := (3965549484167/25000000000000 : ℝ)) (Y := (84137818737001/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496362799/500000000 : ℝ) ^ p + (231279781/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362799/500000000 : ℝ)) (y := (231279781/250000000 : ℝ)) (X := (84137818737001/100000000000000 : ℝ)) (Y := (3965549484167/25000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (87677680/92847871 : ℝ) ^ p + (825163322/835630839 : ℝ) ^ p := by
    exact cert_lt (x := (87677680/92847871 : ℝ)) (y := (825163322/835630839 : ℝ)) (X := (103139229653/400000000000 : ℝ)) (Y := (74215193930683/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (828218082/903279769 : ℝ) ^ p + (1796092021/1806559538 : ℝ) ^ p := by
    exact cert_lt (x := (828218082/903279769 : ℝ)) (y := (1796092021/1806559538 : ℝ)) (X := (513747650937/4000000000000 : ℝ)) (Y := (87156308937621/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112063193/1193440462 : ℝ) ^ p + (1182972945/1193440462 : ℝ) ^ p := by
    exact cert_lt (x := (1112063193/1193440462 : ℝ)) (y := (1182972945/1193440462 : ℝ)) (X := (752475317671/4000000000000 : ℝ)) (Y := (16237623557879/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496362799/500000000 : ℝ)) (U := (596720231/500000000 : ℝ)) (Ab := (414109041/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ)) (Ab := (1112063193/1000000000 : ℝ))
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

theorem localize21_slab084 (p : ℝ) (hpa : (189/8 : ℝ) ≤ p) (hpb : p ≤ (757/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (596720231/500000000 : ℝ)) ∧ coordinateBox (229/500 : ℝ) (11121/10000 : ℝ) (773/1000 : ℝ) (1481/1250 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (10401631495777/6449625000000 : ℝ) ≤ X j i + X k i) ∧
    (29958199845209/5159700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (971086663/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(189/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (971086663/1000000000 : ℝ))
      (by norm_num) 8 189 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(189/8 : ℝ)) ≤ (121385833/125000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (121385833/125000000 : ℝ))
      (by norm_num) (by norm_num) 8 189 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(757/32 : ℝ)) ≤ (971124301/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971124301/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 757 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (524476581179/25798500000000 : ℝ) (10467517/1000000000 : ℝ) (1000000154791/5159700000000 : ℝ) (3033/2500 : ℝ) (971124301/500000000 : ℝ) (971086663/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (189/8 : ℝ)) (β := (757/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (524476581179/25798500000000 : ℝ)) (δ := (10467517/1000000000 : ℝ)) (h := (1000000154791/5159700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (971086663/1000000000 : ℝ)) (thia := (121385833/125000000 : ℝ)) (thib := (971124301/1000000000 : ℝ))
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
  have hh := contract21_slab084 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 85, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab085 (p : ℝ) (hpa : (757/32 : ℝ) ≤ p) (hpb : p ≤ (379/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1048780303399/51665250000000 : ℝ) (5225781/500000000 : ℝ) (4000000619983/20666100000000 : ℝ) (3033/2500 : ℝ) (971161841/500000000 : ℝ) (9711243/10000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596726587/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5561/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2291/5000 : ℝ)
      else (1933/2500 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1048780303399/51665250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5225781/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (919337951/1000000000 : ℝ) ^ p + (993828227/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919337951/1000000000 : ℝ)) (y := (993828227/1000000000 : ℝ)) (X := (6820065287397/50000000000000 : ℝ)) (Y := (21589972037889/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993828227/1000000000 : ℝ) ^ p + (919337951/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993828227/1000000000 : ℝ)) (y := (919337951/1000000000 : ℝ)) (X := (21589972037889/25000000000000 : ℝ)) (Y := (6820065287397/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (956583089/500000000 : ℝ)) (τ := (919337951/1000000000 : ℝ)) (σ := (993828227/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782901297/828762016 : ℝ) ^ p + (409155227/414381008 : ℝ) ^ p := by
    exact cert_lt (x := (782901297/828762016 : ℝ)) (y := (409155227/414381008 : ℝ)) (X := (12982193322839/50000000000000 : ℝ)) (Y := (74035614758843/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (919337951/1000000000 : ℝ)) (n' := (25898813/31250000 : ℝ)) (Ab := (782901297/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924970543/1000000000 : ℝ) ^ p + (496392129/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924970543/1000000000 : ℝ)) (y := (496392129/500000000 : ℝ)) (X := (7881786897559/50000000000000 : ℝ)) (Y := (84236443393221/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496392129/500000000 : ℝ) ^ p + (924970543/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496392129/500000000 : ℝ)) (y := (924970543/1000000000 : ℝ)) (X := (84236443393221/100000000000000 : ℝ)) (Y := (7881786897559/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917754801/1000000000 : ℝ)) (τ := (924970543/1000000000 : ℝ)) (σ := (496392129/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (788966614/835426423 : ℝ) ^ p + (824974861/835426423 : ℝ) ^ p := by
    exact cert_lt (x := (788966614/835426423 : ℝ)) (y := (824974861/835426423 : ℝ)) (X := (25785499388049/100000000000000 : ℝ)) (Y := (9276812697513/12500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924970543/1000000000 : ℝ)) (n' := (835426423/1000000000 : ℝ)) (Ab := (394483307/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185043053/200000000 : ℝ) ^ p + (992734929/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185043053/200000000 : ℝ)) (y := (992734929/1000000000 : ℝ)) (X := (1239270487/7812500000 : ℝ)) (Y := (84137355199789/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992734929/1000000000 : ℝ) ^ p + (185043053/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992734929/1000000000 : ℝ)) (y := (185043053/200000000 : ℝ)) (X := (84137355199789/100000000000000 : ℝ)) (Y := (1239270487/7812500000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958975097/500000000 : ℝ)) (τ := (185043053/200000000 : ℝ)) (σ := (992734929/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (789229270/835715073 : ℝ) ^ p + (275087837/278571691 : ℝ) ^ p := by
    exact cert_lt (x := (789229270/835715073 : ℝ)) (y := (275087837/278571691 : ℝ)) (X := (6444451670863/25000000000000 : ℝ)) (Y := (37111097180587/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185043053/200000000 : ℝ)) (n' := (835715073/1000000000 : ℝ)) (Ab := (78922927/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462612893/500000000 : ℝ) ^ p + (310229/312500 : ℝ) ^ p := by
    exact cert_lt (x := (462612893/500000000 : ℝ)) (y := (310229/312500 : ℝ)) (X := (15866935555001/100000000000000 : ℝ)) (Y := (10516635143381/12500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (310229/312500 : ℝ) ^ p + (462612893/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (310229/312500 : ℝ)) (y := (462612893/500000000 : ℝ)) (X := (10516635143381/12500000000000 : ℝ)) (Y := (15866935555001/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (958979293/500000000 : ℝ)) (τ := (462612893/500000000 : ℝ)) (σ := (310229/312500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (19731014/20893187 : ℝ) ^ p + (412637959/417863740 : ℝ) ^ p := by
    exact cert_lt (x := (19731014/20893187 : ℝ)) (y := (412637959/417863740 : ℝ)) (X := (2577747642663/10000000000000 : ℝ)) (Y := (74222524916837/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (462612893/500000000 : ℝ)) (n' := (20893187/25000000 : ℝ)) (Ab := (9865507/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925226239/1000000000 : ℝ) ^ p + (248183177/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925226239/1000000000 : ℝ)) (y := (248183177/250000000 : ℝ)) (X := (7933559787531/50000000000000 : ℝ)) (Y := (21033224114513/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248183177/250000000 : ℝ) ^ p + (925226239/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248183177/250000000 : ℝ)) (y := (925226239/1000000000 : ℝ)) (X := (21033224114513/25000000000000 : ℝ)) (Y := (7933559787531/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1917958947/1000000000 : ℝ)) (τ := (925226239/1000000000 : ℝ)) (σ := (248183177/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (263080349/278576005 : ℝ) ^ p + (275092151/278576005 : ℝ) ^ p := by
    exact cert_lt (x := (263080349/278576005 : ℝ)) (y := (275092151/278576005 : ℝ)) (X := (2577746231439/10000000000000 : ℝ)) (Y := (74222539170479/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925226239/1000000000 : ℝ)) (n' := (167145603/200000000 : ℝ)) (Ab := (789241047/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925226257/1000000000 : ℝ) ^ p + (198546541/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (925226257/1000000000 : ℝ)) (y := (198546541/200000000 : ℝ)) (X := (396678172179/2500000000000 : ℝ)) (Y := (84132890435591/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198546541/200000000 : ℝ) ^ p + (925226257/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198546541/200000000 : ℝ)) (y := (925226257/1000000000 : ℝ)) (X := (84132890435591/100000000000000 : ℝ)) (Y := (396678172179/2500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (958979481/500000000 : ℝ)) (τ := (925226257/1000000000 : ℝ)) (σ := (198546541/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (394620533/417864018 : ℝ) ^ p + (12504189/12662546 : ℝ) ^ p := by
    exact cert_lt (x := (394620533/417864018 : ℝ)) (y := (12504189/12662546 : ℝ)) (X := (12888730835397/50000000000000 : ℝ)) (Y := (74222539729967/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925226257/1000000000 : ℝ)) (n' := (208932009/250000000 : ℝ)) (Ab := (394620533/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (925226259/1000000000 : ℝ) ^ p + (31022897/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (925226259/1000000000 : ℝ)) (y := (31022897/31250000 : ℝ)) (X := (3173425539923/20000000000000 : ℝ)) (Y := (10516611053513/12500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (31022897/31250000 : ℝ) ^ p + (925226259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31022897/31250000 : ℝ)) (y := (925226259/1000000000 : ℝ)) (X := (10516611053513/12500000000000 : ℝ)) (Y := (3173425539923/20000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (394620534/417864019 : ℝ) ^ p + (412638238/417864019 : ℝ) ^ p := by
    exact cert_lt (x := (394620534/417864019 : ℝ)) (y := (412638238/417864019 : ℝ)) (X := (25777461756863/100000000000000 : ℝ)) (Y := (18555634945813/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (828300441/903273413 : ℝ) ^ p + (898047632/903273413 : ℝ) ^ p := by
    exact cert_lt (x := (828300441/903273413 : ℝ)) (y := (898047632/903273413 : ℝ)) (X := (12841263485307/100000000000000 : ℝ)) (Y := (21789684174973/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112169251/1193453174 : ℝ) ^ p + (591500806/596726587 : ℝ) ^ p := by
    exact cert_lt (x := (1112169251/1193453174 : ℝ)) (y := (591500806/596726587 : ℝ)) (X := (1880811522893/10000000000000 : ℝ)) (Y := (81191885510091/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (31022897/31250000 : ℝ)) (U := (596726587/500000000 : ℝ)) (Ab := (828300441/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ)) (Ab := (1112169251/1000000000 : ℝ))
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

theorem localize21_slab085 (p : ℝ) (hpa : (757/32 : ℝ) ≤ p) (hpb : p ≤ (379/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (596726587/500000000 : ℝ)) ∧ coordinateBox (2291/5000 : ℝ) (5561/5000 : ℝ) (1933/2500 : ℝ) (1481/1250 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (2604240402667/1614539062500 : ℝ) ≤ X j i + X k i) ∧
    (119996599380017/20666100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (9711243/10000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(757/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (9711243/10000000 : ℝ))
      (by norm_num) 32 757 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(757/32 : ℝ)) ≤ (971124301/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971124301/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 757 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(379/16 : ℝ)) ≤ (971161841/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971161841/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 379 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (1048780303399/51665250000000 : ℝ) (5225781/500000000 : ℝ) (4000000619983/20666100000000 : ℝ) (3033/2500 : ℝ) (971161841/500000000 : ℝ) (9711243/10000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (757/32 : ℝ)) (β := (379/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1048780303399/51665250000000 : ℝ)) (δ := (5225781/500000000 : ℝ)) (h := (4000000619983/20666100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (9711243/10000000 : ℝ)) (thia := (971124301/1000000000 : ℝ)) (thib := (971161841/1000000000 : ℝ))
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
  have hh := contract21_slab085 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 86, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab086 (p : ℝ) (hpa : (379/16 : ℝ) ≤ p) (hpb : p ≤ (759/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524304080123/25866750000000 : ℝ) (10435657/1000000000 : ℝ) (2000000310401/10346700000000 : ℝ) (3033/2500 : ℝ) (242799821/125000000 : ℝ) (12139523/12500000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193465897/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11123/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(573/1250 : ℝ)
      else (3867/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524304080123/25866750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10435657/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (183889951/200000000 : ℝ) ^ p + (993834637/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183889951/200000000 : ℝ)) (y := (993834637/1000000000 : ℝ)) (X := (13643625293691/100000000000000 : ℝ)) (Y := (86356391970357/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993834637/1000000000 : ℝ) ^ p + (183889951/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993834637/1000000000 : ℝ)) (y := (183889951/200000000 : ℝ)) (X := (86356391970357/100000000000000 : ℝ)) (Y := (13643625293691/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (239160549/125000000 : ℝ)) (τ := (183889951/200000000 : ℝ)) (σ := (993834637/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783048530/828865903 : ℝ) ^ p + (818430246/828865903 : ℝ) ^ p := by
    exact cert_lt (x := (783048530/828865903 : ℝ)) (y := (818430246/828865903 : ℝ)) (X := (12978405528459/50000000000000 : ℝ)) (Y := (3702159492279/5000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (183889951/200000000 : ℝ)) (n' := (828865903/1000000000 : ℝ)) (Ab := (78304853/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185015609/200000000 : ℝ) ^ p + (99279123/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (185015609/200000000 : ℝ)) (y := (99279123/100000000 : ℝ)) (X := (15768606156211/100000000000000 : ℝ)) (Y := (42115705588821/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99279123/100000000 : ℝ) ^ p + (185015609/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (99279123/100000000 : ℝ)) (y := (185015609/200000000 : ℝ)) (X := (42115705588821/50000000000000 : ℝ)) (Y := (15768606156211/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (76714771/40000000 : ℝ)) (τ := (185015609/200000000 : ℝ)) (σ := (99279123/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394554455/417762072 : ℝ) ^ p + (825088487/835524144 : ℝ) ^ p := by
    exact cert_lt (x := (394554455/417762072 : ℝ)) (y := (825088487/835524144 : ℝ)) (X := (3222269406941/12500000000000 : ℝ)) (Y := (74221845557471/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185015609/200000000 : ℝ)) (n' := (52220259/62500000 : ℝ)) (Ab := (78910891/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185064427/200000000 : ℝ) ^ p + (198548403/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (185064427/200000000 : ℝ)) (y := (198548403/200000000 : ℝ)) (X := (7933794388803/50000000000000 : ℝ)) (Y := (2103310702833/2500000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198548403/200000000 : ℝ) ^ p + (185064427/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198548403/200000000 : ℝ)) (y := (185064427/200000000 : ℝ)) (X := (2103310702833/2500000000000 : ℝ)) (Y := (7933794388803/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (38361283/20000000 : ℝ)) (τ := (185064427/200000000 : ℝ)) (σ := (198548403/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (789370876/835812003 : ℝ) ^ p + (825376346/835812003 : ℝ) ^ p := by
    exact cert_lt (x := (789370876/835812003 : ℝ)) (y := (825376346/835812003 : ℝ)) (X := (6442621695713/25000000000000 : ℝ)) (Y := (74229514500547/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185064427/200000000 : ℝ)) (n' := (835812003/1000000000 : ℝ)) (Ab := (197342719/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (92533261/100000000 : ℝ) ^ p + (198547979/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (92533261/100000000 : ℝ)) (y := (198547979/200000000 : ℝ)) (X := (15871849857359/100000000000000 : ℝ)) (Y := (84128166793363/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198547979/200000000 : ℝ) ^ p + (92533261/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198547979/200000000 : ℝ)) (y := (92533261/100000000 : ℝ)) (X := (84128166793363/100000000000000 : ℝ)) (Y := (15871849857359/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (383614501/200000000 : ℝ)) (τ := (92533261/100000000 : ℝ)) (σ := (198547979/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (131563686/139304059 : ℝ) ^ p + (825388697/835824354 : ℝ) ^ p := by
    exact cert_lt (x := (131563686/139304059 : ℝ)) (y := (825388697/835824354 : ℝ)) (X := (6442539476149/25000000000000 : ℝ)) (Y := (74229843446249/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (92533261/100000000 : ℝ)) (n' := (417912177/500000000 : ℝ)) (Ab := (197345529/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (46266653/50000000 : ℝ) ^ p + (248184951/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (46266653/50000000 : ℝ)) (y := (248184951/250000000 : ℝ)) (X := (496001029233/3125000000000 : ℝ)) (Y := (42063991941421/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248184951/250000000 : ℝ) ^ p + (46266653/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (248184951/250000000 : ℝ)) (y := (46266653/50000000 : ℝ)) (X := (42063991941421/50000000000000 : ℝ)) (Y := (496001029233/3125000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (59939777/31250000 : ℝ)) (τ := (46266653/50000000 : ℝ)) (σ := (248184951/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (263127533/278608295 : ℝ) ^ p + (825389228/835824885 : ℝ) ^ p := by
    exact cert_lt (x := (263127533/278608295 : ℝ)) (y := (825389228/835824885 : ℝ)) (X := (25770143583367/100000000000000 : ℝ)) (Y := (74229857588251/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (46266653/50000000 : ℝ)) (n' := (167164977/200000000 : ℝ)) (Ab := (789382599/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925333079/1000000000 : ℝ) ^ p + (4963699/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (925333079/1000000000 : ℝ)) (y := (4963699/5000000 : ℝ)) (X := (3174408133093/20000000000000 : ℝ)) (Y := (84127975842827/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (4963699/5000000 : ℝ) ^ p + (925333079/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (4963699/5000000 : ℝ)) (y := (925333079/1000000000 : ℝ)) (X := (84127975842827/100000000000000 : ℝ)) (Y := (3174408133093/20000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918072879/1000000000 : ℝ)) (τ := (925333079/1000000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789382619/835824907 : ℝ) ^ p + (825389250/835824907 : ℝ) ^ p := by
    exact cert_lt (x := (789382619/835824907 : ℝ)) (y := (825389250/835824907 : ℝ)) (X := (3221267872659/12500000000000 : ℝ)) (Y := (18557464543543/25000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925333079/1000000000 : ℝ)) (n' := (835824907/1000000000 : ℝ)) (Ab := (789382619/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (23133327/25000000 : ℝ) ^ p + (4963699/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (23133327/25000000 : ℝ)) (y := (4963699/5000000 : ℝ)) (X := (15872041072307/100000000000000 : ℝ)) (Y := (84127975842827/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (4963699/5000000 : ℝ) ^ p + (23133327/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (4963699/5000000 : ℝ)) (y := (23133327/25000000 : ℝ)) (X := (84127975842827/100000000000000 : ℝ)) (Y := (15872041072307/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (197345655/208956227 : ℝ) ^ p + (825389251/835824908 : ℝ) ^ p := by
    exact cert_lt (x := (197345655/208956227 : ℝ)) (y := (825389251/835824908 : ℝ)) (X := (3221267878037/12500000000000 : ℝ)) (Y := (18557464550201/25000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1656765190/1806534103 : ℝ) ^ p + (1796098446/1806534103 : ℝ) ^ p := by
    exact cert_lt (x := (1656765190/1806534103 : ℝ)) (y := (1796098446/1806534103 : ℝ)) (X := (1283884509157/10000000000000 : ℝ)) (Y := (43580577584753/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112275111/1193465897 : ℝ) ^ p + (1183030240/1193465897 : ℝ) ^ p := by
    exact cert_lt (x := (1112275111/1193465897 : ℝ)) (y := (1183030240/1193465897 : ℝ)) (X := (18804360320143/100000000000000 : ℝ)) (Y := (81195640175637/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (4963699/5000000 : ℝ)) (U := (1193465897/1000000000 : ℝ)) (Ab := (165676519/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ)) (Ab := (1112275111/1000000000 : ℝ))
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

theorem localize21_slab086 (p : ℝ) (hpa : (379/16 : ℝ) ≤ p) (hpb : p ≤ (759/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193465897/1000000000 : ℝ)) ∧ coordinateBox (573/1250 : ℝ) (11123/10000 : ℝ) (3867/5000 : ℝ) (11849/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (166916663000431/103467000000000 : ℝ) ≤ X j i + X k i) ∧
    (60080199689599/10346700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (12139523/12500000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(379/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (12139523/12500000 : ℝ))
      (by norm_num) 16 379 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(379/16 : ℝ)) ≤ (971161841/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971161841/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 379 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(759/32 : ℝ)) ≤ (242799821/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (242799821/250000000 : ℝ))
      (by norm_num) (by norm_num) 32 759 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (524304080123/25866750000000 : ℝ) (10435657/1000000000 : ℝ) (2000000310401/10346700000000 : ℝ) (3033/2500 : ℝ) (242799821/125000000 : ℝ) (12139523/12500000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (379/16 : ℝ)) (β := (759/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (524304080123/25866750000000 : ℝ)) (δ := (10435657/1000000000 : ℝ)) (h := (2000000310401/10346700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (12139523/12500000 : ℝ)) (thia := (971161841/1000000000 : ℝ)) (thib := (242799821/250000000 : ℝ))
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
  have hh := contract21_slab086 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 87, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab087 (p : ℝ) (hpa : (759/32 : ℝ) ≤ p) (hpb : p ≤ (95/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2096873227469/103603500000000 : ℝ) (10419801/1000000000 : ℝ) (4000000621621/20720700000000 : ℝ) (3033/2500 : ℝ) (971236629/500000000 : ℝ) (971199283/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (9547829/8000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2781/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2293/5000 : ℝ)
      else (1547/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2096873227469/103603500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10419801/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (919561247/1000000000 : ℝ) ^ p + (248460259/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (919561247/1000000000 : ℝ)) (y := (248460259/250000000 : ℝ)) (X := (1705888733473/12500000000000 : ℝ)) (Y := (86352907955739/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248460259/250000000 : ℝ) ^ p + (919561247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248460259/250000000 : ℝ)) (y := (919561247/1000000000 : ℝ)) (X := (86352907955739/100000000000000 : ℝ)) (Y := (1705888733473/12500000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913402283/1000000000 : ℝ)) (τ := (919561247/1000000000 : ℝ)) (σ := (248460259/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (71199579/75360860 : ℝ) ^ p + (818549659/828969460 : ℝ) ^ p := by
    exact cert_lt (x := (71199579/75360860 : ℝ)) (y := (818549659/828969460 : ℝ)) (X := (25949262558339/100000000000000 : ℝ)) (Y := (37025369408611/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (919561247/1000000000 : ℝ)) (n' := (41448473/50000000 : ℝ)) (Ab := (783195369/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185037047/200000000 : ℝ) ^ p + (992798191/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185037047/200000000 : ℝ)) (y := (992798191/1000000000 : ℝ)) (X := (3943405825401/25000000000000 : ℝ)) (Y := (4211319698427/5000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992798191/1000000000 : ℝ) ^ p + (185037047/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992798191/1000000000 : ℝ)) (y := (185037047/200000000 : ℝ)) (X := (4211319698427/5000000000000 : ℝ)) (Y := (3943405825401/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (958991713/500000000 : ℝ)) (τ := (185037047/200000000 : ℝ)) (σ := (992798191/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (263083604/278540513 : ℝ) ^ p + (275067246/278540513 : ℝ) ^ p := by
    exact cert_lt (x := (263083604/278540513 : ℝ)) (y := (275067246/278540513 : ℝ)) (X := (1610677312601/6250000000000 : ℝ)) (Y := (74229163881759/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185037047/200000000 : ℝ)) (n' := (835621539/1000000000 : ℝ)) (Ab := (197312703/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115678587/125000000 : ℝ) ^ p + (99274909/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (115678587/125000000 : ℝ)) (y := (99274909/100000000 : ℝ)) (X := (7936250266881/50000000000000 : ℝ)) (Y := (84127516605247/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99274909/100000000 : ℝ) ^ p + (115678587/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (99274909/100000000 : ℝ)) (y := (115678587/125000000 : ℝ)) (X := (84127516605247/100000000000000 : ℝ)) (Y := (7936250266881/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (959088893/500000000 : ℝ)) (τ := (115678587/125000000 : ℝ)) (σ := (99274909/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (78951209/83590861 : ℝ) ^ p + (825488809/835908610 : ℝ) ^ p := by
    exact cert_lt (x := (78951209/83590861 : ℝ)) (y := (825488809/835908610 : ℝ)) (X := (25763192263521/100000000000000 : ℝ)) (Y := (18559202272941/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115678587/125000000 : ℝ)) (n' := (83590861/100000000 : ℝ)) (Ab := (78951209/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (7403513/8000000 : ℝ) ^ p + (992746979/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7403513/8000000 : ℝ)) (y := (992746979/1000000000 : ℝ)) (X := (3969187328681/25000000000000 : ℝ)) (Y := (42061634031633/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992746979/1000000000 : ℝ) ^ p + (7403513/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992746979/1000000000 : ℝ)) (y := (7403513/8000000 : ℝ)) (X := (42061634031633/50000000000000 : ℝ)) (Y := (3969187328681/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239773263/125000000 : ℝ)) (τ := (7403513/8000000 : ℝ)) (σ := (992746979/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (263174427/278640302 : ℝ) ^ p + (275167035/278640302 : ℝ) ^ p := by
    exact cert_lt (x := (263174427/278640302 : ℝ)) (y := (275167035/278640302 : ℝ)) (X := (2576286481587/10000000000000 : ℝ)) (Y := (37118568227811/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (7403513/8000000 : ℝ)) (n' := (417960453/500000000 : ℝ)) (Ab := (789523281/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231359893/250000000 : ℝ) ^ p + (124093361/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (231359893/250000000 : ℝ)) (y := (124093361/125000000 : ℝ)) (X := (7938465723571/50000000000000 : ℝ)) (Y := (5257692807733/6250000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124093361/125000000 : ℝ) ^ p + (231359893/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124093361/125000000 : ℝ)) (y := (231359893/250000000 : ℝ)) (X := (5257692807733/6250000000000 : ℝ)) (Y := (7938465723571/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (95909323/50000000 : ℝ)) (τ := (231359893/250000000 : ℝ)) (σ := (124093361/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789523761/835921433 : ℝ) ^ p + (825501632/835921433 : ℝ) ^ p := by
    exact cert_lt (x := (789523761/835921433 : ℝ)) (y := (825501632/835921433 : ℝ)) (X := (3220356382589/12500000000000 : ℝ)) (Y := (37118575243039/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231359893/250000000 : ℝ)) (n' := (835921433/1000000000 : ℝ)) (Ab := (789523761/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925439591/1000000000 : ℝ) ^ p + (248186721/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925439591/1000000000 : ℝ)) (y := (248186721/250000000 : ℝ)) (X := (15876939188833/100000000000000 : ℝ)) (Y := (84123076873647/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248186721/250000000 : ℝ) ^ p + (925439591/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248186721/250000000 : ℝ)) (y := (925439591/1000000000 : ℝ)) (X := (84123076873647/100000000000000 : ℝ)) (Y := (15876939188833/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (76727459/40000000 : ℝ)) (τ := (925439591/1000000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789523781/835921455 : ℝ) ^ p + (275167218/278640485 : ℝ) ^ p := by
    exact cert_lt (x := (789523781/835921455 : ℝ)) (y := (275167218/278640485 : ℝ)) (X := (12881425228541/50000000000000 : ℝ)) (Y := (74237151071789/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925439591/1000000000 : ℝ)) (n' := (167184291/200000000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (115679949/125000000 : ℝ) ^ p + (248186721/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115679949/125000000 : ℝ)) (y := (248186721/250000000 : ℝ)) (X := (15876939596291/100000000000000 : ℝ)) (Y := (84123076873647/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248186721/250000000 : ℝ) ^ p + (115679949/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248186721/250000000 : ℝ)) (y := (115679949/125000000 : ℝ)) (X := (84123076873647/100000000000000 : ℝ)) (Y := (15876939596291/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (789523781/835921456 : ℝ) ^ p + (825501655/835921456 : ℝ) ^ p := by
    exact cert_lt (x := (789523781/835921456 : ℝ)) (y := (825501655/835921456 : ℝ)) (X := (12881424862557/50000000000000 : ℝ)) (Y := (18559287774603/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1656929089/1806521375 : ℝ) ^ p + (1796101574/1806521375 : ℝ) ^ p := by
    exact cert_lt (x := (1656929089/1806521375 : ℝ)) (y := (1796101574/1806521375 : ℝ)) (X := (1604554372411/12500000000000 : ℝ)) (Y := (87163565311391/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112380767/1193478625 : ℝ) ^ p + (1183058824/1193478625 : ℝ) ^ p := by
    exact cert_lt (x := (1112380767/1193478625 : ℝ)) (y := (1183058824/1193478625 : ℝ)) (X := (18800617722157/100000000000000 : ℝ)) (Y := (81199383009411/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248186721/250000000 : ℝ)) (U := (9547829/8000000 : ℝ)) (Ab := (1656929089/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ)) (Ab := (1112380767/1000000000 : ℝ))
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

theorem localize21_slab087 (p : ℝ) (hpa : (759/32 : ℝ) ≤ p) (hpb : p ≤ (95/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (9547829/8000000 : ℝ)) ∧ coordinateBox (2293/5000 : ℝ) (2781/2500 : ℝ) (1547/2000 : ℝ) (11849/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (66864774495511/41441400000000 : ℝ) ≤ X j i + X k i) ∧
    (120324199378379/20720700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (971199283/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(759/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (971199283/1000000000 : ℝ))
      (by norm_num) 32 759 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(759/32 : ℝ)) ≤ (242799821/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (242799821/250000000 : ℝ))
      (by norm_num) (by norm_num) 32 759 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(95/4 : ℝ)) ≤ (971236629/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971236629/1000000000 : ℝ))
      (by norm_num) (by norm_num) 4 95 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (2096873227469/103603500000000 : ℝ) (10419801/1000000000 : ℝ) (4000000621621/20720700000000 : ℝ) (3033/2500 : ℝ) (971236629/500000000 : ℝ) (971199283/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (759/32 : ℝ)) (β := (95/4 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (2096873227469/103603500000000 : ℝ)) (δ := (10419801/1000000000 : ℝ)) (h := (4000000621621/20720700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (971199283/1000000000 : ℝ)) (thia := (242799821/250000000 : ℝ)) (thib := (971236629/1000000000 : ℝ))
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
  have hh := contract21_slab087 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 88, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab088 (p : ℝ) (hpa : (95/4 : ℝ) ≤ p) (hpb : p ≤ (761/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (26206630837/1296750000000 : ℝ) (1040399/100000000 : ℝ) (100000015561/518700000000 : ℝ) (3033/2500 : ℝ) (485636939/250000000 : ℝ) (242809157/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193491347/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(89/80 : ℝ) ≤ X j i ∧ X j i ≤ -(1147/2500 : ℝ)
      else (7737/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (26206630837/1296750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1040399/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (459836219/500000000 : ℝ) ^ p + (993847421/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459836219/500000000 : ℝ)) (y := (993847421/1000000000 : ℝ)) (X := (106645216873/781250000000 : ℝ)) (Y := (43174714909057/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993847421/1000000000 : ℝ) ^ p + (459836219/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993847421/1000000000 : ℝ)) (y := (459836219/500000000 : ℝ)) (X := (43174714909057/50000000000000 : ℝ)) (Y := (106645216873/781250000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913519859/1000000000 : ℝ)) (τ := (459836219/500000000 : ℝ)) (σ := (993847421/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (261113939/276357568 : ℝ) ^ p + (409334357/414536352 : ℝ) ^ p := by
    exact cert_lt (x := (261113939/276357568 : ℝ)) (y := (409334357/414536352 : ℝ)) (X := (12970865312727/50000000000000 : ℝ)) (Y := (74058270337493/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459836219/500000000 : ℝ)) (n' := (12954261/15625000 : ℝ)) (Ab := (783341817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (925292123/1000000000 : ℝ) ^ p + (992805139/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925292123/1000000000 : ℝ)) (y := (992805139/1000000000 : ℝ)) (X := (3944657199351/25000000000000 : ℝ)) (Y := (2631918363783/3125000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992805139/1000000000 : ℝ) ^ p + (925292123/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992805139/1000000000 : ℝ)) (y := (925292123/1000000000 : ℝ)) (X := (2631918363783/3125000000000 : ℝ)) (Y := (3944657199351/25000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (959048631/500000000 : ℝ)) (τ := (925292123/1000000000 : ℝ)) (σ := (992805139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (10525231/11142915 : ℝ) ^ p + (165062927/167143725 : ℝ) ^ p := by
    exact cert_lt (x := (10525231/11142915 : ℝ)) (y := (165062927/167143725 : ℝ)) (X := (1030541432027/4000000000000 : ℝ)) (Y := (37118232581541/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (925292123/1000000000 : ℝ)) (n' := (6685749/8000000 : ℝ)) (Ab := (31575693/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925534957/1000000000 : ℝ) ^ p + (124094519/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (925534957/1000000000 : ℝ)) (y := (124094519/125000000 : ℝ)) (X := (7938700343451/50000000000000 : ℝ)) (Y := (42061308277643/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124094519/125000000 : ℝ) ^ p + (925534957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124094519/125000000 : ℝ)) (y := (925534957/1000000000 : ℝ)) (X := (42061308277643/50000000000000 : ℝ)) (Y := (7938700343451/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918291109/1000000000 : ℝ)) (τ := (925534957/1000000000 : ℝ)) (σ := (124094519/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (394826459/418002456 : ℝ) ^ p + (412800461/418002456 : ℝ) ^ p := by
    exact cert_lt (x := (394826459/418002456 : ℝ)) (y := (412800461/418002456 : ℝ)) (X := (6438978586593/25000000000000 : ℝ)) (Y := (37122043384561/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925534957/1000000000 : ℝ)) (n' := (52250307/62500000 : ℝ)) (Ab := (394826459/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (925545341/1000000000 : ℝ) ^ p + (992754049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925545341/1000000000 : ℝ)) (y := (992754049/1000000000 : ℝ)) (X := (7940818760403/50000000000000 : ℝ)) (Y := (84118378821631/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992754049/1000000000 : ℝ) ^ p + (925545341/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992754049/1000000000 : ℝ)) (y := (925545341/1000000000 : ℝ)) (X := (84118378821631/100000000000000 : ℝ)) (Y := (7940818760403/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (191829939/100000000 : ℝ)) (τ := (925545341/1000000000 : ℝ)) (σ := (992754049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (263221353/278672384 : ℝ) ^ p + (412806581/418008576 : ℝ) ^ p := by
    exact cert_lt (x := (263221353/278672384 : ℝ)) (y := (412806581/418008576 : ℝ)) (X := (643889707389/2500000000000 : ℝ)) (Y := (7424441252589/10000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (925545341/1000000000 : ℝ)) (n' := (1632846/1953125 : ℝ)) (Ab := (789664059/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (185109157/200000000 : ℝ) ^ p + (992753959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185109157/200000000 : ℝ)) (y := (992753959/1000000000 : ℝ)) (X := (15881818703871/100000000000000 : ℝ)) (Y := (2102954936703/2500000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992753959/1000000000 : ℝ) ^ p + (185109157/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992753959/1000000000 : ℝ)) (y := (185109157/200000000 : ℝ)) (X := (2102954936703/2500000000000 : ℝ)) (Y := (15881818703871/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (59946867/31250000 : ℝ)) (τ := (185109157/200000000 : ℝ)) (σ := (992753959/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (197416134/209004419 : ℝ) ^ p + (412806843/418008838 : ℝ) ^ p := by
    exact cert_lt (x := (197416134/209004419 : ℝ)) (y := (412806843/418008838 : ℝ)) (X := (12877787187623/50000000000000 : ℝ)) (Y := (4640276654469/6250000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (185109157/200000000 : ℝ)) (n' := (209004419/250000000 : ℝ)) (Ab := (98708067/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925545803/1000000000 : ℝ) ^ p + (248188489/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925545803/1000000000 : ℝ)) (y := (248188489/250000000 : ℝ)) (X := (3970456512293/25000000000000 : ℝ)) (Y := (8411819142301/10000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248188489/250000000 : ℝ) ^ p + (925545803/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248188489/250000000 : ℝ)) (y := (925545803/1000000000 : ℝ)) (X := (8411819142301/10000000000000 : ℝ)) (Y := (3970456512293/25000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789664556/836017697 : ℝ) ^ p + (825613707/836017697 : ℝ) ^ p := by
    exact cert_lt (x := (789664556/836017697 : ℝ)) (y := (825613707/836017697 : ℝ)) (X := (12877787251361/50000000000000 : ℝ)) (Y := (74244427030393/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1657092566/1806508653 : ℝ) ^ p + (1796104663/1806508653 : ℝ) ^ p := by
    exact cert_lt (x := (1657092566/1806508653 : ℝ)) (y := (1796104663/1806508653 : ℝ)) (X := (12834028608657/100000000000000 : ℝ)) (Y := (43582985796099/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1112486192/1193491347 : ℝ) ^ p + (1183087357/1193491347 : ℝ) ^ p := by
    exact cert_lt (x := (1112486192/1193491347 : ℝ)) (y := (1183087357/1193491347 : ℝ)) (X := (18796880376759/100000000000000 : ℝ)) (Y := (81203120069197/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248188489/250000000 : ℝ)) (U := (1193491347/1000000000 : ℝ)) (Ab := (828546283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ)) (Ab := (69530387/62500000 : ℝ))
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

theorem localize21_slab088 (p : ℝ) (hpa : (95/4 : ℝ) ≤ p) (hpb : p ≤ (761/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193491347/1000000000 : ℝ)) ∧ coordinateBox (1147/2500 : ℝ) (89/80 : ℝ) (7737/10000 : ℝ) (11849/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (8370360331241/5187000000000 : ℝ) ≤ X j i + X k i) ∧
    (3012199984439/518700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (242809157/250000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(95/4 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (242809157/250000000 : ℝ))
      (by norm_num) 4 95 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(95/4 : ℝ)) ≤ (971236629/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971236629/1000000000 : ℝ))
      (by norm_num) (by norm_num) 4 95 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(761/32 : ℝ)) ≤ (485636939/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (485636939/500000000 : ℝ))
      (by norm_num) (by norm_num) 32 761 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (26206630837/1296750000000 : ℝ) (1040399/100000000 : ℝ) (100000015561/518700000000 : ℝ) (3033/2500 : ℝ) (485636939/250000000 : ℝ) (242809157/250000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (95/4 : ℝ)) (β := (761/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (26206630837/1296750000000 : ℝ)) (δ := (1040399/100000000 : ℝ)) (h := (100000015561/518700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (242809157/250000000 : ℝ)) (thia := (971236629/1000000000 : ℝ)) (thib := (485636939/500000000 : ℝ))
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
  have hh := contract21_slab088 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 89, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab089 (p : ℝ) (hpa : (761/32 : ℝ) ≤ p) (hpb : p ≤ (381/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2096189044697/103876500000000 : ℝ) (2597057/250000000 : ℝ) (4000000623259/20775300000000 : ℝ) (3033/2500 : ℝ) (97131103/50000000 : ℝ) (971273877/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596752037/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5563/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4589/10000 : ℝ)
      else (7739/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2096189044697/103876500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2597057/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (459891659/500000000 : ℝ) ^ p + (198770759/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (459891659/500000000 : ℝ)) (y := (198770759/200000000 : ℝ)) (X := (853378439441/6250000000000 : ℝ)) (Y := (86345963649463/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198770759/200000000 : ℝ) ^ p + (459891659/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198770759/200000000 : ℝ)) (y := (459891659/500000000 : ℝ)) (X := (86345963649463/100000000000000 : ℝ)) (Y := (853378439441/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913637113/1000000000 : ℝ)) (τ := (459891659/500000000 : ℝ)) (σ := (198770759/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783487871/829175617 : ℝ) ^ p + (818787389/829175617 : ℝ) ^ p := by
    exact cert_lt (x := (783487871/829175617 : ℝ)) (y := (818787389/829175617 : ℝ)) (X := (25934226034901/100000000000000 : ℝ)) (Y := (74065774936419/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459891659/500000000 : ℝ)) (n' := (829175617/1000000000 : ℝ)) (Ab := (783487871/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (9253987/10000000 : ℝ) ^ p + (992812077/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (9253987/10000000 : ℝ)) (y := (992812077/1000000000 : ℝ)) (X := (15783618517049/100000000000000 : ℝ)) (Y := (10527049768729/12500000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992812077/1000000000 : ℝ) ^ p + (9253987/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (992812077/1000000000 : ℝ)) (y := (9253987/10000000 : ℝ)) (X := (10527049768729/12500000000000 : ℝ)) (Y := (15783618517049/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918210777/1000000000 : ℝ)) (τ := (9253987/10000000 : ℝ)) (σ := (992812077/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (789533446/835815385 : ℝ) ^ p + (825427157/835815385 : ℝ) ^ p := by
    exact cert_lt (x := (789533446/835815385 : ℝ)) (y := (825427157/835815385 : ℝ)) (X := (25756261529853/100000000000000 : ℝ)) (Y := (37121870007393/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (9253987/10000000 : ℝ)) (n' := (167163077/200000000 : ℝ)) (Ab := (394766723/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925640909/1000000000 : ℝ) ^ p + (992763203/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925640909/1000000000 : ℝ)) (y := (992763203/1000000000 : ℝ)) (X := (15882285089141/100000000000000 : ℝ)) (Y := (10514716486709/12500000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992763203/1000000000 : ℝ) ^ p + (925640909/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992763203/1000000000 : ℝ)) (y := (925640909/1000000000 : ℝ)) (X := (10514716486709/12500000000000 : ℝ)) (Y := (15882285089141/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (119900257/62500000 : ℝ)) (τ := (925640909/1000000000 : ℝ)) (σ := (992763203/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (157958671/167220178 : ℝ) ^ p + (412856331/418050445 : ℝ) ^ p := by
    exact cert_lt (x := (157958671/167220178 : ℝ)) (y := (412856331/418050445 : ℝ)) (X := (2574866281403/10000000000000 : ℝ)) (Y := (37125669047509/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925640909/1000000000 : ℝ)) (n' := (83610089/100000000 : ℝ)) (Ab := (157958671/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (925651247/1000000000 : ℝ) ^ p + (992761109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925651247/1000000000 : ℝ)) (y := (992761109/1000000000 : ℝ)) (X := (127092076089/800000000000 : ℝ)) (Y := (5257094189129/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992761109/1000000000 : ℝ) ^ p + (925651247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992761109/1000000000 : ℝ)) (y := (925651247/1000000000 : ℝ)) (X := (5257094189129/6250000000000 : ℝ)) (Y := (127092076089/800000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (479603089/250000000 : ℝ)) (τ := (925651247/1000000000 : ℝ)) (σ := (992761109/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (789804448/836113075 : ℝ) ^ p + (825724847/836113075 : ℝ) ^ p := by
    exact cert_lt (x := (789804448/836113075 : ℝ)) (y := (825724847/836113075 : ℝ)) (X := (25748338988351/100000000000000 : ℝ)) (Y := (7425166227279/10000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (925651247/1000000000 : ℝ)) (n' := (33444523/40000000 : ℝ)) (Ab := (24681389/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (115706461/125000000 : ℝ) ^ p + (49638051/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (115706461/125000000 : ℝ)) (y := (49638051/50000000 : ℝ)) (X := (15886689741107/100000000000000 : ℝ)) (Y := (42056663731803/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (49638051/50000000 : ℝ) ^ p + (115706461/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (49638051/50000000 : ℝ)) (y := (115706461/125000000 : ℝ)) (X := (42056663731803/50000000000000 : ℝ)) (Y := (15886689741107/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479603177/250000000 : ℝ)) (τ := (115706461/125000000 : ℝ)) (σ := (49638051/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789804921/836113595 : ℝ) ^ p + (825725367/836113595 : ℝ) ^ p := by
    exact cert_lt (x := (789804921/836113595 : ℝ)) (y := (825725367/836113595 : ℝ)) (X := (12874162429969/50000000000000 : ℝ)) (Y := (9281459513379/12500000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (115706461/125000000 : ℝ)) (n' := (167222719/200000000 : ℝ)) (Ab := (789804921/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925651707/1000000000 : ℝ) ^ p + (124095127/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (925651707/1000000000 : ℝ)) (y := (124095127/125000000 : ℝ)) (X := (15886697506161/100000000000000 : ℝ)) (Y := (5257082462087/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124095127/125000000 : ℝ) ^ p + (925651707/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124095127/125000000 : ℝ)) (y := (925651707/1000000000 : ℝ)) (X := (5257082462087/6250000000000 : ℝ)) (Y := (15886697506161/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918412723/1000000000 : ℝ)) (τ := (925651707/1000000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789804941/836113617 : ℝ) ^ p + (825725389/836113617 : ℝ) ^ p := by
    exact cert_lt (x := (789804941/836113617 : ℝ)) (y := (825725389/836113617 : ℝ)) (X := (25748324253241/100000000000000 : ℝ)) (Y := (74251676692327/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925651707/1000000000 : ℝ)) (n' := (836113617/1000000000 : ℝ)) (Ab := (789804941/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (231412927/250000000 : ℝ) ^ p + (124095127/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (231412927/250000000 : ℝ)) (y := (124095127/125000000 : ℝ)) (X := (15886697914849/100000000000000 : ℝ)) (Y := (5257082462087/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124095127/125000000 : ℝ) ^ p + (231412927/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124095127/125000000 : ℝ)) (y := (231412927/250000000 : ℝ)) (X := (5257082462087/6250000000000 : ℝ)) (Y := (15886697914849/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (394902471/418056809 : ℝ) ^ p + (412862695/418056809 : ℝ) ^ p := by
    exact cert_lt (x := (394902471/418056809 : ℝ)) (y := (412862695/418056809 : ℝ)) (X := (25748324296237/100000000000000 : ℝ)) (Y := (74251676718931/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657255641/1806495926 : ℝ) ^ p + (898053849/903247963 : ℝ) ^ p := by
    exact cert_lt (x := (1657255641/1806495926 : ℝ)) (y := (898053849/903247963 : ℝ)) (X := (12831631227299/100000000000000 : ℝ)) (Y := (43584184555863/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (556295708/596752037 : ℝ) ^ p + (591557923/596752037 : ℝ) ^ p := by
    exact cert_lt (x := (556295708/596752037 : ℝ)) (y := (591557923/596752037 : ℝ)) (X := (4698288969443/25000000000000 : ℝ)) (Y := (81206844685171/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124095127/125000000 : ℝ)) (U := (596752037/500000000 : ℝ)) (Ab := (1657255641/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ)) (Ab := (139073927/125000000 : ℝ))
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

theorem localize21_slab089 (p : ℝ) (hpa : (761/32 : ℝ) ≤ p) (hpb : p ≤ (381/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (596752037/500000000 : ℝ)) ∧ coordinateBox (4589/10000 : ℝ) (5563/5000 : ℝ) (7739/10000 : ℝ) (11849/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (83826236509187/51938250000000 : ℝ) ≤ X j i + X k i) ∧
    (120651799376741/20775300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (971273877/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(761/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (971273877/1000000000 : ℝ))
      (by norm_num) 32 761 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(761/32 : ℝ)) ≤ (485636939/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (485636939/500000000 : ℝ))
      (by norm_num) (by norm_num) 32 761 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(381/16 : ℝ)) ≤ (97131103/100000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (97131103/100000000 : ℝ))
      (by norm_num) (by norm_num) 16 381 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (2096189044697/103876500000000 : ℝ) (2597057/250000000 : ℝ) (4000000623259/20775300000000 : ℝ) (3033/2500 : ℝ) (97131103/50000000 : ℝ) (971273877/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (761/32 : ℝ)) (β := (381/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (2096189044697/103876500000000 : ℝ)) (δ := (2597057/250000000 : ℝ)) (h := (4000000623259/20775300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (971273877/1000000000 : ℝ)) (thia := (485636939/500000000 : ℝ)) (thib := (97131103/100000000 : ℝ))
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
  have hh := contract21_slab089 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 90, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab090 (p : ℝ) (hpa : (381/16 : ℝ) ≤ p) (hpb : p ≤ (763/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (209584810073/10401300000000 : ℝ) (10372511/1000000000 : ℝ) (2000000312039/10401300000000 : ℝ) (3033/2500 : ℝ) (971348087/500000000 : ℝ) (971311029/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193516797/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11127/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4591/10000 : ℝ)
      else (7741/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (209584810073/10401300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10372511/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (459946949/500000000 : ℝ) ^ p + (198772031/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (459946949/500000000 : ℝ)) (y := (198772031/200000000 : ℝ)) (X := (13657515156547/100000000000000 : ℝ)) (Y := (43171251572263/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198772031/200000000 : ℝ) ^ p + (459946949/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198772031/200000000 : ℝ)) (y := (459946949/500000000 : ℝ)) (X := (43171251572263/50000000000000 : ℝ)) (Y := (13657515156547/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913754053/1000000000 : ℝ)) (τ := (459946949/500000000 : ℝ)) (σ := (198772031/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783633539/829278219 : ℝ) ^ p + (818905708/829278219 : ℝ) ^ p := by
    exact cert_lt (x := (783633539/829278219 : ℝ)) (y := (818905708/829278219 : ℝ)) (X := (25926739954453/100000000000000 : ℝ)) (Y := (7407326138023/10000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459946949/500000000 : ℝ)) (n' := (829278219/1000000000 : ℝ)) (Ab := (783633539/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (57844061/62500000 : ℝ) ^ p + (992819003/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57844061/62500000 : ℝ)) (y := (992819003/1000000000 : ℝ)) (X := (1973574504981/12500000000000 : ℝ)) (Y := (84211421367551/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992819003/1000000000 : ℝ) ^ p + (57844061/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992819003/1000000000 : ℝ)) (y := (57844061/62500000 : ℝ)) (X := (84211421367551/100000000000000 : ℝ)) (Y := (1973574504981/12500000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918323979/1000000000 : ℝ)) (τ := (57844061/62500000 : ℝ)) (σ := (992819003/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394837090/417955919 : ℝ) ^ p + (825539327/835911838 : ℝ) ^ p := by
    exact cert_lt (x := (394837090/417955919 : ℝ)) (y := (825539327/835911838 : ℝ)) (X := (25749003883369/100000000000000 : ℝ)) (Y := (74250997121721/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (57844061/62500000 : ℝ)) (n' := (417955919/500000000 : ℝ)) (Ab := (39483709/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925746563/1000000000 : ℝ) ^ p + (992770241/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925746563/1000000000 : ℝ)) (y := (992770241/1000000000 : ℝ)) (X := (3971789438467/25000000000000 : ℝ)) (Y := (42056429245059/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992770241/1000000000 : ℝ) ^ p + (925746563/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992770241/1000000000 : ℝ)) (y := (925746563/1000000000 : ℝ)) (X := (42056429245059/50000000000000 : ℝ)) (Y := (3971789438467/25000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (479629201/250000000 : ℝ)) (τ := (925746563/1000000000 : ℝ)) (σ := (992770241/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (157986682/167239313 : ℝ) ^ p + (825824054/836196565 : ℝ) ^ p := by
    exact cert_lt (x := (157986682/167239313 : ℝ)) (y := (825824054/836196565 : ℝ)) (X := (643535725129/2500000000000 : ℝ)) (Y := (74258571805067/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925746563/1000000000 : ℝ)) (n' := (167239313/200000000 : ℝ)) (Ab := (78993341/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (115719607/125000000 : ℝ) ^ p + (248192039/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115719607/125000000 : ℝ)) (y := (248192039/250000000 : ℝ)) (X := (7945685058419/50000000000000 : ℝ)) (Y := (1682172930679/2000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248192039/250000000 : ℝ) ^ p + (115719607/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248192039/250000000 : ℝ)) (y := (115719607/125000000 : ℝ)) (X := (1682172930679/2000000000000 : ℝ)) (Y := (7945685058419/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (479631253/250000000 : ℝ)) (τ := (115719607/125000000 : ℝ)) (σ := (248192039/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (789944453/836208694 : ℝ) ^ p + (825836183/836208694 : ℝ) ^ p := by
    exact cert_lt (x := (789944453/836208694 : ℝ)) (y := (825836183/836208694 : ℝ)) (X := (1608819162199/6250000000000 : ℝ)) (Y := (37129447189307/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (115719607/125000000 : ℝ)) (n' := (418104347/500000000 : ℝ)) (Ab := (789944453/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (462878647/500000000 : ℝ) ^ p + (992768067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462878647/500000000 : ℝ)) (y := (992768067/1000000000 : ℝ)) (X := (794577469503/5000000000000 : ℝ)) (Y := (10513558343439/12500000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992768067/1000000000 : ℝ) ^ p + (462878647/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992768067/1000000000 : ℝ)) (y := (462878647/500000000 : ℝ)) (X := (10513558343439/12500000000000 : ℝ)) (Y := (794577469503/5000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1918525361/1000000000 : ℝ)) (τ := (462878647/500000000 : ℝ)) (σ := (992768067/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789944923/836209210 : ℝ) ^ p + (825836699/836209210 : ℝ) ^ p := by
    exact cert_lt (x := (789944923/836209210 : ℝ)) (y := (825836699/836209210 : ℝ)) (X := (25741093035729/100000000000000 : ℝ)) (Y := (2970356324063/4000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (462878647/500000000 : ℝ)) (n' := (83620921/100000000 : ℝ)) (Ab := (789944923/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (7232479/7812500 : ℝ) ^ p + (15512001/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (7232479/7812500 : ℝ)) (y := (15512001/15625000 : ℝ)) (X := (7945778378747/50000000000000 : ℝ)) (Y := (42054230343651/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (15512001/15625000 : ℝ) ^ p + (7232479/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (15512001/15625000 : ℝ)) (y := (7232479/7812500 : ℝ)) (X := (42054230343651/50000000000000 : ℝ)) (Y := (7945778378747/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (29976959/15625000 : ℝ)) (τ := (7232479/7812500 : ℝ)) (σ := (15512001/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789944942/836209231 : ℝ) ^ p + (825836720/836209231 : ℝ) ^ p := by
    exact cert_lt (x := (789944942/836209231 : ℝ)) (y := (825836720/836209231 : ℝ)) (X := (25741092384511/100000000000000 : ℝ)) (Y := (74258908660067/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (7232479/7812500 : ℝ)) (n' := (836209231/1000000000 : ℝ)) (Ab := (394972471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (462878657/500000000 : ℝ) ^ p + (992768063/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462878657/500000000 : ℝ)) (y := (992768063/1000000000 : ℝ)) (X := (7945778788049/50000000000000 : ℝ)) (Y := (2628389333351/3125000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992768063/1000000000 : ℝ) ^ p + (462878657/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992768063/1000000000 : ℝ)) (y := (462878657/500000000 : ℝ)) (X := (2628389333351/3125000000000 : ℝ)) (Y := (7945778788049/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (789944945/836209234 : ℝ) ^ p + (825836723/836209234 : ℝ) ^ p := by
    exact cert_lt (x := (789944945/836209234 : ℝ)) (y := (825836723/836209234 : ℝ)) (X := (25741092513471/100000000000000 : ℝ)) (Y := (74258908739851/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657418297/1806483203 : ℝ) ^ p + (1796110692/1806483203 : ℝ) ^ p := by
    exact cert_lt (x := (1657418297/1806483203 : ℝ)) (y := (1796110692/1806483203 : ℝ)) (X := (12829237891227/100000000000000 : ℝ)) (Y := (43585381167817/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112696415/1193516797 : ℝ) ^ p + (1183144286/1193516797 : ℝ) ^ p := by
    exact cert_lt (x := (1112696415/1193516797 : ℝ)) (y := (1183144286/1193516797 : ℝ)) (X := (3757887523099/20000000000000 : ℝ)) (Y := (40605281480501/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992768063/1000000000 : ℝ)) (U := (1193516797/1000000000 : ℝ)) (Ab := (1657418297/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ)) (Ab := (222539283/200000000 : ℝ))
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

theorem localize21_slab090 (p : ℝ) (hpa : (381/16 : ℝ) ≤ p) (hpb : p ≤ (763/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193516797/1000000000 : ℝ)) ∧ coordinateBox (4591/10000 : ℝ) (11127/10000 : ℝ) (7741/10000 : ℝ) (11849/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (167897736353509/104013000000000 : ℝ) ≤ X j i + X k i) ∧
    (60407799687961/10401300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (971311029/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(381/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (971311029/1000000000 : ℝ))
      (by norm_num) 16 381 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(381/16 : ℝ)) ≤ (97131103/100000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (97131103/100000000 : ℝ))
      (by norm_num) (by norm_num) 16 381 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(763/32 : ℝ)) ≤ (971348087/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971348087/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 763 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (209584810073/10401300000000 : ℝ) (10372511/1000000000 : ℝ) (2000000312039/10401300000000 : ℝ) (3033/2500 : ℝ) (971348087/500000000 : ℝ) (971311029/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (381/16 : ℝ)) (β := (763/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (209584810073/10401300000000 : ℝ)) (δ := (10372511/1000000000 : ℝ)) (h := (2000000312039/10401300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (971311029/1000000000 : ℝ)) (thia := (97131103/100000000 : ℝ)) (thib := (971348087/1000000000 : ℝ))
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
  have hh := contract21_slab090 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 91, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab091 (p : ℝ) (hpa : (763/32 : ℝ) ≤ p) (hpb : p ≤ (191/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (523877161631/26037375000000 : ℝ) (10356843/1000000000 : ℝ) (4000000624897/20829900000000 : ℝ) (3033/2500 : ℝ) (971385047/500000000 : ℝ) (485674043/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149191191/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11129/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4593/10000 : ℝ)
      else (7743/10000 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (523877161631/26037375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10356843/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (115000521/125000000 : ℝ) ^ p + (124233313/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (115000521/125000000 : ℝ)) (y := (124233313/125000000 : ℝ)) (X := (2732192837679/20000000000000 : ℝ)) (Y := (86339054411039/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124233313/125000000 : ℝ) ^ p + (115000521/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (124233313/125000000 : ℝ)) (y := (115000521/125000000 : ℝ)) (X := (86339054411039/100000000000000 : ℝ)) (Y := (2732192837679/20000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (119616917/62500000 : ℝ)) (τ := (115000521/125000000 : ℝ)) (σ := (124233313/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783778813/829380490 : ℝ) ^ p + (819023647/829380490 : ℝ) ^ p := by
    exact cert_lt (x := (783778813/829380490 : ℝ)) (y := (819023647/829380490 : ℝ)) (X := (25919280732383/100000000000000 : ℝ)) (Y := (1852018003087/2500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115000521/125000000 : ℝ)) (n' := (82938049/100000000 : ℝ)) (Ab := (783778813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (925610943/1000000000 : ℝ) ^ p + (496412959/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925610943/1000000000 : ℝ)) (y := (496412959/500000000 : ℝ)) (X := (1974194704559/12500000000000 : ℝ)) (Y := (84206459221659/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496412959/500000000 : ℝ) ^ p + (925610943/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496412959/500000000 : ℝ)) (y := (925610943/1000000000 : ℝ)) (X := (84206459221659/100000000000000 : ℝ)) (Y := (1974194704559/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918436861/1000000000 : ℝ)) (τ := (925610943/1000000000 : ℝ)) (σ := (496412959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (789814525/836007966 : ℝ) ^ p + (275217041/278669322 : ℝ) ^ p := by
    exact cert_lt (x := (789814525/836007966 : ℝ)) (y := (275217041/278669322 : ℝ)) (X := (12870887135731/50000000000000 : ℝ)) (Y := (37129113524541/50000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (925610943/1000000000 : ℝ)) (n' := (418003983/500000000 : ℝ)) (Ab := (31592581/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925851907/1000000000 : ℝ) ^ p + (99277727/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (925851907/1000000000 : ℝ)) (y := (99277727/100000000 : ℝ)) (X := (1986501661937/12500000000000 : ℝ)) (Y := (2102700108259/2500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99277727/100000000 : ℝ) ^ p + (925851907/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99277727/100000000 : ℝ)) (y := (925851907/1000000000 : ℝ)) (X := (2102700108259/2500000000000 : ℝ)) (Y := (1986501661937/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918629177/1000000000 : ℝ)) (τ := (925851907/1000000000 : ℝ)) (σ := (99277727/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (395036537/418145957 : ℝ) ^ p + (825935071/836291914 : ℝ) ^ p := by
    exact cert_lt (x := (395036537/418145957 : ℝ)) (y := (825935071/836291914 : ℝ)) (X := (25734222554323/100000000000000 : ℝ)) (Y := (74265778333799/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925851907/1000000000 : ℝ)) (n' := (418145957/500000000 : ℝ)) (Ab := (395036537/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (231465539/250000000 : ℝ) ^ p + (992775193/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231465539/250000000 : ℝ)) (y := (992775193/1000000000 : ℝ)) (X := (1987026744103/12500000000000 : ℝ)) (Y := (1682076066161/2000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992775193/1000000000 : ℝ) ^ p + (231465539/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992775193/1000000000 : ℝ)) (y := (231465539/250000000 : ℝ)) (X := (1682076066161/2000000000000 : ℝ)) (Y := (1987026744103/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1918637349/1000000000 : ℝ)) (τ := (231465539/250000000 : ℝ)) (σ := (992775193/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (79008407/83630399 : ℝ) ^ p + (825947147/836303990 : ℝ) ^ p := by
    exact cert_lt (x := (79008407/83630399 : ℝ)) (y := (825947147/836303990 : ℝ)) (X := (12866950848967/50000000000000 : ℝ)) (Y := (74266099384363/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (231465539/250000000 : ℝ)) (n' := (83630399/100000000 : ℝ)) (Ab := (79008407/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925862591/1000000000 : ℝ) ^ p + (198555021/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (925862591/1000000000 : ℝ)) (y := (198555021/200000000 : ℝ)) (X := (15896392265549/100000000000000 : ℝ)) (Y := (8410362532021/10000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198555021/200000000 : ℝ) ^ p + (925862591/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198555021/200000000 : ℝ)) (y := (925862591/1000000000 : ℝ)) (X := (8410362532021/10000000000000 : ℝ)) (Y := (15896392265549/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (14989357/7812500 : ℝ)) (τ := (925862591/1000000000 : ℝ)) (σ := (198555021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (395042268/418152251 : ℝ) ^ p + (825947659/836304502 : ℝ) ^ p := by
    exact cert_lt (x := (395042268/418152251 : ℝ)) (y := (825947659/836304502 : ℝ)) (X := (12866943965601/50000000000000 : ℝ)) (Y := (9283264124517/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925862591/1000000000 : ℝ)) (n' := (418152251/500000000 : ℝ)) (Ab := (98760567/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (92586261/100000000 : ℝ) ^ p + (992775101/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92586261/100000000 : ℝ)) (y := (992775101/1000000000 : ℝ)) (X := (3974100013491/25000000000000 : ℝ)) (Y := (84103617229863/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992775101/1000000000 : ℝ) ^ p + (92586261/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992775101/1000000000 : ℝ)) (y := (92586261/100000000 : ℝ)) (X := (84103617229863/100000000000000 : ℝ)) (Y := (3974100013491/25000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918637711/1000000000 : ℝ)) (τ := (92586261/100000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (87787173/92922725 : ℝ) ^ p + (39330842/39824025 : ℝ) ^ p := by
    exact cert_lt (x := (87787173/92922725 : ℝ)) (y := (39330842/39824025 : ℝ)) (X := (5146777472883/20000000000000 : ℝ)) (Y := (37133056803801/50000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (92586261/100000000 : ℝ)) (n' := (33452181/40000000 : ℝ)) (Ab := (790084557/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (925862611/1000000000 : ℝ) ^ p + (992775101/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925862611/1000000000 : ℝ)) (y := (992775101/1000000000 : ℝ)) (X := (15896400463881/100000000000000 : ℝ)) (Y := (84103617229863/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992775101/1000000000 : ℝ) ^ p + (925862611/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992775101/1000000000 : ℝ)) (y := (925862611/1000000000 : ℝ)) (X := (84103617229863/100000000000000 : ℝ)) (Y := (15896400463881/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (395042279/418152263 : ℝ) ^ p + (825947683/836304526 : ℝ) ^ p := by
    exact cert_lt (x := (395042279/418152263 : ℝ)) (y := (825947683/836304526 : ℝ)) (X := (25733887407393/100000000000000 : ℝ)) (Y := (74266113634187/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (552526851/602156824 : ℝ) ^ p + (598704543/602156824 : ℝ) ^ p := by
    exact cert_lt (x := (552526851/602156824 : ℝ)) (y := (598704543/602156824 : ℝ)) (X := (6413426924019/50000000000000 : ℝ)) (Y := (5448321646543/6250000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (556400609/596764764 : ℝ) ^ p + (394390895/397843176 : ℝ) ^ p := by
    exact cert_lt (x := (556400609/596764764 : ℝ)) (y := (394390895/397843176 : ℝ)) (X := (18785732426027/100000000000000 : ℝ)) (Y := (40607134111751/50000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992775101/1000000000 : ℝ)) (U := (149191191/125000000 : ℝ)) (Ab := (1657580553/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ)) (Ab := (556400609/500000000 : ℝ))
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

theorem localize21_slab091 (p : ℝ) (hpa : (763/32 : ℝ) ≤ p) (hpb : p ≤ (191/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (149191191/125000000 : ℝ)) ∧ coordinateBox (4593/10000 : ℝ) (11129/10000 : ℝ) (7743/10000 : ℝ) (237/200 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (168142995382069/104149500000000 : ℝ) ≤ X j i + X k i) ∧
    (120979399375103/20829900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (485674043/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(763/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (485674043/500000000 : ℝ))
      (by norm_num) 32 763 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(763/32 : ℝ)) ≤ (971348087/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971348087/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 763 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(191/8 : ℝ)) ≤ (971385047/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971385047/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 191 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (523877161631/26037375000000 : ℝ) (10356843/1000000000 : ℝ) (4000000624897/20829900000000 : ℝ) (3033/2500 : ℝ) (971385047/500000000 : ℝ) (485674043/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (763/32 : ℝ)) (β := (191/8 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (523877161631/26037375000000 : ℝ)) (δ := (10356843/1000000000 : ℝ)) (h := (4000000624897/20829900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (485674043/500000000 : ℝ)) (thia := (971348087/1000000000 : ℝ)) (thib := (971385047/1000000000 : ℝ))
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
  have hh := contract21_slab091 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 92, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab092 (p : ℝ) (hpa : (191/8 : ℝ) ≤ p) (hpb : p ≤ (765/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (130948074827/6517875000000 : ℝ) (5170609/500000000 : ℝ) (1000000156429/5214300000000 : ℝ) (3033/2500 : ℝ) (971421913/500000000 : ℝ) (485692523/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193542247/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1113/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(919/2000 : ℝ)
      else (484/625 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (130948074827/6517875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5170609/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (920114147/1000000000 : ℝ) ^ p + (496936419/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (920114147/1000000000 : ℝ)) (y := (496936419/500000000 : ℝ)) (X := (13664408453799/100000000000000 : ℝ)) (Y := (17267121810277/20000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496936419/500000000 : ℝ) ^ p + (920114147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496936419/500000000 : ℝ)) (y := (920114147/1000000000 : ℝ)) (X := (17267121810277/20000000000000 : ℝ)) (Y := (13664408453799/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (382797397/200000000 : ℝ)) (τ := (920114147/1000000000 : ℝ)) (σ := (496936419/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783923710/829482463 : ℝ) ^ p + (819141245/829482463 : ℝ) ^ p := by
    exact cert_lt (x := (783923710/829482463 : ℝ)) (y := (819141245/829482463 : ℝ)) (X := (25911836924683/100000000000000 : ℝ)) (Y := (74088164628779/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (920114147/1000000000 : ℝ)) (n' := (829482463/1000000000 : ℝ)) (Ab := (78392371/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (925716617/1000000000 : ℝ) ^ p + (49641641/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (925716617/1000000000 : ℝ)) (y := (49641641/50000000 : ℝ)) (X := (15798509349227/100000000000000 : ℝ)) (Y := (84201507567279/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (49641641/50000000 : ℝ) ^ p + (925716617/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49641641/50000000 : ℝ)) (y := (925716617/1000000000 : ℝ)) (X := (84201507567279/100000000000000 : ℝ)) (Y := (15798509349227/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918549437/1000000000 : ℝ)) (τ := (925716617/1000000000 : ℝ)) (σ := (49641641/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (789954489/836103797 : ℝ) ^ p + (825762579/836103797 : ℝ) ^ p := by
    exact cert_lt (x := (789954489/836103797 : ℝ)) (y := (825762579/836103797 : ℝ)) (X := (5146911617699/20000000000000 : ℝ)) (Y := (18566360760637/25000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (925716617/1000000000 : ℝ)) (n' := (836103797/1000000000 : ℝ)) (Ab := (789954489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925956963/1000000000 : ℝ) ^ p + (248196071/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925956963/1000000000 : ℝ)) (y := (248196071/250000000 : ℝ)) (X := (15896860252867/100000000000000 : ℝ)) (Y := (42051578594193/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248196071/250000000 : ℝ) ^ p + (925956963/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248196071/250000000 : ℝ)) (y := (925956963/1000000000 : ℝ)) (X := (42051578594193/50000000000000 : ℝ)) (Y := (15896860252867/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918741247/1000000000 : ℝ)) (τ := (925956963/1000000000 : ℝ)) (σ := (248196071/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (790212364/836386973 : ℝ) ^ p + (826045755/836386973 : ℝ) ^ p := by
    exact cert_lt (x := (790212364/836386973 : ℝ)) (y := (826045755/836386973 : ℝ)) (X := (2572702998523/10000000000000 : ℝ)) (Y := (14854594227199/20000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925956963/1000000000 : ℝ)) (n' := (836386973/1000000000 : ℝ)) (Ab := (197553091/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462983583/500000000 : ℝ) ^ p + (124097777/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (462983583/500000000 : ℝ)) (y := (124097777/125000000 : ℝ)) (X := (15901048330343/100000000000000 : ℝ)) (Y := (84098969165599/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124097777/125000000 : ℝ) ^ p + (462983583/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124097777/125000000 : ℝ)) (y := (462983583/500000000 : ℝ)) (X := (84098969165599/100000000000000 : ℝ)) (Y := (15901048330343/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (959374691/500000000 : ℝ)) (τ := (462983583/500000000 : ℝ)) (σ := (124097777/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (790223310/836398993 : ℝ) ^ p + (826057775/836398993 : ℝ) ^ p := by
    exact cert_lt (x := (790223310/836398993 : ℝ)) (y := (826057775/836398993 : ℝ)) (X := (6431677640697/25000000000000 : ℝ)) (Y := (37136645292561/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (462983583/500000000 : ℝ)) (n' := (836398993/1000000000 : ℝ)) (Ab := (79022331/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925967599/1000000000 : ℝ) ^ p + (62048883/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (925967599/1000000000 : ℝ)) (y := (62048883/62500000 : ℝ)) (X := (7950613044723/50000000000000 : ℝ)) (Y := (10512348869537/12500000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62048883/62500000 : ℝ) ^ p + (925967599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62048883/62500000 : ℝ)) (y := (925967599/1000000000 : ℝ)) (X := (10512348869537/12500000000000 : ℝ)) (Y := (7950613044723/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1918749727/1000000000 : ℝ)) (τ := (925967599/1000000000 : ℝ)) (σ := (62048883/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (790223774/836399503 : ℝ) ^ p + (826058285/836399503 : ℝ) ^ p := by
    exact cert_lt (x := (790223774/836399503 : ℝ)) (y := (826058285/836399503 : ℝ)) (X := (25726696674803/100000000000000 : ℝ)) (Y := (37136652069473/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925967599/1000000000 : ℝ)) (n' := (836399503/1000000000 : ℝ)) (Ab := (395111887/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (462983809/500000000 : ℝ) ^ p + (248195531/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (462983809/500000000 : ℝ)) (y := (248195531/250000000 : ℝ)) (X := (15901233889543/100000000000000 : ℝ)) (Y := (42049391427941/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248195531/250000000 : ℝ) ^ p + (462983809/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248195531/250000000 : ℝ)) (y := (462983809/500000000 : ℝ)) (X := (42049391427941/50000000000000 : ℝ)) (Y := (15901233889543/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (959374871/500000000 : ℝ)) (τ := (462983809/500000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (790223794/836399525 : ℝ) ^ p + (826058307/836399525 : ℝ) ^ p := by
    exact cert_lt (x := (790223794/836399525 : ℝ)) (y := (826058307/836399525 : ℝ)) (X := (12863348031753/50000000000000 : ℝ)) (Y := (3713665236181/5000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (462983809/500000000 : ℝ)) (n' := (33455981/40000000 : ℝ)) (Ab := (395111897/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (925967619/1000000000 : ℝ) ^ p + (248195531/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925967619/1000000000 : ℝ)) (y := (248195531/250000000 : ℝ)) (X := (7950617150037/50000000000000 : ℝ)) (Y := (42049391427941/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248195531/250000000 : ℝ) ^ p + (925967619/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248195531/250000000 : ℝ)) (y := (925967619/1000000000 : ℝ)) (X := (42049391427941/50000000000000 : ℝ)) (Y := (7950617150037/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (790223795/836399526 : ℝ) ^ p + (413029154/418199763 : ℝ) ^ p := by
    exact cert_lt (x := (790223795/836399526 : ℝ)) (y := (413029154/418199763 : ℝ)) (X := (12863348053237/50000000000000 : ℝ)) (Y := (18568326187549/25000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657742392/1806457753 : ℝ) ^ p + (1796116535/1806457753 : ℝ) ^ p := by
    exact cert_lt (x := (1657742392/1806457753 : ℝ)) (y := (1796116535/1806457753 : ℝ)) (X := (6412236140197/50000000000000 : ℝ)) (Y := (8717552801053/10000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112905784/1193542247 : ℝ) ^ p + (1183201029/1193542247 : ℝ) ^ p := by
    exact cert_lt (x := (1112905784/1193542247 : ℝ)) (y := (1183201029/1193542247 : ℝ)) (X := (18782030969977/100000000000000 : ℝ)) (Y := (2030449242983/2500000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248195531/250000000 : ℝ)) (U := (1193542247/1000000000 : ℝ)) (Ab := (207217799/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ)) (Ab := (139113223/125000000 : ℝ))
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

theorem localize21_slab092 (p : ℝ) (hpa : (191/8 : ℝ) ≤ p) (hpb : p ≤ (765/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193542247/1000000000 : ℝ)) ∧ coordinateBox (919/2000 : ℝ) (1113/1000 : ℝ) (484/625 : ℝ) (237/200 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (84194126093249/52143000000000 : ℝ) ≤ X j i + X k i) ∧
    (30285799843571/5214300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (485692523/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(191/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (485692523/500000000 : ℝ))
      (by norm_num) 8 191 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(191/8 : ℝ)) ≤ (971385047/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971385047/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 191 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(765/32 : ℝ)) ≤ (971421913/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971421913/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 765 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (130948074827/6517875000000 : ℝ) (5170609/500000000 : ℝ) (1000000156429/5214300000000 : ℝ) (3033/2500 : ℝ) (971421913/500000000 : ℝ) (485692523/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (191/8 : ℝ)) (β := (765/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (130948074827/6517875000000 : ℝ)) (δ := (5170609/500000000 : ℝ)) (h := (1000000156429/5214300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (485692523/500000000 : ℝ)) (thia := (971385047/1000000000 : ℝ)) (thib := (971421913/1000000000 : ℝ))
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
  have hh := contract21_slab092 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 93, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab093 (p : ℝ) (hpa : (765/32 : ℝ) ≤ p) (hpb : p ≤ (383/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (209483139413/10442250000000 : ℝ) (10325643/1000000000 : ℝ) (800000125307/4176900000000 : ℝ) (3033/2500 : ℝ) (971458683/500000000 : ℝ) (121427739/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193554979/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11131/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1149/2500 : ℝ)
      else (3873/5000 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (209483139413/10442250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10325643/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (460111907/500000000 : ℝ) ^ p + (496939581/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460111907/500000000 : ℝ)) (y := (496939581/500000000 : ℝ)) (X := (6833920048499/50000000000000 : ℝ)) (Y := (17266435467961/20000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496939581/500000000 : ℝ) ^ p + (460111907/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496939581/500000000 : ℝ)) (y := (460111907/500000000 : ℝ)) (X := (17266435467961/20000000000000 : ℝ)) (Y := (6833920048499/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (29907859/15625000 : ℝ)) (τ := (460111907/500000000 : ℝ)) (σ := (496939581/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784068213/829584101 : ℝ) ^ p + (819258458/829584101 : ℝ) ^ p := by
    exact cert_lt (x := (784068213/829584101 : ℝ)) (y := (819258458/829584101 : ℝ)) (X := (12952211238899/50000000000000 : ℝ)) (Y := (4630973649517/6250000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (460111907/500000000 : ℝ)) (n' := (829584101/1000000000 : ℝ)) (Ab := (784068213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46291099/50000000 : ℝ) ^ p + (992839713/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46291099/50000000 : ℝ)) (y := (992839713/1000000000 : ℝ)) (X := (7901721683371/50000000000000 : ℝ)) (Y := (84196574419371/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992839713/1000000000 : ℝ) ^ p + (46291099/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992839713/1000000000 : ℝ)) (y := (46291099/50000000 : ℝ)) (X := (84196574419371/100000000000000 : ℝ)) (Y := (7901721683371/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918661693/1000000000 : ℝ)) (τ := (46291099/50000000 : ℝ)) (σ := (992839713/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (158018813/167239860 : ℝ) ^ p + (275291219/278733100 : ℝ) ^ p := by
    exact cert_lt (x := (158018813/167239860 : ℝ)) (y := (275291219/278733100 : ℝ)) (X := (25727372436011/100000000000000 : ℝ)) (Y := (18568157214523/25000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46291099/50000000 : ℝ)) (n' := (8361993/10000000 : ℝ)) (Ab := (158018813/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (92606171/100000000 : ℝ) ^ p + (124098911/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (92606171/100000000 : ℝ)) (y := (124098911/125000000 : ℝ)) (X := (993855596491/6250000000000 : ℝ)) (Y := (84098327082747/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124098911/125000000 : ℝ) ^ p + (92606171/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (124098911/125000000 : ℝ)) (y := (92606171/100000000 : ℝ)) (X := (84098327082747/100000000000000 : ℝ)) (Y := (993855596491/6250000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (959426499/500000000 : ℝ)) (τ := (92606171/100000000 : ℝ)) (σ := (124098911/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (790351268/836481707 : ℝ) ^ p + (826156064/836481707 : ℝ) ^ p := by
    exact cert_lt (x := (790351268/836481707 : ℝ)) (y := (826156064/836481707 : ℝ)) (X := (12859933718727/50000000000000 : ℝ)) (Y := (74280133865293/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (92606171/100000000 : ℝ)) (n' := (836481707/1000000000 : ℝ)) (Ab := (197587817/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (92607187/100000000 : ℝ) ^ p + (248197307/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (92607187/100000000 : ℝ)) (y := (248197307/250000000 : ℝ)) (X := (1988233277123/12500000000000 : ℝ)) (Y := (84094150076969/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248197307/250000000 : ℝ) ^ p + (92607187/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248197307/250000000 : ℝ)) (y := (92607187/100000000 : ℝ)) (X := (84094150076969/100000000000000 : ℝ)) (Y := (1988233277123/12500000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (959430549/500000000 : ℝ)) (τ := (92607187/100000000 : ℝ)) (σ := (248197307/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (790362167/836493674 : ℝ) ^ p + (826168031/836493674 : ℝ) ^ p := by
    exact cert_lt (x := (790362167/836493674 : ℝ)) (y := (826168031/836493674 : ℝ)) (X := (3214943698339/12500000000000 : ℝ)) (Y := (18570112948547/25000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (92607187/100000000 : ℝ)) (n' := (418246837/500000000 : ℝ)) (Ab := (790362167/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (9260723/10000000 : ℝ) ^ p + (992789141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (9260723/10000000 : ℝ)) (y := (992789141/1000000000 : ℝ)) (X := (3181208601763/20000000000000 : ℝ)) (Y := (84093973673819/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992789141/1000000000 : ℝ) ^ p + (9260723/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (992789141/1000000000 : ℝ)) (y := (9260723/10000000 : ℝ)) (X := (84093973673819/100000000000000 : ℝ)) (Y := (3181208601763/20000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1918861441/1000000000 : ℝ)) (τ := (9260723/10000000 : ℝ)) (σ := (992789141/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (197590657/209123545 : ℝ) ^ p + (826168537/836494180 : ℝ) ^ p := by
    exact cert_lt (x := (197590657/209123545 : ℝ)) (y := (826168537/836494180 : ℝ)) (X := (514390725411/2000000000000 : ℝ)) (Y := (37140232618493/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (9260723/10000000 : ℝ)) (n' := (41824709/50000000 : ℝ)) (Ab := (197590657/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926072317/1000000000 : ℝ) ^ p + (496394569/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (926072317/1000000000 : ℝ)) (y := (496394569/500000000 : ℝ)) (X := (7953024999149/50000000000000 : ℝ)) (Y := (42046983795479/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496394569/500000000 : ℝ) ^ p + (926072317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496394569/500000000 : ℝ)) (y := (926072317/1000000000 : ℝ)) (X := (42046983795479/50000000000000 : ℝ)) (Y := (7953024999149/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383772291/200000000 : ℝ)) (τ := (926072317/1000000000 : ℝ)) (σ := (496394569/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (395181323/418247100 : ℝ) ^ p + (275389519/278831400 : ℝ) ^ p := by
    exact cert_lt (x := (395181323/418247100 : ℝ)) (y := (275389519/278831400 : ℝ)) (X := (25719535571801/100000000000000 : ℝ)) (Y := (74280465768321/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926072317/1000000000 : ℝ)) (n' := (4182471/5000000 : ℝ)) (Ab := (395181323/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (926072319/1000000000 : ℝ) ^ p + (992789137/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926072319/1000000000 : ℝ)) (y := (992789137/1000000000 : ℝ)) (X := (1590605082059/10000000000000 : ℝ)) (Y := (42046982781669/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992789137/1000000000 : ℝ) ^ p + (926072319/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992789137/1000000000 : ℝ)) (y := (926072319/1000000000 : ℝ)) (X := (42046982781669/50000000000000 : ℝ)) (Y := (1590605082059/10000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (395181324/418247101 : ℝ) ^ p + (826168559/836494202 : ℝ) ^ p := by
    exact cert_lt (x := (395181324/418247101 : ℝ)) (y := (826168559/836494202 : ℝ)) (X := (25719535657719/100000000000000 : ℝ)) (Y := (14856093164291/20000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657903837/1806445021 : ℝ) ^ p + (1796119378/1806445021 : ℝ) ^ p := by
    exact cert_lt (x := (1657903837/1806445021 : ℝ)) (y := (1796119378/1806445021 : ℝ)) (X := (2564420278821/20000000000000 : ℝ)) (Y := (87177898838901/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1113010165/1193554979 : ℝ) ^ p + (1183229336/1193554979 : ℝ) ^ p := by
    exact cert_lt (x := (1113010165/1193554979 : ℝ)) (y := (1183229336/1193554979 : ℝ)) (X := (9389172243059/50000000000000 : ℝ)) (Y := (40610828013071/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992789137/1000000000 : ℝ)) (U := (1193554979/1000000000 : ℝ)) (Ab := (1657903837/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ)) (Ab := (222602033/200000000 : ℝ))
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

theorem localize21_slab093 (p : ℝ) (hpa : (765/32 : ℝ) ≤ p) (hpb : p ≤ (383/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193554979/1000000000 : ℝ)) ∧ coordinateBox (1149/2500 : ℝ) (11131/10000 : ℝ) (3873/5000 : ℝ) (237/200 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (67453401664459/41769000000000 : ℝ) ≤ X j i + X k i) ∧
    (24261399874693/4176900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (121427739/125000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(765/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (121427739/125000000 : ℝ))
      (by norm_num) 32 765 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(765/32 : ℝ)) ≤ (971421913/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971421913/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 765 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(383/16 : ℝ)) ≤ (971458683/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971458683/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 383 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (209483139413/10442250000000 : ℝ) (10325643/1000000000 : ℝ) (800000125307/4176900000000 : ℝ) (3033/2500 : ℝ) (971458683/500000000 : ℝ) (121427739/125000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (765/32 : ℝ)) (β := (383/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (209483139413/10442250000000 : ℝ)) (δ := (10325643/1000000000 : ℝ)) (h := (800000125307/4176900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (121427739/125000000 : ℝ)) (thia := (971421913/1000000000 : ℝ)) (thib := (971458683/1000000000 : ℝ))
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
  have hh := contract21_slab093 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 94, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab094 (p : ℝ) (hpa : (383/16 : ℝ) ≤ p) (hpb : p ≤ (767/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (8181616217/408433593750 : ℝ) (10310111/1000000000 : ℝ) (2000000313677/10455900000000 : ℝ) (3033/2500 : ℝ) (3035923/1562500 : ℝ) (485729341/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193567701/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2783/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2299/5000 : ℝ)
      else (1937/2500 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (8181616217/408433593750 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10310111/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (920333191/1000000000 : ℝ) ^ p + (31058921/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (920333191/1000000000 : ℝ)) (y := (31058921/31250000 : ℝ)) (X := (6835633264541/50000000000000 : ℝ)) (Y := (86328750865629/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31058921/31250000 : ℝ) ^ p + (920333191/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31058921/31250000 : ℝ)) (y := (920333191/1000000000 : ℝ)) (X := (86328750865629/100000000000000 : ℝ)) (Y := (6835633264541/50000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1914218663/1000000000 : ℝ)) (τ := (920333191/1000000000 : ℝ)) (σ := (31058921/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784212340/829685441 : ℝ) ^ p + (2043330/2069041 : ℝ) ^ p := by
    exact cert_lt (x := (784212340/829685441 : ℝ)) (y := (2043330/2069041 : ℝ)) (X := (25897023733963/100000000000000 : ℝ)) (Y := (741029771761/1000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (920333191/1000000000 : ℝ)) (n' := (829685441/1000000000 : ℝ)) (Ab := (39210617/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (231481763/250000000 : ℝ) ^ p + (3878307/3906250 : ℝ) ^ p := by
    exact cert_lt (x := (231481763/250000000 : ℝ)) (y := (3878307/3906250 : ℝ)) (X := (3952091845817/25000000000000 : ℝ)) (Y := (84191649540627/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (3878307/3906250 : ℝ) ^ p + (231481763/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (3878307/3906250 : ℝ)) (y := (231481763/250000000 : ℝ)) (X := (84191649540627/100000000000000 : ℝ)) (Y := (3952091845817/25000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (479693411/250000000 : ℝ)) (τ := (231481763/250000000 : ℝ)) (σ := (3878307/3906250 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (21950924/23230403 : ℝ) ^ p + (117997771/119470644 : ℝ) ^ p := by
    exact cert_lt (x := (21950924/23230403 : ℝ)) (y := (117997771/119470644 : ℝ)) (X := (1028808053799/4000000000000 : ℝ)) (Y := (74279800053873/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (231481763/250000000 : ℝ)) (n' := (209073627/250000000 : ℝ)) (Ab := (49389579/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115770771/125000000 : ℝ) ^ p + (992798279/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115770771/125000000 : ℝ)) (y := (992798279/1000000000 : ℝ)) (X := (15906508912023/100000000000000 : ℝ)) (Y := (10511688480057/12500000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992798279/1000000000 : ℝ) ^ p + (115770771/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992798279/1000000000 : ℝ)) (y := (115770771/125000000 : ℝ)) (X := (10511688480057/12500000000000 : ℝ)) (Y := (15906508912023/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918964447/1000000000 : ℝ)) (τ := (115770771/125000000 : ℝ)) (σ := (992798279/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (197622449/209144037 : ℝ) ^ p + (826266037/836576148 : ℝ) ^ p := by
    exact cert_lt (x := (197622449/209144037 : ℝ)) (y := (826266037/836576148 : ℝ)) (X := (12856359453513/50000000000000 : ℝ)) (Y := (14857456409817/20000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115770771/125000000 : ℝ)) (n' := (209144037/250000000 : ℝ)) (Ab := (197622449/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (926176283/1000000000 : ℝ) ^ p + (248199057/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (926176283/1000000000 : ℝ)) (y := (248199057/250000000 : ℝ)) (X := (15910673305003/100000000000000 : ℝ)) (Y := (21022335980549/25000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248199057/250000000 : ℝ) ^ p + (926176283/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248199057/250000000 : ℝ)) (y := (926176283/1000000000 : ℝ)) (X := (21022335980549/25000000000000 : ℝ)) (Y := (15910673305003/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1918972511/1000000000 : ℝ)) (τ := (926176283/1000000000 : ℝ)) (σ := (248199057/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (395250323/418294030 : ℝ) ^ p + (118039707/119512580 : ℝ) ^ p := by
    exact cert_lt (x := (395250323/418294030 : ℝ)) (y := (118039707/119512580 : ℝ)) (X := (25712402551333/100000000000000 : ℝ)) (Y := (37143799202953/50000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (926176283/1000000000 : ℝ)) (n' := (41829403/50000000 : ℝ)) (Ab := (395250323/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (926176711/1000000000 : ℝ) ^ p + (992796141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926176711/1000000000 : ℝ)) (y := (992796141/1000000000 : ℝ)) (X := (15910849537649/100000000000000 : ℝ)) (Y := (16817833460019/20000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992796141/1000000000 : ℝ) ^ p + (926176711/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992796141/1000000000 : ℝ)) (y := (926176711/1000000000 : ℝ)) (X := (16817833460019/20000000000000 : ℝ)) (Y := (15910849537649/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479743213/250000000 : ℝ)) (τ := (926176711/1000000000 : ℝ)) (σ := (992796141/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (46500065/49211092 : ℝ) ^ p + (118039779/119512652 : ℝ) ^ p := by
    exact cert_lt (x := (46500065/49211092 : ℝ)) (y := (118039779/119512652 : ℝ)) (X := (12856194557341/50000000000000 : ℝ)) (Y := (464297573693/625000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (926176711/1000000000 : ℝ)) (n' := (209147141/250000000 : ℝ)) (Ab := (158100221/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (115772091/125000000 : ℝ) ^ p + (496398069/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115772091/125000000 : ℝ)) (y := (496398069/500000000 : ℝ)) (X := (7955428268791/50000000000000 : ℝ)) (Y := (21022290302421/25000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496398069/500000000 : ℝ) ^ p + (115772091/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496398069/500000000 : ℝ)) (y := (115772091/125000000 : ℝ)) (X := (21022290302421/25000000000000 : ℝ)) (Y := (7955428268791/50000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (959486433/500000000 : ℝ)) (τ := (115772091/125000000 : ℝ)) (σ := (496398069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (197625281/209147146 : ℝ) ^ p + (826278473/836588584 : ℝ) ^ p := by
    exact cert_lt (x := (197625281/209147146 : ℝ)) (y := (826278473/836588584 : ℝ)) (X := (6428097298511/25000000000000 : ℝ)) (Y := (74287612322029/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (115772091/125000000 : ℝ)) (n' := (104573573/125000000 : ℝ)) (Ab := (197625281/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (92617673/100000000 : ℝ) ^ p + (992796137/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92617673/100000000 : ℝ)) (y := (992796137/1000000000 : ℝ)) (X := (994428585069/6250000000000 : ℝ)) (Y := (84089159179547/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992796137/1000000000 : ℝ) ^ p + (92617673/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992796137/1000000000 : ℝ)) (y := (92617673/100000000 : ℝ)) (X := (84089159179547/100000000000000 : ℝ)) (Y := (994428585069/6250000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (263500375/278862862 : ℝ) ^ p + (826278475/836588586 : ℝ) ^ p := by
    exact cert_lt (x := (263500375/278862862 : ℝ)) (y := (826278475/836588586 : ℝ)) (X := (12856194250159/50000000000000 : ℝ)) (Y := (9285951546893/12500000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1658064868/1806432299 : ℝ) ^ p + (256588884/258061757 : ℝ) ^ p := by
    exact cert_lt (x := (1658064868/1806432299 : ℝ)) (y := (256588884/258061757 : ℝ)) (X := (12819733298299/100000000000000 : ℝ)) (Y := (435901334493/500000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1113114315/1193567701 : ℝ) ^ p + (1183257590/1193567701 : ℝ) ^ p := by
    exact cert_lt (x := (1113114315/1193567701 : ℝ)) (y := (1183257590/1193567701 : ℝ)) (X := (3754932547137/20000000000000 : ℝ)) (Y := (16245067602591/20000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992796137/1000000000 : ℝ)) (U := (1193567701/1000000000 : ℝ)) (Ab := (414516217/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ)) (Ab := (222622863/200000000 : ℝ))
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

theorem localize21_slab094 (p : ℝ) (hpa : (383/16 : ℝ) ≤ p) (hpb : p ≤ (767/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1193567701/1000000000 : ℝ)) ∧ coordinateBox (2299/5000 : ℝ) (2783/2500 : ℝ) (1937/2500 : ℝ) (237/200 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (168878753705551/104559000000000 : ℝ) ≤ X j i + X k i) ∧
    (60735399686323/10455900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (485729341/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(383/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (485729341/500000000 : ℝ))
      (by norm_num) 16 383 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(383/16 : ℝ)) ≤ (971458683/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (971458683/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 383 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(767/32 : ℝ)) ≤ (3035923/3125000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (3035923/3125000 : ℝ))
      (by norm_num) (by norm_num) 32 767 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (8181616217/408433593750 : ℝ) (10310111/1000000000 : ℝ) (2000000313677/10455900000000 : ℝ) (3033/2500 : ℝ) (3035923/1562500 : ℝ) (485729341/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (383/16 : ℝ)) (β := (767/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (8181616217/408433593750 : ℝ)) (δ := (10310111/1000000000 : ℝ)) (h := (2000000313677/10455900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (485729341/500000000 : ℝ)) (thia := (971458683/1000000000 : ℝ)) (thib := (3035923/3125000 : ℝ))
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
  have hh := contract21_slab094 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 95, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab095 (p : ℝ) (hpa : (767/32 : ℝ) ≤ p) (hpb : p ≤ (24 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (418831583629/20939100000000 : ℝ) (10294629/1000000000 : ℝ) (4000000628173/20939100000000 : ℝ) (3033/2500 : ℝ) (485765971/250000000 : ℝ) (971495359/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596790219/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11133/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(23/50 : ℝ)
      else (31/40 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (418831583629/20939100000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10294629/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (460221129/500000000 : ℝ) ^ p + (248472943/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (460221129/500000000 : ℝ)) (y := (248472943/250000000 : ℝ)) (X := (3418670057579/25000000000000 : ℝ)) (Y := (43162668926319/50000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248472943/250000000 : ℝ) ^ p + (460221129/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248472943/250000000 : ℝ)) (y := (460221129/500000000 : ℝ)) (X := (43162668926319/50000000000000 : ℝ)) (Y := (3418670057579/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (191433403/100000000 : ℝ)) (τ := (460221129/500000000 : ℝ)) (σ := (248472943/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784356079/829786449 : ℝ) ^ p + (273163940/276595483 : ℝ) ^ p := by
    exact cert_lt (x := (784356079/829786449 : ℝ)) (y := (273163940/276595483 : ℝ)) (X := (101131470251/390625000000 : ℝ)) (Y := (18527586129919/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (460221129/500000000 : ℝ)) (n' := (829786449/1000000000 : ℝ)) (Ab := (784356079/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185206363/200000000 : ℝ) ^ p + (496426731/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (185206363/200000000 : ℝ)) (y := (496426731/500000000 : ℝ)) (X := (158132735681/1000000000000 : ℝ)) (Y := (84186742993677/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496426731/500000000 : ℝ) ^ p + (185206363/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496426731/500000000 : ℝ)) (y := (185206363/200000000 : ℝ)) (X := (84186742993677/100000000000000 : ℝ)) (Y := (158132735681/1000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918885277/1000000000 : ℝ)) (τ := (185206363/200000000 : ℝ)) (σ := (496426731/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (395186039/418194695 : ℝ) ^ p + (826094761/836389390 : ℝ) ^ p := by
    exact cert_lt (x := (395186039/418194695 : ℝ)) (y := (826094761/836389390 : ℝ)) (X := (25713061173443/100000000000000 : ℝ)) (Y := (74286940348189/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185206363/200000000 : ℝ)) (n' := (83638939/100000000 : ℝ)) (Ab := (395186039/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (463135159/500000000 : ℝ) ^ p + (992805261/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (463135159/500000000 : ℝ)) (y := (992805261/1000000000 : ℝ)) (X := (15911310071239/100000000000000 : ℝ)) (Y := (5255544217977/6250000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992805261/1000000000 : ℝ) ^ p + (463135159/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992805261/1000000000 : ℝ)) (y := (463135159/500000000 : ℝ)) (X := (5255544217977/6250000000000 : ℝ)) (Y := (15911310071239/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1919075579/1000000000 : ℝ)) (τ := (463135159/500000000 : ℝ)) (σ := (992805261/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (790627939/836670263 : ℝ) ^ p + (826375634/836670263 : ℝ) ^ p := by
    exact cert_lt (x := (790627939/836670263 : ℝ)) (y := (826375634/836670263 : ℝ)) (X := (803300044811/3125000000000 : ℝ)) (Y := (9286799919579/12500000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (463135159/500000000 : ℝ)) (n' := (836670263/1000000000 : ℝ)) (Ab := (790627939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (92628039/100000000 : ℝ) ^ p + (496401609/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (92628039/100000000 : ℝ)) (y := (496401609/500000000 : ℝ)) (X := (7957731475987/50000000000000 : ℝ)) (Y := (84084554669251/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496401609/500000000 : ℝ) ^ p + (92628039/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496401609/500000000 : ℝ)) (y := (92628039/100000000 : ℝ)) (X := (84084554669251/100000000000000 : ℝ)) (Y := (7957731475987/50000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239885451/125000000 : ℝ)) (τ := (92628039/100000000 : ℝ)) (σ := (496401609/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (790638743/836682123 : ℝ) ^ p + (275462498/278894041 : ℝ) ^ p := by
    exact cert_lt (x := (790638743/836682123 : ℝ)) (y := (275462498/278894041 : ℝ)) (X := (12852643355477/50000000000000 : ℝ)) (Y := (18573678555627/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (92628039/100000000 : ℝ)) (n' := (836682123/1000000000 : ℝ)) (Ab := (790638743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (463140407/500000000 : ℝ) ^ p + (248200783/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (463140407/500000000 : ℝ)) (y := (248200783/250000000 : ℝ)) (X := (15915637798171/100000000000000 : ℝ)) (Y := (16816875972169/20000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248200783/250000000 : ℝ) ^ p + (463140407/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248200783/250000000 : ℝ)) (y := (463140407/500000000 : ℝ)) (X := (16816875972169/20000000000000 : ℝ)) (Y := (15915637798171/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (959541973/500000000 : ℝ)) (τ := (463140407/500000000 : ℝ)) (σ := (248200783/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (395319599/418341311 : ℝ) ^ p + (826387993/836682622 : ℝ) ^ p := by
    exact cert_lt (x := (395319599/418341311 : ℝ)) (y := (826387993/836682622 : ℝ)) (X := (25705273805313/100000000000000 : ℝ)) (Y := (74294727470069/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (463140407/500000000 : ℝ)) (n' := (418341311/500000000 : ℝ)) (Ab := (395319599/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926280833/1000000000 : ℝ) ^ p + (124100391/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (926280833/1000000000 : ℝ)) (y := (124100391/125000000 : ℝ)) (X := (15915645633303/100000000000000 : ℝ)) (Y := (8408437173023/10000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124100391/125000000 : ℝ) ^ p + (926280833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124100391/125000000 : ℝ)) (y := (926280833/1000000000 : ℝ)) (X := (8408437173023/10000000000000 : ℝ)) (Y := (15915645633303/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (790639219/836682645 : ℝ) ^ p + (275462672/278894215 : ℝ) ^ p := by
    exact cert_lt (x := (790639219/836682645 : ℝ)) (y := (275462672/278894215 : ℝ)) (X := (6426318308089/25000000000000 : ℝ)) (Y := (37147364040339/50000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (829112755/903209781 : ℝ) ^ p + (598708311/602139854 : ℝ) ^ p := by
    exact cert_lt (x := (829112755/903209781 : ℝ)) (y := (598708311/602139854 : ℝ)) (X := (12817376591499/100000000000000 : ℝ)) (Y := (21795655918433/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1113218285/1193580438 : ℝ) ^ p + (394428603/397860146 : ℝ) ^ p := by
    exact cert_lt (x := (1113218285/1193580438 : ℝ)) (y := (394428603/397860146 : ℝ)) (X := (9385498290157/50000000000000 : ℝ)) (Y := (16245800845341/20000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124100391/125000000 : ℝ)) (U := (596790219/500000000 : ℝ)) (Ab := (165822551/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ)) (Ab := (222643657/200000000 : ℝ))
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

theorem localize21_slab095 (p : ℝ) (hpa : (767/32 : ℝ) ≤ p) (hpb : p ≤ (24 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (596790219/500000000 : ℝ)) ∧ coordinateBox (23/50 : ℝ) (11133/10000 : ℝ) (31/40 : ℝ) (237/200 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (10570249887901/6543468750000 : ℝ) ≤ X j i + X k i) ∧
    (121634599371827/20939100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (971495359/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(767/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (971495359/1000000000 : ℝ))
      (by norm_num) 32 767 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(767/32 : ℝ)) ≤ (3035923/3125000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (3035923/3125000 : ℝ))
      (by norm_num) (by norm_num) 32 767 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(24 : ℝ)) ≤ (485765971/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (485765971/500000000 : ℝ))
      (by norm_num) (by norm_num) 1 24 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (418831583629/20939100000000 : ℝ) (10294629/1000000000 : ℝ) (4000000628173/20939100000000 : ℝ) (3033/2500 : ℝ) (485765971/250000000 : ℝ) (971495359/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (767/32 : ℝ)) (β := (24 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (418831583629/20939100000000 : ℝ)) (δ := (10294629/1000000000 : ℝ)) (h := (4000000628173/20939100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (971495359/1000000000 : ℝ)) (thia := (3035923/3125000 : ℝ)) (thib := (485765971/500000000 : ℝ))
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
  have hh := contract21_slab095 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
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

theorem localized_nonneg21_chunk05 (p : ℝ) (hpa : (47/2 : ℝ) ≤ p)
    (hpb : p ≤ (24 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (95/4 : ℝ) with hl | hr
  ·
    rcases le_total p (189/8 : ℝ) with hll | hlr
    ·
      rcases le_total p (377/16 : ℝ) with hlll | hllr
      ·
        rcases le_total p (753/32 : ℝ) with hllll | hlllr
        ·
          have hh := localize21_slab080 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab081 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg00 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (755/32 : ℝ) with hllrl | hllrr
        ·
          have hh := localize21_slab082 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab083 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (379/16 : ℝ) with hlrl | hlrr
      ·
        rcases le_total p (757/32 : ℝ) with hlrll | hlrlr
        ·
          have hh := localize21_slab084 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab085 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (759/32 : ℝ) with hlrrl | hlrrr
        ·
          have hh := localize21_slab086 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab087 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
  ·
    rcases le_total p (191/8 : ℝ) with hrl | hrr
    ·
      rcases le_total p (381/16 : ℝ) with hrll | hrlr
      ·
        rcases le_total p (761/32 : ℝ) with hrlll | hrllr
        ·
          have hh := localize21_slab088 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab089 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (763/32 : ℝ) with hrlrl | hrlrr
        ·
          have hh := localize21_slab090 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab091 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (383/16 : ℝ) with hrrl | hrrr
      ·
        rcases le_total p (765/32 : ℝ) with hrrll | hrrlr
        ·
          have hh := localize21_slab092 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab093 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (767/32 : ℝ) with hrrrl | hrrrr
        ·
          have hh := localize21_slab094 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab095 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD

end HlawkaSchatten.DiagonalRealBundle
theorem solution :
    ∀ p : ℝ, (47/2 : ℝ) ≤ p → p ≤ (24 : ℝ) →
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
  exact HlawkaSchatten.DiagonalRealBundle.localized_nonneg21_chunk05 p hp hpmax X hB hS hT hG

#print axioms solution
