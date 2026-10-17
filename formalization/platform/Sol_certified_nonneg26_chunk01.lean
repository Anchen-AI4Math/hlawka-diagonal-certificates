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
   cutoff26/contractor.json, slab 16, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab016 (p : ℝ) (hpa : (27 : ℝ) ≤ p) (hpb : p ≤ (433/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (18106310009/1196100000000 : ℝ) (194143/25000000 : ℝ) (200000035883/1196100000000 : ℝ) (591/500 : ℝ) (487356199/250000000 : ℝ) (974654609/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289000747/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(541/500 : ℝ) ≤ X j i ∧ X j i ≤ -(5501/10000 : ℝ)
      else (2039/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5737/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (18106310009/1196100000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (194143/25000000 : ℝ) := by norm_num
  have pc0 : 1 < (935814081/1000000000 : ℝ) ^ p + (993311417/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (935814081/1000000000 : ℝ)) (y := (993311417/1000000000 : ℝ)) (X := (16608021212527/100000000000000 : ℝ)) (Y := (83391997055237/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993311417/1000000000 : ℝ) ^ p + (935814081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993311417/1000000000 : ℝ)) (y := (935814081/1000000000 : ℝ)) (X := (83391997055237/100000000000000 : ℝ)) (Y := (16608021212527/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (964562749/500000000 : ℝ)) (τ := (935814081/1000000000 : ℝ)) (σ := (993311417/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (816718297/864192769 : ℝ) ^ p + (856427049/864192769 : ℝ) ^ p := by
    exact cert_lt (x := (816718297/864192769 : ℝ)) (y := (856427049/864192769 : ℝ)) (X := (5418400526099/25000000000000 : ℝ)) (Y := (78326399118189/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (935814081/1000000000 : ℝ)) (n' := (864192769/1000000000 : ℝ)) (Ab := (816718297/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939251329/1000000000 : ℝ) ^ p + (992541207/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939251329/1000000000 : ℝ)) (y := (992541207/1000000000 : ℝ)) (X := (3668072845509/20000000000000 : ℝ)) (Y := (81659653609841/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992541207/1000000000 : ℝ) ^ p + (939251329/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992541207/1000000000 : ℝ)) (y := (939251329/1000000000 : ℝ)) (X := (81659653609841/100000000000000 : ℝ)) (Y := (3668072845509/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (241474067/125000000 : ℝ)) (τ := (939251329/1000000000 : ℝ)) (σ := (992541207/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (273446323/289384679 : ℝ) ^ p + (860388317/868154037 : ℝ) ^ p := by
    exact cert_lt (x := (273446323/289384679 : ℝ)) (y := (860388317/868154037 : ℝ)) (X := (10792926822551/50000000000000 : ℝ)) (Y := (3136565899337/4000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939251329/1000000000 : ℝ)) (n' := (868154037/1000000000 : ℝ)) (Ab := (820338969/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469678093/500000000 : ℝ) ^ p + (248129069/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (469678093/500000000 : ℝ)) (y := (248129069/250000000 : ℝ)) (X := (3679171067679/20000000000000 : ℝ)) (Y := (81604162367073/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248129069/250000000 : ℝ) ^ p + (469678093/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248129069/250000000 : ℝ)) (y := (469678093/500000000 : ℝ)) (X := (81604162367073/100000000000000 : ℝ)) (Y := (3679171067679/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (965936231/500000000 : ℝ)) (τ := (469678093/500000000 : ℝ)) (σ := (248129069/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (820449205/868274654 : ℝ) ^ p + (430254467/434137327 : ℝ) ^ p := by
    exact cert_lt (x := (820449205/868274654 : ℝ)) (y := (430254467/434137327 : ℝ)) (X := (5395798114833/25000000000000 : ℝ)) (Y := (15683361651569/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469678093/500000000 : ℝ)) (n' := (434137327/500000000 : ℝ)) (Ab := (164089841/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (187871873/200000000 : ℝ) ^ p + (992515519/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187871873/200000000 : ℝ)) (y := (992515519/1000000000 : ℝ)) (X := (919877010591/5000000000000 : ℝ)) (Y := (40801239005027/50000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992515519/1000000000 : ℝ) ^ p + (187871873/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992515519/1000000000 : ℝ)) (y := (187871873/200000000 : ℝ)) (X := (40801239005027/50000000000000 : ℝ)) (Y := (919877010591/5000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (482968721/250000000 : ℝ)) (τ := (187871873/200000000 : ℝ)) (σ := (992515519/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820452548/868278311 : ℝ) ^ p + (860512591/868278311 : ℝ) ^ p := by
    exact cert_lt (x := (820452548/868278311 : ℝ)) (y := (860512591/868278311 : ℝ)) (X := (21583112319753/100000000000000 : ℝ)) (Y := (78416888919967/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (187871873/200000000 : ℝ)) (n' := (868278311/1000000000 : ℝ)) (Ab := (205113137/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (469679731/500000000 : ℝ) ^ p + (124064437/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (469679731/500000000 : ℝ)) (y := (124064437/125000000 : ℝ)) (X := (18397591624261/100000000000000 : ℝ)) (Y := (16320485366921/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124064437/125000000 : ℝ) ^ p + (469679731/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124064437/125000000 : ℝ)) (y := (469679731/500000000 : ℝ)) (X := (16320485366921/20000000000000 : ℝ)) (Y := (18397591624261/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (965937479/500000000 : ℝ)) (τ := (469679731/500000000 : ℝ)) (σ := (124064437/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (820452649/868278422 : ℝ) ^ p + (430256351/434139211 : ℝ) ^ p := by
    exact cert_lt (x := (820452649/868278422 : ℝ)) (y := (430256351/434139211 : ℝ)) (X := (10791554776627/50000000000000 : ℝ)) (Y := (3136675654731/4000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (469679731/500000000 : ℝ)) (n' := (434139211/500000000 : ℝ)) (Ab := (820452649/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (187871893/200000000 : ℝ) ^ p + (198503099/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (187871893/200000000 : ℝ)) (y := (198503099/200000000 : ℝ)) (X := (18397593214339/100000000000000 : ℝ)) (Y := (81602424609587/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198503099/200000000 : ℝ) ^ p + (187871893/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198503099/200000000 : ℝ)) (y := (187871893/200000000 : ℝ)) (X := (81602424609587/100000000000000 : ℝ)) (Y := (18397593214339/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (820452653/868278426 : ℝ) ^ p + (430256353/434139213 : ℝ) ^ p := by
    exact cert_lt (x := (820452653/868278426 : ℝ)) (y := (430256353/434139213 : ℝ)) (X := (21583109710107/100000000000000 : ℝ)) (Y := (39208445728251/50000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (424593492/460999253 : ℝ) ^ p + (459057823/460999253 : ℝ) ^ p := by
    exact cert_lt (x := (424593492/460999253 : ℝ)) (y := (459057823/460999253 : ℝ)) (X := (10792972752569/100000000000000 : ℝ)) (Y := (17841405510937/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (270490719/289000747 : ℝ) ^ p + (287059317/289000747 : ℝ) ^ p := by
    exact cert_lt (x := (270490719/289000747 : ℝ)) (y := (287059317/289000747 : ℝ)) (X := (4168552038377/25000000000000 : ℝ)) (Y := (83325792661771/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198503099/200000000 : ℝ)) (U := (289000747/250000000 : ℝ)) (Ab := (106148373/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ)) (Ab := (270490719/250000000 : ℝ))
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

theorem localize26_slab016 (p : ℝ) (hpa : (27 : ℝ) ≤ p) (hpb : p ≤ (433/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (289000747/250000000 : ℝ)) ∧ coordinateBox (5501/10000 : ℝ) (541/500 : ℝ) (2039/2500 : ℝ) (5737/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (10028024070461/5980500000000 : ℝ) ≤ X j i + X k i) ∧
    (6976599964117/1196100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (974654609/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(27 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (974654609/1000000000 : ℝ))
      (by norm_num) 1 27 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(27 : ℝ)) ≤ (97465461/100000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (97465461/100000000 : ℝ))
      (by norm_num) (by norm_num) 1 27 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(433/16 : ℝ)) ≤ (487356199/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (487356199/500000000 : ℝ))
      (by norm_num) (by norm_num) 16 433 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (18106310009/1196100000000 : ℝ) (194143/25000000 : ℝ) (200000035883/1196100000000 : ℝ) (591/500 : ℝ) (487356199/250000000 : ℝ) (974654609/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (27 : ℝ)) (β := (433/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (18106310009/1196100000000 : ℝ)) (δ := (194143/25000000 : ℝ)) (h := (200000035883/1196100000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (974654609/1000000000 : ℝ)) (thia := (97465461/100000000 : ℝ)) (thib := (487356199/500000000 : ℝ))
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
  have hh := contract26_slab016 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 17, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab017 (p : ℝ) (hpa : (433/16 : ℝ) ≤ p) (hpb : p ≤ (217/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1448075293171/95909500000000 : ℝ) (7745029/1000000000 : ℝ) (3200000575457/19181900000000 : ℝ) (591/500 : ℝ) (974769923/500000000 : ℝ) (974712397/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578021569/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5411/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(344/625 : ℝ)
      else (4079/5000 : ℝ) ≤ X j i ∧ X j i ≤ (459/400 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1448075293171/95909500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7745029/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (187193899/200000000 : ℝ) ^ p + (248331041/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (187193899/200000000 : ℝ)) (y := (248331041/250000000 : ℝ)) (X := (16613971581029/100000000000000 : ℝ)) (Y := (667088376411/800000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248331041/250000000 : ℝ) ^ p + (187193899/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248331041/250000000 : ℝ)) (y := (187193899/200000000 : ℝ)) (X := (667088376411/800000000000 : ℝ)) (Y := (16613971581029/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1929293659/1000000000 : ℝ)) (τ := (187193899/200000000 : ℝ)) (σ := (248331041/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (816931089/864320062 : ℝ) ^ p + (856575033/864320062 : ℝ) ^ p := by
    exact cert_lt (x := (816931089/864320062 : ℝ)) (y := (856575033/864320062 : ℝ)) (X := (676988497289/3125000000000 : ℝ)) (Y := (78336369114873/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187193899/200000000 : ℝ)) (n' := (432160031/500000000 : ℝ)) (Ab := (816931089/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (469700711/500000000 : ℝ) ^ p + (992554899/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469700711/500000000 : ℝ)) (y := (992554899/1000000000 : ℝ)) (X := (18348018082403/100000000000000 : ℝ)) (Y := (1633039987271/2000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992554899/1000000000 : ℝ) ^ p + (469700711/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992554899/1000000000 : ℝ)) (y := (469700711/500000000 : ℝ)) (X := (1633039987271/2000000000000 : ℝ)) (Y := (18348018082403/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1931956321/1000000000 : ℝ)) (τ := (469700711/500000000 : ℝ)) (σ := (992554899/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (205136499/217068568 : ℝ) ^ p + (860529243/868274272 : ℝ) ^ p := by
    exact cert_lt (x := (205136499/217068568 : ℝ)) (y := (860529243/868274272 : ℝ)) (X := (21576087624427/100000000000000 : ℝ)) (Y := (9802989160769/12500000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (469700711/500000000 : ℝ)) (n' := (27133571/31250000 : ℝ)) (Ab := (205136499/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469752901/500000000 : ℝ) ^ p + (992530073/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469752901/500000000 : ℝ)) (y := (992530073/1000000000 : ℝ)) (X := (3680679680391/20000000000000 : ℝ)) (Y := (40798310067787/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992530073/1000000000 : ℝ) ^ p + (469752901/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992530073/1000000000 : ℝ)) (y := (469752901/500000000 : ℝ)) (X := (40798310067787/50000000000000 : ℝ)) (Y := (3680679680391/20000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (15456287/8000000 : ℝ)) (τ := (469752901/500000000 : ℝ)) (σ := (992530073/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (410327863/434197156 : ℝ) ^ p + (860649283/868394312 : ℝ) ^ p := by
    exact cert_lt (x := (410327863/434197156 : ℝ)) (y := (860649283/868394312 : ℝ)) (X := (2696680116077/12500000000000 : ℝ)) (Y := (784265599071/1000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469752901/500000000 : ℝ)) (n' := (108549289/125000000 : ℝ)) (Ab := (410327863/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939508957/1000000000 : ℝ) ^ p + (992529321/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939508957/1000000000 : ℝ)) (y := (992529321/1000000000 : ℝ)) (X := (18405074836969/100000000000000 : ℝ)) (Y := (16318988643547/20000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992529321/1000000000 : ℝ) ^ p + (939508957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992529321/1000000000 : ℝ)) (y := (939508957/1000000000 : ℝ)) (X := (16318988643547/20000000000000 : ℝ)) (Y := (18405074836969/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966019139/500000000 : ℝ)) (τ := (939508957/1000000000 : ℝ)) (σ := (992529321/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820659043/868397940 : ℝ) ^ p + (860652911/868397940 : ℝ) ^ p := by
    exact cert_lt (x := (820659043/868397940 : ℝ)) (y := (860652911/868397940 : ℝ)) (X := (1078668069111/5000000000000 : ℝ)) (Y := (39213319943279/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939508957/1000000000 : ℝ)) (n' := (43419897/50000000 : ℝ)) (Ab := (820659043/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (939509053/1000000000 : ℝ) ^ p + (496264649/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (939509053/1000000000 : ℝ)) (y := (496264649/500000000 : ℝ)) (X := (9202562924829/50000000000000 : ℝ)) (Y := (20398722982387/25000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496264649/500000000 : ℝ) ^ p + (939509053/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496264649/500000000 : ℝ)) (y := (939509053/1000000000 : ℝ)) (X := (20398722982387/25000000000000 : ℝ)) (Y := (9202562924829/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1932038351/1000000000 : ℝ)) (τ := (939509053/1000000000 : ℝ)) (σ := (496264649/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (273553048/289466017 : ℝ) ^ p + (860653022/868398051 : ℝ) ^ p := by
    exact cert_lt (x := (273553048/289466017 : ℝ)) (y := (860653022/868398051 : ℝ)) (X := (4314671720553/20000000000000 : ℝ)) (Y := (1568532846671/2000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (939509053/1000000000 : ℝ)) (n' := (868398051/1000000000 : ℝ)) (Ab := (102582393/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (14679829/15625000 : ℝ) ^ p + (992529297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14679829/15625000 : ℝ)) (y := (992529297/1000000000 : ℝ)) (X := (18405127443807/100000000000000 : ℝ)) (Y := (20398722424907/25000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992529297/1000000000 : ℝ) ^ p + (14679829/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (992529297/1000000000 : ℝ)) (y := (14679829/15625000 : ℝ)) (X := (20398722424907/25000000000000 : ℝ)) (Y := (18405127443807/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (273553049/289466018 : ℝ) ^ p + (860653025/868398054 : ℝ) ^ p := by
    exact cert_lt (x := (273553049/289466018 : ℝ)) (y := (860653025/868398054 : ℝ)) (X := (21573358720363/100000000000000 : ℝ)) (Y := (15685328479937/20000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (849319272/921978431 : ℝ) ^ p + (1836211833/1843956862 : ℝ) ^ p := by
    exact cert_lt (x := (849319272/921978431 : ℝ)) (y := (1836211833/1843956862 : ℝ)) (X := (10789458617667/100000000000000 : ℝ)) (Y := (44605270810571/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082150759/1156043138 : ℝ) ^ p + (1148298109/1156043138 : ℝ) ^ p := by
    exact cert_lt (x := (1082150759/1156043138 : ℝ)) (y := (1148298109/1156043138 : ℝ)) (X := (16668053187909/100000000000000 : ℝ)) (Y := (41665973743077/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992529297/1000000000 : ℝ)) (U := (578021569/500000000 : ℝ)) (Ab := (106164909/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ)) (Ab := (1082150759/1000000000 : ℝ))
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

theorem localize26_slab017 (p : ℝ) (hpa : (433/16 : ℝ) ≤ p) (hpb : p ≤ (217/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (578021569/500000000 : ℝ)) ∧ coordinateBox (344/625 : ℝ) (5411/5000 : ℝ) (4079/5000 : ℝ) (459/400 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (80426489848447/47954750000000 : ℝ) ≤ X j i + X k i) ∧
    (111891399424543/19181900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (974712397/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(433/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (974712397/1000000000 : ℝ))
      (by norm_num) 16 433 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(433/16 : ℝ)) ≤ (487356199/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (487356199/500000000 : ℝ))
      (by norm_num) (by norm_num) 16 433 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(217/8 : ℝ)) ≤ (974769923/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974769923/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 217 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (1448075293171/95909500000000 : ℝ) (7745029/1000000000 : ℝ) (3200000575457/19181900000000 : ℝ) (591/500 : ℝ) (974769923/500000000 : ℝ) (974712397/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (433/16 : ℝ)) (β := (217/8 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1448075293171/95909500000000 : ℝ)) (δ := (7745029/1000000000 : ℝ)) (h := (3200000575457/19181900000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (974712397/1000000000 : ℝ)) (thia := (487356199/500000000 : ℝ)) (thib := (974769923/1000000000 : ℝ))
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
  have hh := contract26_slab017 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 18, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab018 (p : ℝ) (hpa : (217/8 : ℝ) ≤ p) (hpb : p ≤ (435/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (90477980713/6008187500000 : ℝ) (3862223/500000000 : ℝ) (1600000288393/9613100000000 : ℝ) (591/500 : ℝ) (974827187/500000000 : ℝ) (487384961/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156083193/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1353/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(2753/5000 : ℝ)
      else (8161/10000 : ℝ) ≤ X j i ∧ X j i ≤ (459/400 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (90477980713/6008187500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3862223/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (936124161/1000000000 : ℝ) ^ p + (31041777/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (936124161/1000000000 : ℝ)) (y := (31041777/31250000 : ℝ)) (X := (8309947780907/50000000000000 : ℝ)) (Y := (41690061794719/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31041777/31250000 : ℝ) ^ p + (936124161/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31041777/31250000 : ℝ)) (y := (936124161/1000000000 : ℝ)) (X := (41690061794719/50000000000000 : ℝ)) (Y := (8309947780907/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (77178441/40000000 : ℝ)) (τ := (936124161/1000000000 : ℝ)) (σ := (31041777/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817142898/864446657 : ℝ) ^ p + (856722211/864446657 : ℝ) ^ p := by
    exact cert_lt (x := (817142898/864446657 : ℝ)) (y := (856722211/864446657 : ℝ)) (X := (21653712756571/100000000000000 : ℝ)) (Y := (78346288625339/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936124161/1000000000 : ℝ)) (n' := (864446657/1000000000 : ℝ)) (Ab := (408571449/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (37582031/40000000 : ℝ) ^ p + (31017767/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (37582031/40000000 : ℝ)) (y := (31017767/31250000 : ℝ)) (X := (18355635965807/100000000000000 : ℝ)) (Y := (3265775243539/4000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (31017767/31250000 : ℝ) ^ p + (37582031/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (31017767/31250000 : ℝ)) (y := (37582031/40000000 : ℝ)) (X := (3265775243539/4000000000000 : ℝ)) (Y := (18355635965807/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1932119319/1000000000 : ℝ)) (τ := (37582031/40000000 : ℝ)) (σ := (31017767/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (4856521/5138425 : ℝ) ^ p + (860669379/868393825 : ℝ) ^ p := by
    exact cert_lt (x := (4856521/5138425 : ℝ)) (y := (860669379/868393825 : ℝ)) (X := (2695796440961/12500000000000 : ℝ)) (Y := (78433629385503/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (37582031/40000000 : ℝ)) (n' := (34735753/40000000 : ℝ)) (Ab := (820752049/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (23491367/25000000 : ℝ) ^ p + (496271911/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (23491367/25000000 : ℝ)) (y := (496271911/500000000 : ℝ)) (X := (18410905258381/100000000000000 : ℝ)) (Y := (40794556334751/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496271911/500000000 : ℝ) ^ p + (23491367/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (496271911/500000000 : ℝ)) (y := (23491367/25000000 : ℝ)) (X := (40794556334751/50000000000000 : ℝ)) (Y := (18410905258381/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (966099251/500000000 : ℝ)) (τ := (23491367/25000000 : ℝ)) (σ := (496271911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (205215319/217128323 : ℝ) ^ p + (430394423/434256646 : ℝ) ^ p := by
    exact cert_lt (x := (205215319/217128323 : ℝ)) (y := (430394423/434256646 : ℝ)) (X := (1347733684151/6250000000000 : ℝ)) (Y := (78436261962513/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (23491367/25000000 : ℝ)) (n' := (217128323/250000000 : ℝ)) (Ab := (205215319/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939657811/1000000000 : ℝ) ^ p + (248135769/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (939657811/1000000000 : ℝ)) (y := (248135769/250000000 : ℝ)) (X := (2301571648707/12500000000000 : ℝ)) (Y := (81587445474701/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248135769/250000000 : ℝ) ^ p + (939657811/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248135769/250000000 : ℝ)) (y := (939657811/1000000000 : ℝ)) (X := (81587445474701/100000000000000 : ℝ)) (Y := (2301571648707/12500000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1932200887/1000000000 : ℝ)) (τ := (939657811/1000000000 : ℝ)) (σ := (248135769/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820864567/868516891 : ℝ) ^ p + (860792445/868516891 : ℝ) ^ p := by
    exact cert_lt (x := (820864567/868516891 : ℝ)) (y := (860792445/868516891 : ℝ)) (X := (1078183000049/5000000000000 : ℝ)) (Y := (39218170630113/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939657811/1000000000 : ℝ)) (n' := (868516891/1000000000 : ℝ)) (Ab := (820864567/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (469828953/500000000 : ℝ) ^ p + (992543053/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469828953/500000000 : ℝ)) (y := (992543053/1000000000 : ℝ)) (X := (147300990399/800000000000 : ℝ)) (Y := (3263495762951/4000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992543053/1000000000 : ℝ) ^ p + (469828953/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992543053/1000000000 : ℝ)) (y := (469828953/500000000 : ℝ)) (X := (3263495762951/4000000000000 : ℝ)) (Y := (147300990399/800000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1932200959/1000000000 : ℝ)) (τ := (469828953/500000000 : ℝ)) (σ := (992543053/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (820864667/868517001 : ℝ) ^ p + (860792555/868517001 : ℝ) ^ p := by
    exact cert_lt (x := (820864667/868517001 : ℝ)) (y := (860792555/868517001 : ℝ)) (X := (10781828584693/50000000000000 : ℝ)) (Y := (19609085920969/25000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (469828953/500000000 : ℝ)) (n' := (868517001/1000000000 : ℝ)) (Ab := (820864667/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (939657909/1000000000 : ℝ) ^ p + (248135763/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (939657909/1000000000 : ℝ)) (y := (248135763/250000000 : ℝ)) (X := (9206312699047/50000000000000 : ℝ)) (Y := (10198423979869/12500000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248135763/250000000 : ℝ) ^ p + (939657909/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248135763/250000000 : ℝ)) (y := (939657909/1000000000 : ℝ)) (X := (10198423979869/12500000000000 : ℝ)) (Y := (9206312699047/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (410432335/434258502 : ℝ) ^ p + (430396279/434258502 : ℝ) ^ p := by
    exact cert_lt (x := (410432335/434258502 : ℝ)) (y := (430396279/434258502 : ℝ)) (X := (21563657286943/100000000000000 : ℝ)) (Y := (9804542968747/12500000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1698901951/1843916807 : ℝ) ^ p + (1836192361/1843916807 : ℝ) ^ p := by
    exact cert_lt (x := (1698901951/1843916807 : ℝ)) (y := (1836192361/1843916807 : ℝ)) (X := (10785961137491/100000000000000 : ℝ)) (Y := (89214039202541/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082337953/1156083193 : ℝ) ^ p + (1148358747/1156083193 : ℝ) ^ p := by
    exact cert_lt (x := (1082337953/1156083193 : ℝ)) (y := (1148358747/1156083193 : ℝ)) (X := (16661925540583/100000000000000 : ℝ)) (Y := (83338074952761/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248135763/250000000 : ℝ)) (U := (1156083193/1000000000 : ℝ)) (Ab := (1698901951/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ)) (Ab := (1082337953/1000000000 : ℝ))
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

theorem localize26_slab018 (p : ℝ) (hpa : (217/8 : ℝ) ≤ p) (hpb : p ≤ (435/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1156083193/1000000000 : ℝ)) ∧ coordinateBox (2753/5000 : ℝ) (1353/1250 : ℝ) (8161/10000 : ℝ) (459/400 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (161257565612407/96131000000000 : ℝ) ≤ X j i + X k i) ∧
    (56078599711607/9613100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (487384961/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(217/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (487384961/500000000 : ℝ))
      (by norm_num) 8 217 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(217/8 : ℝ)) ≤ (974769923/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974769923/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 217 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(435/16 : ℝ)) ≤ (974827187/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974827187/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 435 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (90477980713/6008187500000 : ℝ) (3862223/500000000 : ℝ) (1600000288393/9613100000000 : ℝ) (591/500 : ℝ) (974827187/500000000 : ℝ) (487384961/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (217/8 : ℝ)) (β := (435/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (90477980713/6008187500000 : ℝ)) (δ := (3862223/500000000 : ℝ)) (h := (1600000288393/9613100000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (487384961/500000000 : ℝ)) (thia := (974769923/1000000000 : ℝ)) (thib := (974827187/1000000000 : ℝ))
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
  have hh := contract26_slab018 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 19, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab019 (p : ℝ) (hpa : (435/16 : ℝ) ≤ p) (hpb : p ≤ (109/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (36180552577/2408812500000 : ℝ) (770397/100000000 : ℝ) (640000115623/3854100000000 : ℝ) (591/500 : ℝ) (974884191/500000000 : ℝ) (487413593/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (23122463/20000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5413/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1377/2500 : ℝ)
      else (8163/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2869/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (36180552577/2408812500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (770397/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (936278083/1000000000 : ℝ) ^ p + (993349517/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (936278083/1000000000 : ℝ)) (y := (993349517/1000000000 : ℝ)) (X := (3325158533483/20000000000000 : ℝ)) (Y := (41687112962863/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993349517/1000000000 : ℝ) ^ p + (936278083/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993349517/1000000000 : ℝ)) (y := (936278083/1000000000 : ℝ)) (X := (41687112962863/50000000000000 : ℝ)) (Y := (3325158533483/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (4824069/2500000 : ℝ)) (τ := (936278083/1000000000 : ℝ)) (σ := (993349517/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817353727/864572558 : ℝ) ^ p + (428434294/432286279 : ℝ) ^ p := by
    exact cert_lt (x := (817353727/864572558 : ℝ)) (y := (428434294/432286279 : ℝ)) (X := (1082192128577/5000000000000 : ℝ)) (Y := (78356158418043/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936278083/1000000000 : ℝ)) (n' := (432286279/500000000 : ℝ)) (Ab := (817353727/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939699391/1000000000 : ℝ) ^ p + (992582143/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939699391/1000000000 : ℝ)) (y := (992582143/1000000000 : ℝ)) (X := (18363216820113/100000000000000 : ℝ)) (Y := (81636800292541/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992582143/1000000000 : ℝ) ^ p + (939699391/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992582143/1000000000 : ℝ)) (y := (939699391/1000000000 : ℝ)) (X := (81636800292541/100000000000000 : ℝ)) (Y := (18363216820113/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (966140767/500000000 : ℝ)) (τ := (939699391/1000000000 : ℝ)) (σ := (992582143/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (820957133/868512700 : ℝ) ^ p + (86080873/86851270 : ℝ) ^ p := by
    exact cert_lt (x := (820957133/868512700 : ℝ)) (y := (86080873/86851270 : ℝ)) (X := (4311340942351/20000000000000 : ℝ)) (Y := (39221648272359/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939699391/1000000000 : ℝ)) (n' := (8685127/10000000 : ℝ)) (Ab := (820957133/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37592113/40000000 : ℝ) ^ p + (248139381/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (37592113/40000000 : ℝ)) (y := (248139381/250000000 : ℝ)) (X := (2302296990323/12500000000000 : ℝ)) (Y := (81581641460931/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248139381/250000000 : ℝ) ^ p + (37592113/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (248139381/250000000 : ℝ)) (y := (37592113/40000000 : ℝ)) (X := (81581641460931/100000000000000 : ℝ)) (Y := (2302296990323/12500000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1932360349/1000000000 : ℝ)) (τ := (37592113/40000000 : ℝ)) (σ := (248139381/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (45614770/48257311 : ℝ) ^ p + (143487938/144771933 : ℝ) ^ p := by
    exact cert_lt (x := (45614770/48257311 : ℝ)) (y := (143487938/144771933 : ℝ)) (X := (21554085866013/100000000000000 : ℝ)) (Y := (3137836607479/4000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37592113/40000000 : ℝ)) (n' := (434315799/500000000 : ℝ)) (Ab := (41053293/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939805933/1000000000 : ℝ) ^ p + (992556783/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939805933/1000000000 : ℝ)) (y := (992556783/1000000000 : ℝ)) (X := (18420035818873/100000000000000 : ℝ)) (Y := (81579981808247/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992556783/1000000000 : ℝ) ^ p + (939805933/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992556783/1000000000 : ℝ)) (y := (939805933/1000000000 : ℝ)) (X := (81579981808247/100000000000000 : ℝ)) (Y := (18420035818873/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (483090679/250000000 : ℝ)) (τ := (939805933/1000000000 : ℝ)) (σ := (992556783/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (91229903/96515019 : ℝ) ^ p + (286977067/289545057 : ℝ) ^ p := by
    exact cert_lt (x := (91229903/96515019 : ℝ)) (y := (286977067/289545057 : ℝ)) (X := (4310801386297/20000000000000 : ℝ)) (Y := (39222996934959/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939805933/1000000000 : ℝ)) (n' := (868635171/1000000000 : ℝ)) (Ab := (821069127/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (469903013/500000000 : ℝ) ^ p + (992556761/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469903013/500000000 : ℝ)) (y := (992556761/1000000000 : ℝ)) (X := (3684017097961/20000000000000 : ℝ)) (Y := (16315986506861/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992556761/1000000000 : ℝ) ^ p + (469903013/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992556761/1000000000 : ℝ)) (y := (469903013/500000000 : ℝ)) (X := (16315986506861/20000000000000 : ℝ)) (Y := (3684017097961/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1932362787/1000000000 : ℝ)) (τ := (469903013/500000000 : ℝ)) (σ := (992556761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (821069225/868635278 : ℝ) ^ p + (430465654/434317639 : ℝ) ^ p := by
    exact cert_lt (x := (821069225/868635278 : ℝ)) (y := (430465654/434317639 : ℝ)) (X := (10777002342391/50000000000000 : ℝ)) (Y := (78445996226213/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (469903013/500000000 : ℝ)) (n' := (434317639/500000000 : ℝ)) (Ab := (32842769/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (939806029/1000000000 : ℝ) ^ p + (24813919/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (939806029/1000000000 : ℝ)) (y := (24813919/25000000 : ℝ)) (X := (3684017418419/20000000000000 : ℝ)) (Y := (81579930294581/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (24813919/25000000 : ℝ) ^ p + (939806029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24813919/25000000 : ℝ)) (y := (939806029/1000000000 : ℝ)) (X := (81579930294581/100000000000000 : ℝ)) (Y := (3684017418419/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (821069228/868635281 : ℝ) ^ p + (860931311/868635281 : ℝ) ^ p := by
    exact cert_lt (x := (821069228/868635281 : ℝ)) (y := (860931311/868635281 : ℝ)) (X := (10777002401149/50000000000000 : ℝ)) (Y := (78445996292277/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (849582098/921938425 : ℝ) ^ p + (183617288/184387685 : ℝ) ^ p := by
    exact cert_lt (x := (849582098/921938425 : ℝ)) (y := (183617288/184387685 : ℝ)) (X := (134780994761/1250000000000 : ℝ)) (Y := (5576095040917/6250000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082524459/1156123150 : ℝ) ^ p + (114841918/115612315 : ℝ) ^ p := by
    exact cert_lt (x := (1082524459/1156123150 : ℝ)) (y := (114841918/115612315 : ℝ)) (X := (8327912554513/50000000000000 : ℝ)) (Y := (41672087767457/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (24813919/25000000 : ℝ)) (U := (23122463/20000000 : ℝ)) (Ab := (424791049/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ)) (Ab := (1082524459/1000000000 : ℝ))
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

theorem localize26_slab019 (p : ℝ) (hpa : (435/16 : ℝ) ≤ p) (hpb : p ≤ (109/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (23122463/20000000 : ℝ)) ∧ coordinateBox (1377/2500 : ℝ) (5413/5000 : ℝ) (8163/10000 : ℝ) (2869/2500 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (1616621432261/963525000000 : ℝ) ≤ X j i + X k i) ∧
    (22484599884377/3854100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (487413593/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(435/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (487413593/500000000 : ℝ))
      (by norm_num) 16 435 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(435/16 : ℝ)) ≤ (974827187/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974827187/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 435 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(109/4 : ℝ)) ≤ (974884191/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974884191/1000000000 : ℝ))
      (by norm_num) (by norm_num) 4 109 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (36180552577/2408812500000 : ℝ) (770397/100000000 : ℝ) (640000115623/3854100000000 : ℝ) (591/500 : ℝ) (974884191/500000000 : ℝ) (487413593/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (435/16 : ℝ)) (β := (109/4 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (36180552577/2408812500000 : ℝ)) (δ := (770397/100000000 : ℝ)) (h := (640000115623/3854100000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (487413593/500000000 : ℝ)) (thia := (974827187/1000000000 : ℝ)) (thib := (974884191/1000000000 : ℝ))
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
  have hh := contract26_slab019 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 20, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab020 (p : ℝ) (hpa : (109/4 : ℝ) ≤ p) (hpb : p ≤ (437/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (90424879189/6035875000000 : ℝ) (7683599/1000000000 : ℝ) (800000144861/4828700000000 : ℝ) (591/500 : ℝ) (487470469/250000000 : ℝ) (97488419/100000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231232601/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2707/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(5511/10000 : ℝ)
      else (1633/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2869/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (90424879189/6035875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7683599/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (936431273/1000000000 : ℝ) ^ p + (993362123/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (936431273/1000000000 : ℝ)) (y := (993362123/1000000000 : ℝ)) (X := (16631666307741/100000000000000 : ℝ)) (Y := (10421044164599/12500000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993362123/1000000000 : ℝ) ^ p + (936431273/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993362123/1000000000 : ℝ)) (y := (936431273/1000000000 : ℝ)) (X := (10421044164599/12500000000000 : ℝ)) (Y := (16631666307741/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (482448349/250000000 : ℝ)) (τ := (936431273/1000000000 : ℝ)) (σ := (993362123/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817563590/864697781 : ℝ) ^ p + (857014182/864697781 : ℝ) ^ p := by
    exact cert_lt (x := (817563590/864697781 : ℝ)) (y := (857014182/864697781 : ℝ)) (X := (10817009522467/50000000000000 : ℝ)) (Y := (31346392819/40000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936431273/1000000000 : ℝ)) (n' := (864697781/1000000000 : ℝ)) (Ab := (81756359/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939847281/1000000000 : ℝ) ^ p + (198519139/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (939847281/1000000000 : ℝ)) (y := (198519139/200000000 : ℝ)) (X := (1837076387151/10000000000000 : ℝ)) (Y := (40814627005681/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198519139/200000000 : ℝ) ^ p + (939847281/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198519139/200000000 : ℝ)) (y := (939847281/1000000000 : ℝ)) (X := (40814627005681/50000000000000 : ℝ)) (Y := (1837076387151/10000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60388843/31250000 : ℝ)) (τ := (939847281/1000000000 : ℝ)) (σ := (198519139/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (410580629/434315456 : ℝ) ^ p + (860947313/868630912 : ℝ) ^ p := by
    exact cert_lt (x := (410580629/434315456 : ℝ)) (y := (860947313/868630912 : ℝ)) (X := (1077354133647/5000000000000 : ℝ)) (Y := (3922645914013/5000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939847281/1000000000 : ℝ)) (n' := (6786179/7812500 : ℝ)) (Ab := (410580629/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469975123/500000000 : ℝ) ^ p + (992571179/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469975123/500000000 : ℝ)) (y := (992571179/1000000000 : ℝ)) (X := (18425812574943/100000000000000 : ℝ)) (Y := (81574205777209/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992571179/1000000000 : ℝ) ^ p + (469975123/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992571179/1000000000 : ℝ)) (y := (469975123/500000000 : ℝ)) (X := (81574205777209/100000000000000 : ℝ)) (Y := (18425812574943/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (77300857/40000000 : ℝ)) (τ := (469975123/500000000 : ℝ)) (σ := (992571179/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (205317372/217187311 : ℝ) ^ p + (78278695/78977204 : ℝ) ^ p := by
    exact cert_lt (x := (205317372/217187311 : ℝ)) (y := (78278695/78977204 : ℝ)) (X := (10772238929237/50000000000000 : ℝ)) (Y := (7845552307427/10000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469975123/500000000 : ℝ)) (n' := (217187311/250000000 : ℝ)) (Ab := (51329343/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939953331/1000000000 : ℝ) ^ p + (992570443/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939953331/1000000000 : ℝ)) (y := (992570443/1000000000 : ℝ)) (X := (575858261681/3125000000000 : ℝ)) (Y := (20393138428913/25000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992570443/1000000000 : ℝ) ^ p + (939953331/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992570443/1000000000 : ℝ)) (y := (939953331/1000000000 : ℝ)) (X := (20393138428913/25000000000000 : ℝ)) (Y := (575858261681/3125000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966261887/500000000 : ℝ)) (τ := (939953331/1000000000 : ℝ)) (σ := (992570443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (273757577/289584263 : ℝ) ^ p + (861069190/868752789 : ℝ) ^ p := by
    exact cert_lt (x := (273757577/289584263 : ℝ)) (y := (861069190/868752789 : ℝ)) (X := (21544400294941/100000000000000 : ℝ)) (Y := (39227800549623/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939953331/1000000000 : ℝ)) (n' := (868752789/1000000000 : ℝ)) (Ab := (821272731/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (939953423/1000000000 : ℝ) ^ p + (992570421/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939953423/1000000000 : ℝ)) (y := (992570421/1000000000 : ℝ)) (X := (9213756817731/50000000000000 : ℝ)) (Y := (81572504333873/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992570421/1000000000 : ℝ) ^ p + (939953423/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992570421/1000000000 : ℝ)) (y := (939953423/1000000000 : ℝ)) (X := (81572504333873/100000000000000 : ℝ)) (Y := (9213756817731/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (483130961/250000000 : ℝ)) (τ := (939953423/1000000000 : ℝ)) (σ := (992570421/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (821272828/868752895 : ℝ) ^ p + (861069296/868752895 : ℝ) ^ p := by
    exact cert_lt (x := (821272828/868752895 : ℝ)) (y := (861069296/868752895 : ℝ)) (X := (21544397997333/100000000000000 : ℝ)) (Y := (78455603432283/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (939953423/1000000000 : ℝ)) (n' := (173750579/200000000 : ℝ)) (Ab := (205318207/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (939953427/1000000000 : ℝ) ^ p + (49628521/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (939953427/1000000000 : ℝ)) (y := (49628521/50000000 : ℝ)) (X := (4606878944319/25000000000000 : ℝ)) (Y := (2549140690289/3125000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (49628521/50000000 : ℝ) ^ p + (939953427/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49628521/50000000 : ℝ)) (y := (939953427/1000000000 : ℝ)) (X := (2549140690289/3125000000000 : ℝ)) (Y := (4606878944319/25000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (821272831/868752899 : ℝ) ^ p + (123009900/124107557 : ℝ) ^ p := by
    exact cert_lt (x := (821272831/868752899 : ℝ)) (y := (123009900/124107557 : ℝ)) (X := (21544397437479/100000000000000 : ℝ)) (Y := (39227801760161/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1699425283/1843836995 : ℝ) ^ p + (23846148/23945935 : ℝ) ^ p := by
    exact cert_lt (x := (1699425283/1843836995 : ℝ)) (y := (23846148/23945935 : ℝ)) (X := (10779012544617/100000000000000 : ℝ)) (Y := (89220987678191/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (216542054/231232601 : ℝ) ^ p + (1148479406/1156163005 : ℝ) ^ p := by
    exact cert_lt (x := (216542054/231232601 : ℝ)) (y := (1148479406/1156163005 : ℝ)) (X := (16649748839167/100000000000000 : ℝ)) (Y := (83350251693151/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (49628521/50000000 : ℝ)) (U := (231232601/200000000 : ℝ)) (Ab := (1699425283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ)) (Ab := (108271027/100000000 : ℝ))
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

theorem localize26_slab020 (p : ℝ) (hpa : (109/4 : ℝ) ≤ p) (hpb : p ≤ (437/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (231232601/200000000 : ℝ)) ∧ coordinateBox (5511/10000 : ℝ) (2707/2500 : ℝ) (1633/2000 : ℝ) (2869/2500 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (16206671298939/9657400000000 : ℝ) ≤ X j i + X k i) ∧
    (28172199855139/4828700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (97488419/100000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(109/4 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (97488419/100000000 : ℝ))
      (by norm_num) 4 109 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(109/4 : ℝ)) ≤ (974884191/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974884191/1000000000 : ℝ))
      (by norm_num) (by norm_num) 4 109 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(437/16 : ℝ)) ≤ (487470469/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (487470469/500000000 : ℝ))
      (by norm_num) (by norm_num) 16 437 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (90424879189/6035875000000 : ℝ) (7683599/1000000000 : ℝ) (800000144861/4828700000000 : ℝ) (591/500 : ℝ) (487470469/250000000 : ℝ) (97488419/100000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (109/4 : ℝ)) (β := (437/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (90424879189/6035875000000 : ℝ)) (δ := (7683599/1000000000 : ℝ)) (h := (800000144861/4828700000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (97488419/100000000 : ℝ)) (thia := (974884191/1000000000 : ℝ)) (thib := (487470469/500000000 : ℝ))
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
  have hh := contract26_slab020 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 21, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab021 (p : ℝ) (hpa : (437/16 : ℝ) ≤ p) (hpb : p ≤ (219/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1446376288939/96795500000000 : ℝ) (957917/125000000 : ℝ) (3200000580773/19359100000000 : ℝ) (591/500 : ℝ) (974997429/500000000 : ℝ) (974940937/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144525347/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10829/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5513/10000 : ℝ)
      else (1021/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11477/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1446376288939/96795500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (957917/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (468291863/500000000 : ℝ) ^ p + (993374683/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468291863/500000000 : ℝ)) (y := (993374683/1000000000 : ℝ)) (X := (16637511680913/100000000000000 : ℝ)) (Y := (83362507316713/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993374683/1000000000 : ℝ) ^ p + (468291863/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993374683/1000000000 : ℝ)) (y := (468291863/500000000 : ℝ)) (X := (83362507316713/100000000000000 : ℝ)) (Y := (16637511680913/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1929958409/1000000000 : ℝ)) (τ := (468291863/500000000 : ℝ)) (σ := (993374683/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817772489/864822313 : ℝ) ^ p + (857158977/864822313 : ℝ) ^ p := by
    exact cert_lt (x := (817772489/864822313 : ℝ)) (y := (857158977/864822313 : ℝ)) (X := (10812125510807/50000000000000 : ℝ)) (Y := (39187874976861/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (468291863/500000000 : ℝ)) (n' := (864822313/1000000000 : ℝ)) (Ab := (817772489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939994443/1000000000 : ℝ) ^ p + (992609201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939994443/1000000000 : ℝ)) (y := (992609201/1000000000 : ℝ)) (X := (18378273444669/100000000000000 : ℝ)) (Y := (5101358985209/6250000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992609201/1000000000 : ℝ) ^ p + (939994443/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992609201/1000000000 : ℝ)) (y := (939994443/1000000000 : ℝ)) (X := (5101358985209/6250000000000 : ℝ)) (Y := (18378273444669/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (483150911/250000000 : ℝ)) (τ := (939994443/1000000000 : ℝ)) (σ := (992609201/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821364430/868748449 : ℝ) ^ p + (861085113/868748449 : ℝ) ^ p := by
    exact cert_lt (x := (821364430/868748449 : ℝ)) (y := (861085113/868748449 : ℝ)) (X := (21537516340839/100000000000000 : ℝ)) (Y := (78462485086501/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939994443/1000000000 : ℝ)) (n' := (868748449/1000000000 : ℝ)) (Ab := (82136443/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (940096941/1000000000 : ℝ) ^ p + (248146197/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (940096941/1000000000 : ℝ)) (y := (248146197/250000000 : ℝ)) (X := (3686642307409/20000000000000 : ℝ)) (Y := (40783403567797/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248146197/250000000 : ℝ) ^ p + (940096941/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248146197/250000000 : ℝ)) (y := (940096941/1000000000 : ℝ)) (X := (40783403567797/50000000000000 : ℝ)) (Y := (3686642307409/20000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1932681729/1000000000 : ℝ)) (τ := (940096941/1000000000 : ℝ)) (σ := (248146197/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (821472165/868866218 : ℝ) ^ p + (430601441/434433109 : ℝ) ^ p := by
    exact cert_lt (x := (821472165/868866218 : ℝ)) (y := (430601441/434433109 : ℝ)) (X := (21534925132667/100000000000000 : ℝ)) (Y := (39232538059791/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (940096941/1000000000 : ℝ)) (n' := (434433109/500000000 : ℝ)) (Ab := (164294433/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (235025001/250000000 : ℝ) ^ p + (992584057/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (235025001/250000000 : ℝ)) (y := (992584057/1000000000 : ℝ)) (X := (1843485571247/10000000000000 : ℝ)) (Y := (4078258135707/5000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992584057/1000000000 : ℝ) ^ p + (235025001/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992584057/1000000000 : ℝ)) (y := (235025001/250000000 : ℝ)) (X := (4078258135707/5000000000000 : ℝ)) (Y := (1843485571247/10000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1932684061/1000000000 : ℝ)) (τ := (235025001/250000000 : ℝ)) (σ := (992584057/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (821475384/868869737 : ℝ) ^ p + (861206401/868869737 : ℝ) ^ p := by
    exact cert_lt (x := (821475384/868869737 : ℝ)) (y := (861206401/868869737 : ℝ)) (X := (21534847593133/100000000000000 : ℝ)) (Y := (78465153531481/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (235025001/250000000 : ℝ)) (n' := (868869737/1000000000 : ℝ)) (Ab := (102684423/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (188020019/200000000 : ℝ) ^ p + (198516807/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (188020019/200000000 : ℝ)) (y := (198516807/200000000 : ℝ)) (X := (9217452281077/50000000000000 : ℝ)) (Y := (81565113224523/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198516807/200000000 : ℝ) ^ p + (188020019/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198516807/200000000 : ℝ)) (y := (188020019/200000000 : ℝ)) (X := (81565113224523/100000000000000 : ℝ)) (Y := (9217452281077/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (193268413/100000000 : ℝ)) (τ := (188020019/200000000 : ℝ)) (σ := (198516807/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (410737740/434434921 : ℝ) ^ p + (430603253/434434921 : ℝ) ^ p := by
    exact cert_lt (x := (410737740/434434921 : ℝ)) (y := (430603253/434434921 : ℝ)) (X := (2691855655581/12500000000000 : ℝ)) (Y := (78465155841291/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (188020019/200000000 : ℝ)) (n' := (434434921/500000000 : ℝ)) (Ab := (20536887/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (940100099/1000000000 : ℝ) ^ p + (496292017/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (940100099/1000000000 : ℝ)) (y := (496292017/500000000 : ℝ)) (X := (4608726677349/25000000000000 : ℝ)) (Y := (16313022194999/20000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496292017/500000000 : ℝ) ^ p + (940100099/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496292017/500000000 : ℝ)) (y := (940100099/1000000000 : ℝ)) (X := (16313022194999/20000000000000 : ℝ)) (Y := (4608726677349/25000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (410737742/434434923 : ℝ) ^ p + (430603255/434434923 : ℝ) ^ p := by
    exact cert_lt (x := (410737742/434434923 : ℝ)) (y := (430603255/434434923 : ℝ)) (X := (21534845401227/100000000000000 : ℝ)) (Y := (78465155929283/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1699685233/1843797224 : ℝ) ^ p + (229516736/230474653 : ℝ) ^ p := by
    exact cert_lt (x := (1699685233/1843797224 : ℝ)) (y := (229516736/230474653 : ℝ)) (X := (2693891274447/25000000000000 : ℝ)) (Y := (17844887045091/20000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082895425/1156202776 : ℝ) ^ p + (143567430/144525347 : ℝ) ^ p := by
    exact cert_lt (x := (1082895425/1156202776 : ℝ)) (y := (143567430/144525347 : ℝ)) (X := (8321852178107/50000000000000 : ℝ)) (Y := (41678148140203/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496292017/500000000 : ℝ)) (U := (144525347/125000000 : ℝ)) (Ab := (1699685233/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ)) (Ab := (43315817/40000000 : ℝ))
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

theorem localize26_slab021 (p : ℝ) (hpa : (437/16 : ℝ) ≤ p) (hpb : p ≤ (219/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (144525347/125000000 : ℝ)) ∧ coordinateBox (5513/10000 : ℝ) (10829/10000 : ℝ) (1021/1250 : ℝ) (11477/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (162471273227737/96795500000000 : ℝ) ≤ X j i + X k i) ∧
    (112954599419227/19359100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (974940937/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(437/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (974940937/1000000000 : ℝ))
      (by norm_num) 16 437 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(437/16 : ℝ)) ≤ (487470469/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (487470469/500000000 : ℝ))
      (by norm_num) (by norm_num) 16 437 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(219/8 : ℝ)) ≤ (974997429/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974997429/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 219 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (1446376288939/96795500000000 : ℝ) (957917/125000000 : ℝ) (3200000580773/19359100000000 : ℝ) (591/500 : ℝ) (974997429/500000000 : ℝ) (974940937/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (437/16 : ℝ)) (β := (219/8 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1446376288939/96795500000000 : ℝ)) (δ := (957917/125000000 : ℝ)) (h := (3200000580773/19359100000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (974940937/1000000000 : ℝ)) (thia := (487470469/500000000 : ℝ)) (thib := (974997429/1000000000 : ℝ))
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
  have hh := contract26_slab021 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 22, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab022 (p : ℝ) (hpa : (219/8 : ℝ) ≤ p) (hpb : p ≤ (439/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (361489081567/24254250000000 : ℝ) (7643177/1000000000 : ℝ) (1600000291051/9701700000000 : ℝ) (591/500 : ℝ) (975053667/500000000 : ℝ) (243749357/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156242449/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10831/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1103/2000 : ℝ)
      else (817/1000 : ℝ) ≤ X j i ∧ X j i ≤ (11477/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (361489081567/24254250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7643177/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (936735453/1000000000 : ℝ) ^ p + (993387197/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (936735453/1000000000 : ℝ)) (y := (993387197/1000000000 : ℝ)) (X := (3328666351679/20000000000000 : ℝ)) (Y := (83356687197711/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993387197/1000000000 : ℝ) ^ p + (936735453/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993387197/1000000000 : ℝ)) (y := (936735453/1000000000 : ℝ)) (X := (83356687197711/100000000000000 : ℝ)) (Y := (3328666351679/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (38602453/20000000 : ℝ)) (τ := (936735453/1000000000 : ℝ)) (σ := (993387197/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817980431/864946171 : ℝ) ^ p + (857302994/864946171 : ℝ) ^ p := by
    exact cert_lt (x := (817980431/864946171 : ℝ)) (y := (857302994/864946171 : ℝ)) (X := (21614530475611/100000000000000 : ℝ)) (Y := (78385470735979/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936735453/1000000000 : ℝ)) (n' := (864946171/1000000000 : ℝ)) (Ab := (817980431/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (188028177/200000000 : ℝ) ^ p + (496311331/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (188028177/200000000 : ℝ)) (y := (496311331/500000000 : ℝ)) (X := (18385747215901/100000000000000 : ℝ)) (Y := (81614271086833/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496311331/500000000 : ℝ) ^ p + (188028177/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496311331/500000000 : ℝ)) (y := (188028177/200000000 : ℝ)) (X := (81614271086833/100000000000000 : ℝ)) (Y := (18385747215901/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1932763547/1000000000 : ℝ)) (τ := (188028177/200000000 : ℝ)) (σ := (496311331/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821566652/868865327 : ℝ) ^ p + (861222150/868865327 : ℝ) ^ p := by
    exact cert_lt (x := (821566652/868865327 : ℝ)) (y := (861222150/868865327 : ℝ)) (X := (21527995540339/100000000000000 : ℝ)) (Y := (7847200550713/10000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (188028177/200000000 : ℝ)) (n' := (868865327/1000000000 : ℝ)) (Ab := (205391663/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (940242923/1000000000 : ℝ) ^ p + (992598349/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940242923/1000000000 : ℝ)) (y := (992598349/1000000000 : ℝ)) (X := (9220288594099/50000000000000 : ℝ)) (Y := (81559440309859/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992598349/1000000000 : ℝ) ^ p + (940242923/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992598349/1000000000 : ℝ)) (y := (940242923/1000000000 : ℝ)) (X := (81559440309859/100000000000000 : ℝ)) (Y := (9220288594099/50000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (241605159/125000000 : ℝ)) (τ := (940242923/1000000000 : ℝ)) (σ := (992598349/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (273891300/289660847 : ℝ) ^ p + (861339364/868982541 : ℝ) ^ p := by
    exact cert_lt (x := (273891300/289660847 : ℝ)) (y := (861339364/868982541 : ℝ)) (X := (1076270921341/5000000000000 : ℝ)) (Y := (78474582975377/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (940242923/1000000000 : ℝ)) (n' := (868982541/1000000000 : ℝ)) (Ab := (8216739/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (470122981/500000000 : ℝ) ^ p + (124074703/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (470122981/500000000 : ℝ)) (y := (124074703/125000000 : ℝ)) (X := (18442212604151/100000000000000 : ℝ)) (Y := (8155780583201/10000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124074703/125000000 : ℝ) ^ p + (470122981/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124074703/125000000 : ℝ)) (y := (470122981/500000000 : ℝ)) (X := (8155780583201/10000000000000 : ℝ)) (Y := (18442212604151/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966421793/500000000 : ℝ)) (τ := (470122981/500000000 : ℝ)) (σ := (124074703/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (410838547/434493016 : ℝ) ^ p + (861342855/868986032 : ℝ) ^ p := by
    exact cert_lt (x := (410838547/434493016 : ℝ)) (y := (861342855/868986032 : ℝ)) (X := (21525341557207/100000000000000 : ℝ)) (Y := (78474659731041/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (470122981/500000000 : ℝ)) (n' := (54311627/62500000 : ℝ)) (Ab := (410838547/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (235061513/250000000 : ℝ) ^ p + (496298801/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (235061513/250000000 : ℝ)) (y := (496298801/500000000 : ℝ)) (X := (18442261039133/100000000000000 : ℝ)) (Y := (16311551246911/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496298801/500000000 : ℝ) ^ p + (235061513/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496298801/500000000 : ℝ)) (y := (235061513/250000000 : ℝ)) (X := (16311551246911/20000000000000 : ℝ)) (Y := (18442261039133/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (966421827/500000000 : ℝ)) (τ := (235061513/250000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (273892396/289662045 : ℝ) ^ p + (861342958/868986135 : ℝ) ^ p := by
    exact cert_lt (x := (273892396/289662045 : ℝ)) (y := (861342958/868986135 : ℝ)) (X := (10762669559373/50000000000000 : ℝ)) (Y := (15694932399133/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (235061513/250000000 : ℝ)) (n' := (173797227/200000000 : ℝ)) (Ab := (205419297/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470123027/500000000 : ℝ) ^ p + (496298801/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (470123027/500000000 : ℝ)) (y := (496298801/500000000 : ℝ)) (X := (4610565528867/25000000000000 : ℝ)) (Y := (16311551246911/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496298801/500000000 : ℝ) ^ p + (470123027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496298801/500000000 : ℝ)) (y := (470123027/500000000 : ℝ)) (X := (16311551246911/20000000000000 : ℝ)) (Y := (4610565528867/25000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (273892397/289662046 : ℝ) ^ p + (861342961/868986138 : ℝ) ^ p := by
    exact cert_lt (x := (273892397/289662046 : ℝ)) (y := (861342961/868986138 : ℝ)) (X := (1076266961807/5000000000000 : ℝ)) (Y := (627797296493/800000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1699944040/1843757551 : ℝ) ^ p + (1836114374/1843757551 : ℝ) ^ p := by
    exact cert_lt (x := (1699944040/1843757551 : ℝ)) (y := (1836114374/1843757551 : ℝ)) (X := (10772132536983/100000000000000 : ℝ)) (Y := (44613933860927/50000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083079899/1156242449 : ℝ) ^ p + (1148599272/1156242449 : ℝ) ^ p := by
    exact cert_lt (x := (1083079899/1156242449 : ℝ)) (y := (1148599272/1156242449 : ℝ)) (X := (3327537001833/20000000000000 : ℝ)) (Y := (83362315612349/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496298801/500000000 : ℝ)) (U := (1156242449/1000000000 : ℝ)) (Ab := (42498601/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ)) (Ab := (1083079899/1000000000 : ℝ))
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

theorem localize26_slab022 (p : ℝ) (hpa : (219/8 : ℝ) ≤ p) (hpb : p ≤ (439/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1156242449/1000000000 : ℝ)) ∧ coordinateBox (1103/2000 : ℝ) (10831/10000 : ℝ) (817/1000 : ℝ) (11477/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (162875825355197/97017000000000 : ℝ) ≤ X j i + X k i) ∧
    (56610199708949/9701700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (243749357/250000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(219/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (243749357/250000000 : ℝ))
      (by norm_num) 8 219 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(219/8 : ℝ)) ≤ (974997429/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (974997429/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 219 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(439/16 : ℝ)) ≤ (975053667/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975053667/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 439 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (361489081567/24254250000000 : ℝ) (7643177/1000000000 : ℝ) (1600000291051/9701700000000 : ℝ) (591/500 : ℝ) (975053667/500000000 : ℝ) (243749357/250000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (219/8 : ℝ)) (β := (439/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (361489081567/24254250000000 : ℝ)) (δ := (7643177/1000000000 : ℝ)) (h := (1600000291051/9701700000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (243749357/250000000 : ℝ)) (thia := (974997429/1000000000 : ℝ)) (thib := (975053667/1000000000 : ℝ))
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
  have hh := contract26_slab022 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 23, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab023 (p : ℝ) (hpa : (439/16 : ℝ) ≤ p) (hpb : p ≤ (55/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (180692363579/12154812500000 : ℝ) (12197/1600000 : ℝ) (3200000583431/19447700000000 : ℝ) (591/500 : ℝ) (975109651/500000000 : ℝ) (487526833/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156282039/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10833/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2759/5000 : ℝ)
      else (2043/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5739/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (180692363579/12154812500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (12197/1600000 : ℝ) := by norm_num
  have pc0 : 1 < (18737729/20000000 : ℝ) ^ p + (993399667/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18737729/20000000 : ℝ)) (y := (993399667/1000000000 : ℝ)) (X := (16649122231641/100000000000000 : ℝ)) (Y := (10418862105877/12500000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993399667/1000000000 : ℝ) ^ p + (18737729/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (993399667/1000000000 : ℝ)) (y := (18737729/20000000 : ℝ)) (X := (10418862105877/12500000000000 : ℝ)) (Y := (16649122231641/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1930286117/1000000000 : ℝ)) (τ := (18737729/20000000 : ℝ)) (σ := (993399667/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (818187419/865069343 : ℝ) ^ p + (857446218/865069343 : ℝ) ^ p := by
    exact cert_lt (x := (818187419/865069343 : ℝ)) (y := (857446218/865069343 : ℝ)) (X := (21604866351269/100000000000000 : ℝ)) (Y := (78395134839907/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (18737729/20000000 : ℝ)) (n' := (865069343/1000000000 : ℝ)) (Ab := (818187419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940286607/1000000000 : ℝ) ^ p + (496318039/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (940286607/1000000000 : ℝ)) (y := (496318039/500000000 : ℝ)) (X := (3678636519641/20000000000000 : ℝ)) (Y := (1020085440991/1250000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496318039/500000000 : ℝ) ^ p + (940286607/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496318039/500000000 : ℝ)) (y := (940286607/1000000000 : ℝ)) (X := (1020085440991/1250000000000 : ℝ)) (Y := (3678636519641/20000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (386584537/200000000 : ℝ)) (τ := (940286607/1000000000 : ℝ)) (σ := (496318039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821767933/868981538 : ℝ) ^ p + (861358413/868981538 : ℝ) ^ p := by
    exact cert_lt (x := (821767933/868981538 : ℝ)) (y := (861358413/868981538 : ℝ)) (X := (21518530704329/100000000000000 : ℝ)) (Y := (78481470107819/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940286607/1000000000 : ℝ)) (n' := (434490769/500000000 : ℝ)) (Ab := (821767933/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (117548523/125000000 : ℝ) ^ p + (992611867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (117548523/125000000 : ℝ)) (y := (992611867/1000000000 : ℝ)) (X := (4611975661521/25000000000000 : ℝ)) (Y := (81552115850523/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992611867/1000000000 : ℝ) ^ p + (117548523/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992611867/1000000000 : ℝ)) (y := (117548523/125000000 : ℝ)) (X := (81552115850523/100000000000000 : ℝ)) (Y := (4611975661521/25000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1933000051/1000000000 : ℝ)) (τ := (117548523/125000000 : ℝ)) (σ := (992611867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (205468673/217274549 : ℝ) ^ p + (861475071/869098196 : ℝ) ^ p := by
    exact cert_lt (x := (205468673/217274549 : ℝ)) (y := (861475071/869098196 : ℝ)) (X := (5378991774679/25000000000000 : ℝ)) (Y := (78484034010159/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (117548523/125000000 : ℝ)) (n' := (217274549/250000000 : ℝ)) (Ab := (205468673/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (1175489/1250000 : ℝ) ^ p + (992611147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (1175489/1250000 : ℝ)) (y := (992611147/1000000000 : ℝ)) (X := (9224764888171/50000000000000 : ℝ)) (Y := (40775244557807/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992611147/1000000000 : ℝ) ^ p + (1175489/1250000 : ℝ) ^ p := by
    exact cert_lt (x := (992611147/1000000000 : ℝ)) (y := (1175489/1250000 : ℝ)) (X := (40775244557807/50000000000000 : ℝ)) (Y := (9224764888171/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1933002347/1000000000 : ℝ)) (τ := (1175489/1250000 : ℝ)) (σ := (992611147/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (410938931/434550830 : ℝ) ^ p + (172295707/173820332 : ℝ) ^ p := by
    exact cert_lt (x := (410938931/434550830 : ℝ)) (y := (172295707/173820332 : ℝ)) (X := (21515890945819/100000000000000 : ℝ)) (Y := (78484110132449/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (1175489/1250000 : ℝ)) (n' := (43455083/50000000 : ℝ)) (Ab := (410938931/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (94039129/100000000 : ℝ) ^ p + (7940889/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (94039129/100000000 : ℝ)) (y := (7940889/8000000 : ℝ)) (X := (3689915666683/20000000000000 : ℝ)) (Y := (81550439410317/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (7940889/8000000 : ℝ) ^ p + (94039129/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (7940889/8000000 : ℝ)) (y := (94039129/100000000 : ℝ)) (X := (81550439410317/100000000000000 : ℝ)) (Y := (3689915666683/20000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (386600483/200000000 : ℝ)) (τ := (94039129/100000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (821877956/869101763 : ℝ) ^ p + (861478638/869101763 : ℝ) ^ p := by
    exact cert_lt (x := (821877956/869101763 : ℝ)) (y := (861478638/869101763 : ℝ)) (X := (2689486061959/12500000000000 : ℝ)) (Y := (19621028098973/25000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (94039129/100000000 : ℝ)) (n' := (869101763/1000000000 : ℝ)) (Ab := (205469489/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (235097823/250000000 : ℝ) ^ p + (7940889/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (235097823/250000000 : ℝ)) (y := (7940889/8000000 : ℝ)) (X := (9224789706231/50000000000000 : ℝ)) (Y := (81550439410317/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (7940889/8000000 : ℝ) ^ p + (235097823/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (7940889/8000000 : ℝ)) (y := (235097823/250000000 : ℝ)) (X := (81550439410317/100000000000000 : ℝ)) (Y := (9224789706231/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (821877959/869101766 : ℝ) ^ p + (861478641/869101766 : ℝ) ^ p := by
    exact cert_lt (x := (821877959/869101766 : ℝ)) (y := (861478641/869101766 : ℝ)) (X := (860635544521/4000000000000 : ℝ)) (Y := (39242056230909/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1700201729/1843717961 : ℝ) ^ p + (1836094836/1843717961 : ℝ) ^ p := by
    exact cert_lt (x := (1700201729/1843717961 : ℝ)) (y := (1836094836/1843717961 : ℝ)) (X := (10768720193281/100000000000000 : ℝ)) (Y := (89231280126691/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083263727/1156282039 : ℝ) ^ p + (1148658914/1156282039 : ℝ) ^ p := by
    exact cert_lt (x := (1083263727/1156282039 : ℝ)) (y := (1148658914/1156282039 : ℝ)) (X := (2078962247517/12500000000000 : ℝ)) (Y := (41684151244079/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (7940889/8000000 : ℝ)) (U := (1156282039/1000000000 : ℝ)) (Ab := (1700201729/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ)) (Ab := (1083263727/1000000000 : ℝ))
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

theorem localize26_slab023 (p : ℝ) (hpa : (439/16 : ℝ) ≤ p) (hpb : p ≤ (55/2 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1156282039/1000000000 : ℝ)) ∧ coordinateBox (2759/5000 : ℝ) (10833/10000 : ℝ) (2043/2500 : ℝ) (5739/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (326560735956627/194477000000000 : ℝ) ≤ X j i + X k i) ∧
    (113486199416569/19447700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (487526833/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(439/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (487526833/500000000 : ℝ))
      (by norm_num) 16 439 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(439/16 : ℝ)) ≤ (975053667/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975053667/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 439 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(55/2 : ℝ)) ≤ (975109651/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975109651/1000000000 : ℝ))
      (by norm_num) (by norm_num) 2 55 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (180692363579/12154812500000 : ℝ) (12197/1600000 : ℝ) (3200000583431/19447700000000 : ℝ) (591/500 : ℝ) (975109651/500000000 : ℝ) (487526833/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (439/16 : ℝ)) (β := (55/2 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (180692363579/12154812500000 : ℝ)) (δ := (12197/1600000 : ℝ)) (h := (3200000583431/19447700000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (487526833/500000000 : ℝ)) (thia := (975053667/1000000000 : ℝ)) (thib := (975109651/1000000000 : ℝ))
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
  have hh := contract26_slab023 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 24, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab024 (p : ℝ) (hpa : (55/2 : ℝ) ≤ p) (hpb : p ≤ (441/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (4516007633/304562500000 : ℝ) (1900793/250000000 : ℝ) (80000014619/487300000000 : ℝ) (591/500 : ℝ) (195033077/100000000 : ℝ) (19502193/20000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578160757/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2167/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(69/125 : ℝ)
      else (327/400 : ℝ) ≤ X j i ∧ X j i ≤ (5739/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (4516007633/304562500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1900793/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (937036741/1000000000 : ℝ) ^ p + (993412089/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937036741/1000000000 : ℝ)) (y := (993412089/1000000000 : ℝ)) (X := (8327446243759/50000000000000 : ℝ)) (Y := (41672563158969/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993412089/1000000000 : ℝ) ^ p + (937036741/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993412089/1000000000 : ℝ)) (y := (937036741/1000000000 : ℝ)) (X := (41672563158969/50000000000000 : ℝ)) (Y := (8327446243759/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193044883/100000000 : ℝ)) (τ := (937036741/1000000000 : ℝ)) (σ := (993412089/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (818393467/865191870 : ℝ) ^ p + (428794349/432595935 : ℝ) ^ p := by
    exact cert_lt (x := (818393467/865191870 : ℝ)) (y := (428794349/432595935 : ℝ)) (X := (21595239204723/100000000000000 : ℝ)) (Y := (4900297596061/6250000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (937036741/1000000000 : ℝ)) (n' := (86519187/100000000 : ℝ)) (Ab := (818393467/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940431629/1000000000 : ℝ) ^ p + (992649447/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940431629/1000000000 : ℝ)) (y := (992649447/1000000000 : ℝ)) (X := (18400587787189/100000000000000 : ℝ)) (Y := (40799715553491/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992649447/1000000000 : ℝ) ^ p + (940431629/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992649447/1000000000 : ℝ)) (y := (940431629/1000000000 : ℝ)) (X := (40799715553491/50000000000000 : ℝ)) (Y := (18400587787189/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (483270269/250000000 : ℝ)) (τ := (940431629/1000000000 : ℝ)) (σ := (992649447/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821968283/869097118 : ℝ) ^ p + (430746973/434548559 : ℝ) ^ p := by
    exact cert_lt (x := (821968283/869097118 : ℝ)) (y := (430746973/434548559 : ℝ)) (X := (10754551527619/50000000000000 : ℝ)) (Y := (78490897977533/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940431629/1000000000 : ℝ)) (n' := (434548559/500000000 : ℝ)) (Ab := (821968283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (3762131/4000000 : ℝ) ^ p + (124078167/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (3762131/4000000 : ℝ)) (y := (124078167/125000000 : ℝ)) (X := (4613799842541/25000000000000 : ℝ)) (Y := (81544819499411/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124078167/125000000 : ℝ) ^ p + (3762131/4000000 : ℝ) ^ p := by
    exact cert_lt (x := (124078167/125000000 : ℝ)) (y := (3762131/4000000 : ℝ)) (X := (81544819499411/100000000000000 : ℝ)) (Y := (4613799842541/25000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (966579043/500000000 : ℝ)) (τ := (3762131/4000000 : ℝ)) (σ := (124078167/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822074559/869213227 : ℝ) ^ p + (861610055/869213227 : ℝ) ^ p := by
    exact cert_lt (x := (822074559/869213227 : ℝ)) (y := (861610055/869213227 : ℝ)) (X := (4301310536971/20000000000000 : ℝ)) (Y := (78493448486461/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (3762131/4000000 : ℝ)) (n' := (869213227/1000000000 : ℝ)) (Ab := (822074559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (188107149/200000000 : ℝ) ^ p + (49631231/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (188107149/200000000 : ℝ)) (y := (49631231/50000000 : ℝ)) (X := (1845681923441/10000000000000 : ℝ)) (Y := (81543198292343/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49631231/50000000 : ℝ) ^ p + (188107149/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (49631231/50000000 : ℝ)) (y := (188107149/200000000 : ℝ)) (X := (81543198292343/100000000000000 : ℝ)) (Y := (1845681923441/10000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (386632073/200000000 : ℝ)) (τ := (188107149/200000000 : ℝ)) (σ := (49631231/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822077706/869216665 : ℝ) ^ p + (861613493/869216665 : ℝ) ^ p := by
    exact cert_lt (x := (822077706/869216665 : ℝ)) (y := (861613493/869216665 : ℝ)) (X := (4301295459113/20000000000000 : ℝ)) (Y := (9811690499767/12500000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (188107149/200000000 : ℝ)) (n' := (173843333/200000000 : ℝ)) (Ab := (411038853/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (940535833/1000000000 : ℝ) ^ p + (992624599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940535833/1000000000 : ℝ)) (y := (992624599/1000000000 : ℝ)) (X := (9228433415913/50000000000000 : ℝ)) (Y := (81543150743443/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992624599/1000000000 : ℝ) ^ p + (940535833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992624599/1000000000 : ℝ)) (y := (940535833/1000000000 : ℝ)) (X := (81543150743443/100000000000000 : ℝ)) (Y := (9228433415913/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (120822527/62500000 : ℝ)) (τ := (940535833/1000000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (411038899/434608383 : ℝ) ^ p + (430806797/434608383 : ℝ) ^ p := by
    exact cert_lt (x := (411038899/434608383 : ℝ)) (y := (430806797/434608383 : ℝ)) (X := (2688309344441/12500000000000 : ℝ)) (Y := (3139741048659/4000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (940535833/1000000000 : ℝ)) (n' := (434608383/500000000 : ℝ)) (Ab := (411038899/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (188107167/200000000 : ℝ) ^ p + (992624599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188107167/200000000 : ℝ)) (y := (992624599/1000000000 : ℝ)) (X := (18456867913587/100000000000000 : ℝ)) (Y := (81543150743443/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992624599/1000000000 : ℝ) ^ p + (188107167/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992624599/1000000000 : ℝ)) (y := (188107167/200000000 : ℝ)) (X := (81543150743443/100000000000000 : ℝ)) (Y := (18456867913587/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (822077801/869216769 : ℝ) ^ p + (861613597/869216769 : ℝ) ^ p := by
    exact cert_lt (x := (822077801/869216769 : ℝ)) (y := (861613597/869216769 : ℝ)) (X := (21506474872841/100000000000000 : ℝ)) (Y := (39246763141183/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (130804483/141821422 : ℝ) ^ p + (918037657/921839243 : ℝ) ^ p := by
    exact cert_lt (x := (130804483/141821422 : ℝ)) (y := (918037657/921839243 : ℝ)) (X := (10765317859677/100000000000000 : ℝ)) (Y := (89234682356723/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083446851/1156321514 : ℝ) ^ p + (574359171/578160757 : ℝ) ^ p := by
    exact cert_lt (x := (1083446851/1156321514 : ℝ)) (y := (574359171/578160757 : ℝ)) (X := (519554056383/3125000000000 : ℝ)) (Y := (83374271038847/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992624599/1000000000 : ℝ)) (U := (578160757/500000000 : ℝ)) (Ab := (1700458279/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ)) (Ab := (1083446851/1000000000 : ℝ))
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

theorem localize26_slab024 (p : ℝ) (hpa : (55/2 : ℝ) ≤ p) (hpb : p ≤ (441/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (578160757/500000000 : ℝ)) ∧ coordinateBox (69/125 : ℝ) (2167/2000 : ℝ) (327/400 : ℝ) (5739/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (2046061303387/1218250000000 : ℝ) ≤ X j i + X k i) ∧
    (2843799985381/487300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (19502193/20000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(55/2 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (19502193/20000000 : ℝ))
      (by norm_num) 2 55 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(55/2 : ℝ)) ≤ (975109651/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975109651/1000000000 : ℝ))
      (by norm_num) (by norm_num) 2 55 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(441/16 : ℝ)) ≤ (195033077/200000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (195033077/200000000 : ℝ))
      (by norm_num) (by norm_num) 16 441 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (4516007633/304562500000 : ℝ) (1900793/250000000 : ℝ) (80000014619/487300000000 : ℝ) (591/500 : ℝ) (195033077/100000000 : ℝ) (19502193/20000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (55/2 : ℝ)) (β := (441/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (4516007633/304562500000 : ℝ)) (δ := (1900793/250000000 : ℝ)) (h := (80000014619/487300000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (19502193/20000000 : ℝ)) (thia := (975109651/1000000000 : ℝ)) (thib := (195033077/200000000 : ℝ))
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
  have hh := contract26_slab024 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 25, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab025 (p : ℝ) (hpa : (441/16 : ℝ) ≤ p) (hpb : p ≤ (221/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (144470825971/9768150000000 : ℝ) (1895831/250000000 : ℝ) (3200000586089/19536300000000 : ℝ) (591/500 : ℝ) (97522087/50000000 : ℝ) (121895673/125000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578180453/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10837/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2761/5000 : ℝ)
      else (8177/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11479/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (144470825971/9768150000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1895831/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (234296579/250000000 : ℝ) ^ p + (993424467/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (234296579/250000000 : ℝ)) (y := (993424467/1000000000 : ℝ)) (X := (16660635328527/100000000000000 : ℝ)) (Y := (16667876824613/20000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993424467/1000000000 : ℝ) ^ p + (234296579/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993424467/1000000000 : ℝ)) (y := (234296579/250000000 : ℝ)) (X := (16667876824613/20000000000000 : ℝ)) (Y := (16660635328527/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1930610783/1000000000 : ℝ)) (τ := (234296579/250000000 : ℝ)) (σ := (993424467/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (272866193/288437909 : ℝ) ^ p + (857730403/865313727 : ℝ) ^ p := by
    exact cert_lt (x := (272866193/288437909 : ℝ)) (y := (857730403/865313727 : ℝ)) (X := (5396416916981/25000000000000 : ℝ)) (Y := (19603583364603/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (234296579/250000000 : ℝ)) (n' := (865313727/1000000000 : ℝ)) (Ab := (818598579/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940575943/1000000000 : ℝ) ^ p + (992662771/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940575943/1000000000 : ℝ)) (y := (992662771/1000000000 : ℝ)) (X := (9203977972839/50000000000000 : ℝ)) (Y := (81592062379907/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992662771/1000000000 : ℝ) ^ p + (940575943/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992662771/1000000000 : ℝ)) (y := (940575943/1000000000 : ℝ)) (X := (81592062379907/100000000000000 : ℝ)) (Y := (9203977972839/50000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (966619357/500000000 : ℝ)) (τ := (940575943/1000000000 : ℝ)) (σ := (992662771/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822167705/869212044 : ℝ) ^ p + (215407180/217303011 : ℝ) ^ p := by
    exact cert_lt (x := (822167705/869212044 : ℝ)) (y := (215407180/217303011 : ℝ)) (X := (21499728956359/100000000000000 : ℝ)) (Y := (19625067962943/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940575943/1000000000 : ℝ)) (n' := (217303011/250000000 : ℝ)) (Ab := (164433541/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (94067661/100000000 : ℝ) ^ p + (24815969/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (94067661/100000000 : ℝ)) (y := (24815969/25000000 : ℝ)) (X := (4615614724217/25000000000000 : ℝ)) (Y := (81537559572823/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24815969/25000000 : ℝ) ^ p + (94067661/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (24815969/25000000 : ℝ)) (y := (94067661/100000000 : ℝ)) (X := (81537559572823/100000000000000 : ℝ)) (Y := (4615614724217/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (193331537/100000000 : ℝ)) (τ := (94067661/100000000 : ℝ)) (σ := (24815969/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (411136750/434663803 : ℝ) ^ p + (61553163/62094829 : ℝ) ^ p := by
    exact cert_lt (x := (411136750/434663803 : ℝ)) (y := (61553163/62094829 : ℝ)) (X := (5374298016819/25000000000000 : ℝ)) (Y := (39251404515757/50000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (94067661/100000000 : ℝ)) (n' := (434663803/500000000 : ℝ)) (Ab := (1644547/2000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (470339791/500000000 : ℝ) ^ p + (19852761/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (470339791/500000000 : ℝ)) (y := (19852761/20000000 : ℝ)) (X := (577002198539/3125000000000 : ℝ)) (Y := (16307189694207/20000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (19852761/20000000 : ℝ) ^ p + (470339791/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (19852761/20000000 : ℝ)) (y := (470339791/500000000 : ℝ)) (X := (16307189694207/20000000000000 : ℝ)) (Y := (577002198539/3125000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (3776011/1953125 : ℝ)) (τ := (470339791/500000000 : ℝ)) (σ := (19852761/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822276623/869331017 : ℝ) ^ p + (861747693/869331017 : ℝ) ^ p := by
    exact cert_lt (x := (822276623/869331017 : ℝ)) (y := (861747693/869331017 : ℝ)) (X := (171976939281/800000000000 : ℝ)) (Y := (19625720977861/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (470339791/500000000 : ℝ)) (n' := (869331017/1000000000 : ℝ)) (Ab := (822276623/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (94067967/100000000 : ℝ) ^ p + (992638029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94067967/100000000 : ℝ)) (y := (992638029/1000000000 : ℝ)) (X := (18464118070039/100000000000000 : ℝ)) (Y := (16307180163839/20000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992638029/1000000000 : ℝ) ^ p + (94067967/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992638029/1000000000 : ℝ)) (y := (94067967/100000000 : ℝ)) (X := (16307180163839/20000000000000 : ℝ)) (Y := (18464118070039/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1933317699/1000000000 : ℝ)) (τ := (94067967/100000000 : ℝ)) (σ := (992638029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (822276715/869331118 : ℝ) ^ p + (430873897/434665559 : ℝ) ^ p := by
    exact cert_lt (x := (822276715/869331118 : ℝ)) (y := (430873897/434665559 : ℝ)) (X := (5374278714609/25000000000000 : ℝ)) (Y := (78502886128637/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (94067967/100000000 : ℝ)) (n' := (434665559/500000000 : ℝ)) (Ab := (164455343/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (940679673/1000000000 : ℝ) ^ p + (248159507/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (940679673/1000000000 : ℝ)) (y := (248159507/250000000 : ℝ)) (X := (73856478787/400000000000 : ℝ)) (Y := (81535898550061/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248159507/250000000 : ℝ) ^ p + (940679673/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248159507/250000000 : ℝ)) (y := (940679673/1000000000 : ℝ)) (X := (81535898550061/100000000000000 : ℝ)) (Y := (73856478787/400000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (74752429/79030102 : ℝ) ^ p + (430873899/434665561 : ℝ) ^ p := by
    exact cert_lt (x := (74752429/79030102 : ℝ)) (y := (430873899/434665561 : ℝ)) (X := (21497115014801/100000000000000 : ℝ)) (Y := (78502886216447/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1700713723/1843639094 : ℝ) ^ p + (918027885/921819547 : ℝ) ^ p := by
    exact cert_lt (x := (1700713723/1843639094 : ℝ)) (y := (918027885/921819547 : ℝ)) (X := (10761935024339/100000000000000 : ℝ)) (Y := (11154758159611/12500000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083629333/1156360906 : ℝ) ^ p + (574388791/578180453 : ℝ) ^ p := by
    exact cert_lt (x := (1083629333/1156360906 : ℝ)) (y := (574388791/578180453 : ℝ)) (X := (8309896188101/50000000000000 : ℝ)) (Y := (8338020831289/10000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248159507/250000000 : ℝ)) (U := (578180453/500000000 : ℝ)) (Ab := (1700713723/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ)) (Ab := (1083629333/1000000000 : ℝ))
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

theorem localize26_slab025 (p : ℝ) (hpa : (441/16 : ℝ) ≤ p) (hpb : p ≤ (221/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (578180453/500000000 : ℝ)) ∧ coordinateBox (2761/5000 : ℝ) (10837/10000 : ℝ) (8177/10000 : ℝ) (11479/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (82044715591873/48840750000000 : ℝ) ≤ X j i + X k i) ∧
    (114017799413911/19536300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (121895673/125000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(441/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (121895673/125000000 : ℝ))
      (by norm_num) 16 441 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(441/16 : ℝ)) ≤ (195033077/200000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (195033077/200000000 : ℝ))
      (by norm_num) (by norm_num) 16 441 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(221/8 : ℝ)) ≤ (97522087/100000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (97522087/100000000 : ℝ))
      (by norm_num) (by norm_num) 8 221 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (144470825971/9768150000000 : ℝ) (1895831/250000000 : ℝ) (3200000586089/19536300000000 : ℝ) (591/500 : ℝ) (97522087/50000000 : ℝ) (121895673/125000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (441/16 : ℝ)) (β := (221/8 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (144470825971/9768150000000 : ℝ)) (δ := (1895831/250000000 : ℝ)) (h := (3200000586089/19536300000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (121895673/125000000 : ℝ)) (thia := (195033077/200000000 : ℝ)) (thib := (97522087/100000000 : ℝ))
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
  have hh := contract26_slab025 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 26, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab026 (p : ℝ) (hpa : (221/8 : ℝ) ≤ p) (hpb : p ≤ (443/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (5777183803/391612000000 : ℝ) (7563577/1000000000 : ℝ) (1600000293709/9790300000000 : ℝ) (591/500 : ℝ) (243819027/125000000 : ℝ) (975220869/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156400201/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10839/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(221/400 : ℝ)
      else (8179/10000 : ℝ) ≤ X j i ∧ X j i ≤ (287/250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (5777183803/391612000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7563577/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (937335183/1000000000 : ℝ) ^ p + (310449/312500 : ℝ) ^ p := by
    exact cert_lt (x := (937335183/1000000000 : ℝ)) (y := (310449/312500 : ℝ)) (X := (8333176184049/50000000000000 : ℝ)) (Y := (83333667243383/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (310449/312500 : ℝ) ^ p + (937335183/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (310449/312500 : ℝ)) (y := (937335183/1000000000 : ℝ)) (X := (83333667243383/100000000000000 : ℝ)) (Y := (8333176184049/50000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1930771983/1000000000 : ℝ)) (τ := (937335183/1000000000 : ℝ)) (σ := (310449/312500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (818802757/865434929 : ℝ) ^ p + (857871352/865434929 : ℝ) ^ p := by
    exact cert_lt (x := (818802757/865434929 : ℝ)) (y := (857871352/865434929 : ℝ)) (X := (21576141440719/100000000000000 : ℝ)) (Y := (39211929649007/50000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (937335183/1000000000 : ℝ)) (n' := (865434929/1000000000 : ℝ)) (Ab := (818802757/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (470359779/500000000 : ℝ) ^ p + (19853521/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (470359779/500000000 : ℝ)) (y := (19853521/20000000 : ℝ)) (X := (9207644702013/50000000000000 : ℝ)) (Y := (81584728396473/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (19853521/20000000 : ℝ) ^ p + (470359779/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (19853521/20000000 : ℝ)) (y := (470359779/500000000 : ℝ)) (X := (81584728396473/100000000000000 : ℝ)) (Y := (9207644702013/50000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (241674451/125000000 : ℝ)) (τ := (470359779/500000000 : ℝ)) (σ := (19853521/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822366205/869326332 : ℝ) ^ p + (123108965/124189476 : ℝ) ^ p := by
    exact cert_lt (x := (822366205/869326332 : ℝ)) (y := (123108965/124189476 : ℝ)) (X := (5372600093049/25000000000000 : ℝ)) (Y := (78509600412861/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (470359779/500000000 : ℝ)) (n' := (217331583/250000000 : ℝ)) (Ab := (164473241/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37632791/40000000 : ℝ) ^ p + (496326069/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (37632791/40000000 : ℝ)) (y := (496326069/500000000 : ℝ)) (X := (18469684657891/100000000000000 : ℝ)) (Y := (407651665477/500000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496326069/500000000 : ℝ) ^ p + (37632791/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496326069/500000000 : ℝ)) (y := (37632791/40000000 : ℝ)) (X := (407651665477/500000000000 : ℝ)) (Y := (18469684657891/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1933471913/1000000000 : ℝ)) (τ := (37632791/40000000 : ℝ)) (σ := (496326069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822471523/869441352 : ℝ) ^ p + (861877775/869441352 : ℝ) ^ p := by
    exact cert_lt (x := (822471523/869441352 : ℝ)) (y := (861877775/869441352 : ℝ)) (X := (268598457577/1250000000000 : ℝ)) (Y := (78512124392359/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37632791/40000000 : ℝ)) (n' := (108680169/125000000 : ℝ)) (Ab := (822471523/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (37632909/40000000 : ℝ) ^ p + (992651433/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (37632909/40000000 : ℝ)) (y := (992651433/1000000000 : ℝ)) (X := (2308911023433/12500000000000 : ℝ)) (Y := (509554561773/625000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992651433/1000000000 : ℝ) ^ p + (37632909/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (992651433/1000000000 : ℝ)) (y := (37632909/40000000 : ℝ)) (X := (509554561773/625000000000 : ℝ)) (Y := (2308911023433/12500000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966737079/500000000 : ℝ)) (τ := (37632909/40000000 : ℝ)) (σ := (992651433/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822474623/869444737 : ℝ) ^ p + (4245720/4282979 : ℝ) ^ p := by
    exact cert_lt (x := (822474623/869444737 : ℝ)) (y := (4245720/4282979 : ℝ)) (X := (10743901363969/50000000000000 : ℝ)) (Y := (78512198663297/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (37632909/40000000 : ℝ)) (n' := (869444737/1000000000 : ℝ)) (Ab := (822474623/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (235205703/250000000 : ℝ) ^ p + (248162853/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (235205703/250000000 : ℝ)) (y := (248162853/250000000 : ℝ)) (X := (3694267096007/20000000000000 : ℝ)) (Y := (81528682128903/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248162853/250000000 : ℝ) ^ p + (235205703/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248162853/250000000 : ℝ)) (y := (235205703/250000000 : ℝ)) (X := (81528682128903/100000000000000 : ℝ)) (Y := (3694267096007/20000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (120842139/62500000 : ℝ)) (τ := (235205703/250000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (822474714/869444837 : ℝ) ^ p + (861881260/869444837 : ℝ) ^ p := by
    exact cert_lt (x := (822474714/869444837 : ℝ)) (y := (861881260/869444837 : ℝ)) (X := (10743900062761/50000000000000 : ℝ)) (Y := (78512200857409/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (235205703/250000000 : ℝ)) (n' := (869444837/1000000000 : ℝ)) (Ab := (411237357/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470411407/500000000 : ℝ) ^ p + (248162853/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (470411407/500000000 : ℝ)) (y := (248162853/250000000 : ℝ)) (X := (18471336567221/100000000000000 : ℝ)) (Y := (81528682128903/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248162853/250000000 : ℝ) ^ p + (470411407/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248162853/250000000 : ℝ)) (y := (470411407/500000000 : ℝ)) (X := (81528682128903/100000000000000 : ℝ)) (Y := (18471336567221/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (822474716/869444839 : ℝ) ^ p + (861881262/869444839 : ℝ) ^ p := by
    exact cert_lt (x := (822474716/869444839 : ℝ)) (y := (861881262/869444839 : ℝ)) (X := (10743900101839/50000000000000 : ℝ)) (Y := (78512200901291/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1700968054/1843599799 : ℝ) ^ p + (1836036222/1843599799 : ℝ) ^ p := by
    exact cert_lt (x := (1700968054/1843599799 : ℝ)) (y := (1836036222/1843599799 : ℝ)) (X := (10758566822489/100000000000000 : ℝ)) (Y := (557758958683/625000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083811150/1156400201 : ℝ) ^ p + (39615056/39875869 : ℝ) ^ p := by
    exact cert_lt (x := (1083811150/1156400201 : ℝ)) (y := (39615056/39875869 : ℝ)) (X := (4153469975777/25000000000000 : ℝ)) (Y := (20846530184997/25000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248162853/250000000 : ℝ)) (U := (1156400201/1000000000 : ℝ)) (Ab := (850484027/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ)) (Ab := (21676223/20000000 : ℝ))
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

theorem localize26_slab026 (p : ℝ) (hpa : (221/8 : ℝ) ≤ p) (hpb : p ≤ (443/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1156400201/1000000000 : ℝ)) ∧ coordinateBox (221/400 : ℝ) (10839/10000 : ℝ) (8179/10000 : ℝ) (287/250 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (164493950142467/97903000000000 : ℝ) ≤ X j i + X k i) ∧
    (57141799706291/9790300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (975220869/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(221/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (975220869/1000000000 : ℝ))
      (by norm_num) 8 221 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(221/8 : ℝ)) ≤ (97522087/100000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (97522087/100000000 : ℝ))
      (by norm_num) (by norm_num) 8 221 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(443/16 : ℝ)) ≤ (243819027/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (243819027/250000000 : ℝ))
      (by norm_num) (by norm_num) 16 443 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (5777183803/391612000000 : ℝ) (7563577/1000000000 : ℝ) (1600000293709/9790300000000 : ℝ) (591/500 : ℝ) (243819027/125000000 : ℝ) (975220869/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (221/8 : ℝ)) (β := (443/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (5777183803/391612000000 : ℝ)) (δ := (7563577/1000000000 : ℝ)) (h := (1600000293709/9790300000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (975220869/1000000000 : ℝ)) (thia := (97522087/100000000 : ℝ)) (thib := (243819027/250000000 : ℝ))
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
  have hh := contract26_slab026 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 27, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab027 (p : ℝ) (hpa : (443/16 : ℝ) ≤ p) (hpb : p ≤ (111/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1443885700411/98124500000000 : ℝ) (7543933/1000000000 : ℝ) (3200000588747/19624900000000 : ℝ) (591/500 : ℝ) (9753311/5000000 : ℝ) (975276107/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (115643941/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(271/250 : ℝ) ≤ X j i ∧ X j i ≤ -(5527/10000 : ℝ)
      else (4091/5000 : ℝ) ≤ X j i ∧ X j i ≤ (287/250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1443885700411/98124500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7543933/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (937483347/1000000000 : ℝ) ^ p + (7761321/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (937483347/1000000000 : ℝ)) (y := (7761321/7812500 : ℝ)) (X := (4168010943813/25000000000000 : ℝ)) (Y := (10415996870937/12500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (7761321/7812500 : ℝ) ^ p + (937483347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7761321/7812500 : ℝ)) (y := (937483347/1000000000 : ℝ)) (X := (10415996870937/12500000000000 : ℝ)) (Y := (4168010943813/25000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (386186487/200000000 : ℝ)) (τ := (937483347/1000000000 : ℝ)) (σ := (7761321/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819006013/865555475 : ℝ) ^ p + (858011542/865555475 : ℝ) ^ p := by
    exact cert_lt (x := (819006013/865555475 : ℝ)) (y := (858011542/865555475 : ℝ)) (X := (21566668537009/100000000000000 : ℝ)) (Y := (78433332264619/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (937483347/1000000000 : ℝ)) (n' := (34622219/40000000 : ℝ)) (Ab := (819006013/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940862477/1000000000 : ℝ) ^ p + (198537857/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (940862477/1000000000 : ℝ)) (y := (198537857/200000000 : ℝ)) (X := (4605646819539/25000000000000 : ℝ)) (Y := (10197178841983/12500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198537857/200000000 : ℝ) ^ p + (940862477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198537857/200000000 : ℝ)) (y := (940862477/1000000000 : ℝ)) (X := (10197178841983/12500000000000 : ℝ)) (Y := (4605646819539/25000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (966775881/500000000 : ℝ)) (τ := (940862477/1000000000 : ℝ)) (σ := (198537857/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822563793/869439980 : ℝ) ^ p + (861896047/869439980 : ℝ) ^ p := by
    exact cert_lt (x := (822563793/869439980 : ℝ)) (y := (861896047/869439980 : ℝ)) (X := (21481124464409/100000000000000 : ℝ)) (Y := (78518876869033/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940862477/1000000000 : ℝ)) (n' := (43471999/50000000 : ℝ)) (Ab := (822563793/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (188192449/200000000 : ℝ) ^ p + (7755199/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (188192449/200000000 : ℝ)) (y := (7755199/7812500 : ℝ)) (X := (18476874147661/100000000000000 : ℝ)) (Y := (254759824717/312500000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (7755199/7812500 : ℝ) ^ p + (188192449/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (7755199/7812500 : ℝ)) (y := (188192449/200000000 : ℝ)) (X := (254759824717/312500000000 : ℝ)) (Y := (18476874147661/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1933627717/1000000000 : ℝ)) (τ := (188192449/200000000 : ℝ)) (σ := (7755199/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822668634/869554459 : ℝ) ^ p + (862010526/869554459 : ℝ) ^ p := by
    exact cert_lt (x := (822668634/869554459 : ℝ)) (y := (862010526/869554459 : ℝ)) (X := (5369653325339/25000000000000 : ℝ)) (Y := (9815173461241/12500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (188192449/200000000 : ℝ)) (n' := (869554459/1000000000 : ℝ)) (Ab := (411334317/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (940965173/1000000000 : ℝ) ^ p + (248166193/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (940965173/1000000000 : ℝ)) (y := (248166193/250000000 : ℝ)) (X := (18478469690383/100000000000000 : ℝ)) (Y := (81521548636733/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248166193/250000000 : ℝ) ^ p + (940965173/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248166193/250000000 : ℝ)) (y := (940965173/1000000000 : ℝ)) (X := (81521548636733/100000000000000 : ℝ)) (Y := (18478469690383/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (386725989/200000000 : ℝ)) (τ := (940965173/1000000000 : ℝ)) (σ := (248166193/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (411335855/434778909 : ℝ) ^ p + (862013885/869557818 : ℝ) ^ p := by
    exact cert_lt (x := (411335855/434778909 : ℝ)) (y := (862013885/869557818 : ℝ)) (X := (21478539485187/100000000000000 : ℝ)) (Y := (1963036533817/2500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (940965173/1000000000 : ℝ)) (n' := (434778909/500000000 : ℝ)) (Ab := (82267171/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (47048263/50000000 : ℝ) ^ p + (992664751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (47048263/50000000 : ℝ)) (y := (992664751/1000000000 : ℝ)) (X := (18478517100959/100000000000000 : ℝ)) (Y := (81521500779017/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992664751/1000000000 : ℝ) ^ p + (47048263/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992664751/1000000000 : ℝ)) (y := (47048263/50000000 : ℝ)) (X := (81521500779017/100000000000000 : ℝ)) (Y := (18478517100959/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1933630011/1000000000 : ℝ)) (τ := (47048263/50000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (411335901/434778959 : ℝ) ^ p + (862013985/869557918 : ℝ) ^ p := by
    exact cert_lt (x := (411335901/434778959 : ℝ)) (y := (862013985/869557918 : ℝ)) (X := (21478537595641/100000000000000 : ℝ)) (Y := (78521463545669/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (47048263/50000000 : ℝ)) (n' := (434778959/500000000 : ℝ)) (Ab := (411335901/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470482631/500000000 : ℝ) ^ p + (992664751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470482631/500000000 : ℝ)) (y := (992664751/1000000000 : ℝ)) (X := (18478518190859/100000000000000 : ℝ)) (Y := (81521500779017/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992664751/1000000000 : ℝ) ^ p + (470482631/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992664751/1000000000 : ℝ)) (y := (470482631/500000000 : ℝ)) (X := (81521500779017/100000000000000 : ℝ)) (Y := (18478518190859/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (822671805/869557921 : ℝ) ^ p + (862013988/869557921 : ℝ) ^ p := by
    exact cert_lt (x := (822671805/869557921 : ℝ)) (y := (862013988/869557921 : ℝ)) (X := (5369634428209/25000000000000 : ℝ)) (Y := (78521463611459/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1701221293/1843560590 : ℝ) ^ p + (1836016657/1843560590 : ℝ) ^ p := by
    exact cert_lt (x := (1701221293/1843560590 : ℝ)) (y := (1836016657/1843560590 : ℝ)) (X := (10755217324443/100000000000000 : ℝ)) (Y := (89244783014169/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (541996164/578219705 : ℝ) ^ p + (1148895477/1156439410 : ℝ) ^ p := by
    exact cert_lt (x := (541996164/578219705 : ℝ)) (y := (1148895477/1156439410 : ℝ)) (X := (16607997438809/100000000000000 : ℝ)) (Y := (20848000766583/25000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992664751/1000000000 : ℝ)) (U := (115643941/100000000 : ℝ)) (Ab := (1701221293/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ)) (Ab := (135499041/125000000 : ℝ))
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

theorem localize26_slab027 (p : ℝ) (hpa : (443/16 : ℝ) ≤ p) (hpb : p ≤ (111/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (115643941/100000000 : ℝ)) ∧ coordinateBox (5527/10000 : ℝ) (271/250 : ℝ) (4091/5000 : ℝ) (287/250 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (16489846013221/9812450000000 : ℝ) ≤ X j i + X k i) ∧
    (114549399411253/19624900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (975276107/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(443/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (975276107/1000000000 : ℝ))
      (by norm_num) 16 443 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(443/16 : ℝ)) ≤ (243819027/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (243819027/250000000 : ℝ))
      (by norm_num) (by norm_num) 16 443 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(111/4 : ℝ)) ≤ (9753311/10000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (9753311/10000000 : ℝ))
      (by norm_num) (by norm_num) 4 111 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (1443885700411/98124500000000 : ℝ) (7543933/1000000000 : ℝ) (3200000588747/19624900000000 : ℝ) (591/500 : ℝ) (9753311/5000000 : ℝ) (975276107/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (443/16 : ℝ)) (β := (111/4 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1443885700411/98124500000000 : ℝ)) (δ := (7543933/1000000000 : ℝ)) (h := (3200000588747/19624900000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (975276107/1000000000 : ℝ)) (thia := (243819027/250000000 : ℝ)) (thib := (9753311/10000000 : ℝ))
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
  have hh := contract26_slab027 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 28, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab028 (p : ℝ) (hpa : (111/4 : ℝ) ≤ p) (hpb : p ≤ (445/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (72173855699/4917300000000 : ℝ) (1881097/250000000 : ℝ) (800000147519/4917300000000 : ℝ) (591/500 : ℝ) (975385847/500000000 : ℝ) (975331099/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578239259/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5421/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5529/10000 : ℝ)
      else (1023/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11481/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (72173855699/4917300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1881097/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (187526163/200000000 : ℝ) ^ p + (248365333/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (187526163/200000000 : ℝ)) (y := (248365333/250000000 : ℝ)) (X := (416942768253/2500000000000 : ℝ)) (Y := (41661154458449/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248365333/250000000 : ℝ) ^ p + (187526163/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248365333/250000000 : ℝ)) (y := (187526163/200000000 : ℝ)) (X := (41661154458449/50000000000000 : ℝ)) (Y := (416942768253/2500000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1931092147/1000000000 : ℝ)) (τ := (187526163/200000000 : ℝ)) (σ := (248365333/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819208350/865675379 : ℝ) ^ p + (858150991/865675379 : ℝ) ^ p := by
    exact cert_lt (x := (819208350/865675379 : ℝ)) (y := (858150991/865675379 : ℝ)) (X := (21557240058491/100000000000000 : ℝ)) (Y := (78442761107661/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187526163/200000000 : ℝ)) (n' := (865675379/1000000000 : ℝ)) (Ab := (16384167/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (941004709/1000000000 : ℝ) ^ p + (39708099/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (941004709/1000000000 : ℝ)) (y := (39708099/40000000 : ℝ)) (X := (18429851965509/100000000000000 : ℝ)) (Y := (40785083213243/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (39708099/40000000 : ℝ) ^ p + (941004709/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39708099/40000000 : ℝ)) (y := (941004709/1000000000 : ℝ)) (X := (40785083213243/50000000000000 : ℝ)) (Y := (18429851965509/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (120856699/62500000 : ℝ)) (τ := (941004709/1000000000 : ℝ)) (σ := (39708099/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822760471/869553003 : ℝ) ^ p + (862028615/869553003 : ℝ) ^ p := by
    exact cert_lt (x := (822760471/869553003 : ℝ)) (y := (862028615/869553003 : ℝ)) (X := (21471890971911/100000000000000 : ℝ)) (Y := (7852810995831/10000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (941004709/1000000000 : ℝ)) (n' := (869553003/1000000000 : ℝ)) (Ab := (822760471/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (29409501/31250000 : ℝ) ^ p + (24816969/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (29409501/31250000 : ℝ)) (y := (24816969/25000000 : ℝ)) (X := (4621007853183/25000000000000 : ℝ)) (Y := (5094749172577/6250000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24816969/25000000 : ℝ) ^ p + (29409501/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (24816969/25000000 : ℝ)) (y := (29409501/31250000 : ℝ)) (X := (5094749172577/6250000000000 : ℝ)) (Y := (4621007853183/25000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (241722849/125000000 : ℝ)) (τ := (29409501/31250000 : ℝ)) (σ := (24816969/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822864841/869666946 : ℝ) ^ p + (431071279/434833473 : ℝ) ^ p := by
    exact cert_lt (x := (822864841/869666946 : ℝ)) (y := (431071279/434833473 : ℝ)) (X := (858775739929/4000000000000 : ℝ)) (Y := (15706121549771/20000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (29409501/31250000 : ℝ)) (n' := (434833473/500000000 : ℝ)) (Ab := (822864841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (941106939/1000000000 : ℝ) ^ p + (198535613/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (941106939/1000000000 : ℝ)) (y := (198535613/200000000 : ℝ)) (X := (9242809727593/50000000000000 : ℝ)) (Y := (81514399476579/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198535613/200000000 : ℝ) ^ p + (941106939/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198535613/200000000 : ℝ)) (y := (941106939/1000000000 : ℝ)) (X := (81514399476579/100000000000000 : ℝ)) (Y := (9242809727593/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (483446251/250000000 : ℝ)) (τ := (941106939/1000000000 : ℝ)) (σ := (198535613/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822867896/869670281 : ℝ) ^ p + (862145893/869670281 : ℝ) ^ p := by
    exact cert_lt (x := (822867896/869670281 : ℝ)) (y := (862145893/869670281 : ℝ)) (X := (21469320553259/100000000000000 : ℝ)) (Y := (2454083776501/3125000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (941106939/1000000000 : ℝ)) (n' := (869670281/1000000000 : ℝ)) (Ab := (102858487/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (58819189/62500000 : ℝ) ^ p + (248169511/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (58819189/62500000 : ℝ)) (y := (248169511/250000000 : ℝ)) (X := (3697133178231/20000000000000 : ℝ)) (Y := (20378587878981/25000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248169511/250000000 : ℝ) ^ p + (58819189/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248169511/250000000 : ℝ)) (y := (58819189/62500000 : ℝ)) (X := (20378587878981/25000000000000 : ℝ)) (Y := (3697133178231/20000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (483446267/250000000 : ℝ)) (τ := (58819189/62500000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (822867985/869670379 : ℝ) ^ p + (862145991/869670379 : ℝ) ^ p := by
    exact cert_lt (x := (822867985/869670379 : ℝ)) (y := (862145991/869670379 : ℝ)) (X := (858772713979/4000000000000 : ℝ)) (Y := (78530682996067/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (58819189/62500000 : ℝ)) (n' := (869670379/1000000000 : ℝ)) (Ab := (164573597/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470553513/500000000 : ℝ) ^ p + (248169511/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (470553513/500000000 : ℝ)) (y := (248169511/250000000 : ℝ)) (X := (2310708372971/12500000000000 : ℝ)) (Y := (20378587878981/25000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248169511/250000000 : ℝ) ^ p + (470553513/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248169511/250000000 : ℝ)) (y := (470553513/500000000 : ℝ)) (X := (20378587878981/25000000000000 : ℝ)) (Y := (2310708372971/12500000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (274289329/289890127 : ℝ) ^ p + (862145993/869670381 : ℝ) ^ p := by
    exact cert_lt (x := (274289329/289890127 : ℝ)) (y := (862145993/869670381 : ℝ)) (X := (10734658963789/50000000000000 : ℝ)) (Y := (2454083844997/3125000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (154679403/167592862 : ℝ) ^ p + (917998547/921760741 : ℝ) ^ p := by
    exact cert_lt (x := (154679403/167592862 : ℝ)) (y := (917998547/921760741 : ℝ)) (X := (2150376300913/20000000000000 : ℝ)) (Y := (44624059351087/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (542086421/578239259 : ℝ) ^ p + (574477065/578239259 : ℝ) ^ p := by
    exact cert_lt (x := (542086421/578239259 : ℝ)) (y := (574477065/578239259 : ℝ)) (X := (16602138744271/100000000000000 : ℝ)) (Y := (3335914470897/4000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248169511/250000000 : ℝ)) (U := (578239259/500000000 : ℝ)) (Ab := (1701473433/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ)) (Ab := (542086421/500000000 : ℝ))
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

theorem localize26_slab028 (p : ℝ) (hpa : (111/4 : ℝ) ≤ p) (hpb : p ≤ (445/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (578239259/500000000 : ℝ)) ∧ coordinateBox (5529/10000 : ℝ) (5421/5000 : ℝ) (1023/1250 : ℝ) (11481/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (1291429395979/768328125000 : ℝ) ≤ X j i + X k i) ∧
    (28703799852481/4917300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (975331099/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(111/4 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (975331099/1000000000 : ℝ))
      (by norm_num) 4 111 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(111/4 : ℝ)) ≤ (9753311/10000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (9753311/10000000 : ℝ))
      (by norm_num) (by norm_num) 4 111 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(445/16 : ℝ)) ≤ (975385847/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975385847/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 445 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (72173855699/4917300000000 : ℝ) (1881097/250000000 : ℝ) (800000147519/4917300000000 : ℝ) (591/500 : ℝ) (975385847/500000000 : ℝ) (975331099/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (111/4 : ℝ)) (β := (445/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (72173855699/4917300000000 : ℝ)) (δ := (1881097/250000000 : ℝ)) (h := (800000147519/4917300000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (975331099/1000000000 : ℝ)) (thia := (9753311/10000000 : ℝ)) (thib := (975385847/1000000000 : ℝ))
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
  have hh := contract26_slab028 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 29, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab029 (p : ℝ) (hpa : (445/16 : ℝ) ≤ p) (hpb : p ≤ (223/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (72153490103/4928375000000 : ℝ) (7504939/1000000000 : ℝ) (640000118281/3942700000000 : ℝ) (591/500 : ℝ) (975440353/500000000 : ℝ) (487692923/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156517517/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2711/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(5531/10000 : ℝ)
      else (4093/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11481/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (72153490103/4928375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7504939/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (586111/625000 : ℝ) ^ p + (993473529/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (586111/625000 : ℝ)) (y := (993473529/1000000000 : ℝ)) (X := (16683357419603/100000000000000 : ℝ)) (Y := (833166613827/1000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993473529/1000000000 : ℝ) ^ p + (586111/625000 : ℝ) ^ p := by
    exact cert_lt (x := (993473529/1000000000 : ℝ)) (y := (586111/625000 : ℝ)) (X := (833166613827/1000000000000 : ℝ)) (Y := (16683357419603/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1931251129/1000000000 : ℝ)) (τ := (586111/625000 : ℝ)) (σ := (993473529/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819409777/865794659 : ℝ) ^ p + (858289720/865794659 : ℝ) ^ p := by
    exact cert_lt (x := (819409777/865794659 : ℝ)) (y := (858289720/865794659 : ℝ)) (X := (21547848682849/100000000000000 : ℝ)) (Y := (78452152206097/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (586111/625000 : ℝ)) (n' := (865794659/1000000000 : ℝ)) (Ab := (819409777/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (117643283/125000000 : ℝ) ^ p + (992715619/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (117643283/125000000 : ℝ)) (y := (992715619/1000000000 : ℝ)) (X := (18437086455397/100000000000000 : ℝ)) (Y := (20390733119363/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992715619/1000000000 : ℝ) ^ p + (117643283/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992715619/1000000000 : ℝ)) (y := (117643283/125000000 : ℝ)) (X := (20390733119363/25000000000000 : ℝ)) (Y := (18437086455397/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1933861883/1000000000 : ℝ)) (τ := (117643283/125000000 : ℝ)) (σ := (992715619/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822956250/869665417 : ℝ) ^ p + (862160478/869665417 : ℝ) ^ p := by
    exact cert_lt (x := (822956250/869665417 : ℝ)) (y := (862160478/869665417 : ℝ)) (X := (21462695432021/100000000000000 : ℝ)) (Y := (9817163248797/12500000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (117643283/125000000 : ℝ)) (n' := (869665417/1000000000 : ℝ)) (Ab := (131673/160000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (188249029/200000000 : ℝ) ^ p + (992692001/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188249029/200000000 : ℝ)) (y := (992692001/1000000000 : ℝ)) (X := (9245579459483/50000000000000 : ℝ)) (Y := (2547151832717/3125000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992692001/1000000000 : ℝ) ^ p + (188249029/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992692001/1000000000 : ℝ)) (y := (188249029/200000000 : ℝ)) (X := (2547151832717/3125000000000 : ℝ)) (Y := (9245579459483/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (966968573/500000000 : ℝ)) (τ := (188249029/200000000 : ℝ)) (σ := (992692001/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823060151/869778828 : ℝ) ^ p + (862273889/869778828 : ℝ) ^ p := by
    exact cert_lt (x := (823060151/869778828 : ℝ)) (y := (862273889/869778828 : ℝ)) (X := (10730105259421/50000000000000 : ℝ)) (Y := (3141591634239/4000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (188249029/200000000 : ℝ)) (n' := (217444707/250000000 : ℝ)) (Ab := (823060151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (94124803/100000000 : ℝ) ^ p + (992691311/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94124803/100000000 : ℝ)) (y := (992691311/1000000000 : ℝ)) (X := (4623184714167/25000000000000 : ℝ)) (Y := (40753639699719/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992691311/1000000000 : ℝ) ^ p + (94124803/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992691311/1000000000 : ℝ)) (y := (94124803/100000000 : ℝ)) (X := (40753639699719/50000000000000 : ℝ)) (Y := (4623184714167/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1933939341/1000000000 : ℝ)) (τ := (94124803/100000000 : ℝ)) (σ := (992691311/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (274354394/289927379 : ℝ) ^ p + (862277198/869782137 : ℝ) ^ p := by
    exact cert_lt (x := (274354394/289927379 : ℝ)) (y := (862277198/869782137 : ℝ)) (X := (536503441197/2500000000000 : ℝ)) (Y := (39269931674233/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (94124803/100000000 : ℝ)) (n' := (869782137/1000000000 : ℝ)) (Ab := (411531591/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (470624057/500000000 : ℝ) ^ p + (992691291/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470624057/500000000 : ℝ)) (y := (992691291/1000000000 : ℝ)) (X := (18492784860271/100000000000000 : ℝ)) (Y := (20376808406147/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992691291/1000000000 : ℝ) ^ p + (470624057/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992691291/1000000000 : ℝ)) (y := (470624057/500000000 : ℝ)) (X := (20376808406147/25000000000000 : ℝ)) (Y := (18492784860271/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (386787881/200000000 : ℝ)) (τ := (470624057/500000000 : ℝ)) (σ := (992691291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (823063270/869782233 : ℝ) ^ p + (862277294/869782233 : ℝ) ^ p := by
    exact cert_lt (x := (823063270/869782233 : ℝ)) (y := (862277294/869782233 : ℝ)) (X := (10730067790609/50000000000000 : ℝ)) (Y := (19634966362899/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (470624057/500000000 : ℝ)) (n' := (869782233/1000000000 : ℝ)) (Ab := (82306327/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (941248117/1000000000 : ℝ) ^ p + (99269129/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (941248117/1000000000 : ℝ)) (y := (99269129/100000000 : ℝ)) (X := (9246393251629/50000000000000 : ℝ)) (Y := (40753615667923/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99269129/100000000 : ℝ) ^ p + (941248117/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99269129/100000000 : ℝ)) (y := (941248117/1000000000 : ℝ)) (X := (40753615667923/50000000000000 : ℝ)) (Y := (9246393251629/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (823063274/869782237 : ℝ) ^ p + (50722194/51163661 : ℝ) ^ p := by
    exact cert_lt (x := (823063274/869782237 : ℝ)) (y := (50722194/51163661 : ℝ)) (X := (10730067868687/50000000000000 : ℝ)) (Y := (39269932769613/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1701724474/1843482483 : ℝ) ^ p + (1835977544/1843482483 : ℝ) ^ p := by
    exact cert_lt (x := (1701724474/1843482483 : ℝ)) (y := (1835977544/1843482483 : ℝ)) (X := (5374278340809/50000000000000 : ℝ)) (Y := (89251443659597/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1084352677/1156517517 : ℝ) ^ p + (1149012578/1156517517 : ℝ) ^ p := by
    exact cert_lt (x := (1084352677/1156517517 : ℝ)) (y := (1149012578/1156517517 : ℝ)) (X := (16596299020673/100000000000000 : ℝ)) (Y := (16680740296129/20000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99269129/100000000 : ℝ)) (U := (1156517517/1000000000 : ℝ)) (Ab := (850862237/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ)) (Ab := (1084352677/1000000000 : ℝ))
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

theorem localize26_slab029 (p : ℝ) (hpa : (445/16 : ℝ) ≤ p) (hpb : p ≤ (223/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1156517517/1000000000 : ℝ)) ∧ coordinateBox (5531/10000 : ℝ) (2711/2500 : ℝ) (4093/5000 : ℝ) (11481/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (66282983462971/39427000000000 : ℝ) ≤ X j i + X k i) ∧
    (23016199881719/3942700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (487692923/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(445/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (487692923/500000000 : ℝ))
      (by norm_num) 16 445 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(445/16 : ℝ)) ≤ (975385847/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975385847/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 445 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(223/8 : ℝ)) ≤ (975440353/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975440353/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 223 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (72153490103/4928375000000 : ℝ) (7504939/1000000000 : ℝ) (640000118281/3942700000000 : ℝ) (591/500 : ℝ) (975440353/500000000 : ℝ) (487692923/500000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (445/16 : ℝ)) (β := (223/8 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (72153490103/4928375000000 : ℝ)) (δ := (7504939/1000000000 : ℝ)) (h := (640000118281/3942700000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (487692923/500000000 : ℝ)) (thia := (975385847/1000000000 : ℝ)) (thib := (975440353/1000000000 : ℝ))
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
  have hh := contract26_slab029 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 30, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab030 (p : ℝ) (hpa : (223/8 : ℝ) ≤ p) (hpb : p ≤ (447/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (360666289693/24697250000000 : ℝ) (3742797/500000000 : ℝ) (1600000296367/9878900000000 : ℝ) (591/500 : ℝ) (975494617/500000000 : ℝ) (30482511/31250000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231311289/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5423/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5533/10000 : ℝ)
      else (8189/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5741/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (360666289693/24697250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3742797/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (187584737/200000000 : ℝ) ^ p + (198697137/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (187584737/200000000 : ℝ)) (y := (198697137/200000000 : ℝ)) (X := (16688973177613/100000000000000 : ℝ)) (Y := (83311045680461/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198697137/200000000 : ℝ) ^ p + (187584737/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198697137/200000000 : ℝ)) (y := (187584737/200000000 : ℝ)) (X := (83311045680461/100000000000000 : ℝ)) (Y := (16688973177613/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193140937/100000000 : ℝ)) (τ := (187584737/200000000 : ℝ)) (σ := (198697137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (163922059/173182656 : ℝ) ^ p + (143071281/144318880 : ℝ) ^ p := by
    exact cert_lt (x := (163922059/173182656 : ℝ)) (y := (143071281/144318880 : ℝ)) (X := (6730786877/31250000000 : ℝ)) (Y := (78461482746639/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187584737/200000000 : ℝ)) (n' := (2705979/3125000 : ℝ)) (Ab := (163922059/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (94128713/100000000 : ℝ) ^ p + (992728721/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94128713/100000000 : ℝ)) (y := (992728721/1000000000 : ℝ)) (X := (18444281744971/100000000000000 : ℝ)) (Y := (81555737354331/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992728721/1000000000 : ℝ) ^ p + (94128713/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992728721/1000000000 : ℝ)) (y := (94128713/100000000 : ℝ)) (X := (81555737354331/100000000000000 : ℝ)) (Y := (18444281744971/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1934015851/1000000000 : ℝ)) (τ := (94128713/100000000 : ℝ)) (σ := (992728721/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (823151131/869777190 : ℝ) ^ p + (143715266/144962865 : ℝ) ^ p := by
    exact cert_lt (x := (823151131/869777190 : ℝ)) (y := (143715266/144962865 : ℝ)) (X := (2145355915741/10000000000000 : ℝ)) (Y := (78546442296967/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (94128713/100000000 : ℝ)) (n' := (86977719/100000000 : ℝ)) (Ab := (823151131/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (94138557/100000000 : ℝ) ^ p + (992705201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94138557/100000000 : ℝ)) (y := (992705201/1000000000 : ℝ)) (X := (18498246551767/100000000000000 : ℝ)) (Y := (81501772599261/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992705201/1000000000 : ℝ) ^ p + (94138557/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992705201/1000000000 : ℝ)) (y := (94138557/100000000 : ℝ)) (X := (81501772599261/100000000000000 : ℝ)) (Y := (18498246551767/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1934090771/1000000000 : ℝ)) (τ := (94138557/100000000 : ℝ)) (σ := (992705201/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823254565/869890071 : ℝ) ^ p + (287468159/289963357 : ℝ) ^ p := by
    exact cert_lt (x := (823254565/869890071 : ℝ)) (y := (287468159/289963357 : ℝ)) (X := (21451087041291/100000000000000 : ℝ)) (Y := (39274457150679/50000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (94138557/100000000 : ℝ)) (n' := (869890071/1000000000 : ℝ)) (Ab := (164650913/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (188277687/200000000 : ℝ) ^ p + (198540903/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (188277687/200000000 : ℝ)) (y := (198540903/200000000 : ℝ)) (X := (1849981942237/10000000000000 : ℝ)) (Y := (815001991441/1000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198540903/200000000 : ℝ) ^ p + (188277687/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198540903/200000000 : ℝ)) (y := (188277687/200000000 : ℝ)) (X := (815001991441/1000000000000 : ℝ)) (Y := (1849981942237/10000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (38681859/20000000 : ℝ)) (τ := (188277687/200000000 : ℝ)) (σ := (198540903/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (823257575/869893356 : ℝ) ^ p + (143734627/144982226 : ℝ) ^ p := by
    exact cert_lt (x := (823257575/869893356 : ℝ)) (y := (143734627/144982226 : ℝ)) (X := (21451015055599/100000000000000 : ℝ)) (Y := (7854898623177/10000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (188277687/200000000 : ℝ)) (n' := (217473339/250000000 : ℝ)) (Ab := (32930303/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (941388519/1000000000 : ℝ) ^ p + (198540899/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (941388519/1000000000 : ℝ)) (y := (198540899/200000000 : ℝ)) (X := (18499865539893/100000000000000 : ℝ)) (Y := (81500153271211/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198540899/200000000 : ℝ) ^ p + (941388519/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198540899/200000000 : ℝ)) (y := (941388519/1000000000 : ℝ)) (X := (81500153271211/100000000000000 : ℝ)) (Y := (18499865539893/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (967046507/500000000 : ℝ)) (τ := (941388519/1000000000 : ℝ)) (σ := (198540899/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (274419221/289964484 : ℝ) ^ p + (143734643/144982242 : ℝ) ^ p := by
    exact cert_lt (x := (274419221/289964484 : ℝ)) (y := (143734643/144982242 : ℝ)) (X := (21451012978511/100000000000000 : ℝ)) (Y := (78548988333839/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (941388519/1000000000 : ℝ)) (n' := (217473363/250000000 : ℝ)) (Ab := (823257663/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (941388521/1000000000 : ℝ) ^ p + (496352247/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (941388521/1000000000 : ℝ)) (y := (496352247/500000000 : ℝ)) (X := (18499866637931/100000000000000 : ℝ)) (Y := (81500150977567/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496352247/500000000 : ℝ) ^ p + (941388521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496352247/500000000 : ℝ)) (y := (941388521/1000000000 : ℝ)) (X := (81500150977567/100000000000000 : ℝ)) (Y := (18499866637931/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (164651533/173978691 : ℝ) ^ p + (287469287/289964485 : ℝ) ^ p := by
    exact cert_lt (x := (164651533/173978691 : ℝ)) (y := (287469287/289964485 : ℝ)) (X := (10725506183821/50000000000000 : ℝ)) (Y := (9818623549941/12500000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (567324818/614481185 : ℝ) ^ p + (611985987/614481185 : ℝ) ^ p := by
    exact cert_lt (x := (567324818/614481185 : ℝ)) (y := (611985987/614481185 : ℝ)) (X := (537262717981/5000000000000 : ℝ)) (Y := (5578421621007/6250000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1084531913/1156556445 : ℝ) ^ p + (383023617/385518815 : ℝ) ^ p := by
    exact cert_lt (x := (1084531913/1156556445 : ℝ)) (y := (383023617/385518815 : ℝ)) (X := (4147623904297/25000000000000 : ℝ)) (Y := (20852376291163/25000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496352247/500000000 : ℝ)) (U := (231311289/200000000 : ℝ)) (Ab := (850987227/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ)) (Ab := (1084531913/1000000000 : ℝ))
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

theorem localize26_slab030 (p : ℝ) (hpa : (223/8 : ℝ) ≤ p) (hpb : p ≤ (447/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (231311289/200000000 : ℝ)) ∧ coordinateBox (5533/10000 : ℝ) (5423/5000 : ℝ) (8189/10000 : ℝ) (5741/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (33222388873401/19757800000000 : ℝ) ≤ X j i + X k i) ∧
    (57673399703633/9878900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (30482511/31250000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(223/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (30482511/31250000 : ℝ))
      (by norm_num) 8 223 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(223/8 : ℝ)) ≤ (975440353/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975440353/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 223 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(447/16 : ℝ)) ≤ (975494617/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975494617/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 447 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (360666289693/24697250000000 : ℝ) (3742797/500000000 : ℝ) (1600000296367/9878900000000 : ℝ) (591/500 : ℝ) (975494617/500000000 : ℝ) (30482511/31250000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (223/8 : ℝ)) (β := (447/16 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (360666289693/24697250000000 : ℝ)) (δ := (3742797/500000000 : ℝ)) (h := (1600000296367/9878900000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (30482511/31250000 : ℝ)) (thia := (975440353/1000000000 : ℝ)) (thib := (975494617/1000000000 : ℝ))
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
  have hh := contract26_slab030 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 31, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract26_slab031 (p : ℝ) (hpa : (447/16 : ℝ) ≤ p) (hpb : p ≤ (28 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (721130814593/49505250000000 : ℝ) (7466343/1000000000 : ℝ) (3200000594063/19802100000000 : ℝ) (591/500 : ℝ) (975548643/500000000 : ℝ) (121936827/125000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156595263/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(678/625 : ℝ) ≤ X j i ∧ X j i ≤ -(346/625 : ℝ)
      else (8191/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5741/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (721130814593/49505250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7466343/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (938069097/1000000000 : ℝ) ^ p + (198699559/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (938069097/1000000000 : ℝ)) (y := (198699559/200000000 : ℝ)) (X := (16694569179661/100000000000000 : ℝ)) (Y := (520659058883/625000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198699559/200000000 : ℝ) ^ p + (938069097/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198699559/200000000 : ℝ)) (y := (938069097/1000000000 : ℝ)) (X := (520659058883/625000000000 : ℝ)) (Y := (16694569179661/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (482891723/250000000 : ℝ)) (τ := (938069097/1000000000 : ℝ)) (σ := (198699559/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819809917/866031289 : ℝ) ^ p + (858564946/866031289 : ℝ) ^ p := by
    exact cert_lt (x := (819809917/866031289 : ℝ)) (y := (858564946/866031289 : ℝ)) (X := (21529223542263/100000000000000 : ℝ)) (Y := (78470777611821/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (938069097/1000000000 : ℝ)) (n' := (866031289/1000000000 : ℝ)) (Ab := (819809917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (94142733/100000000 : ℝ) ^ p + (992741777/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94142733/100000000 : ℝ)) (y := (992741777/1000000000 : ℝ)) (X := (4612861992697/25000000000000 : ℝ)) (Y := (81548571200999/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992741777/1000000000 : ℝ) ^ p + (94142733/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992741777/1000000000 : ℝ)) (y := (94142733/100000000 : ℝ)) (X := (81548571200999/100000000000000 : ℝ)) (Y := (4612861992697/25000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1934169107/1000000000 : ℝ)) (τ := (94142733/100000000 : ℝ)) (σ := (992741777/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (411672562/434944183 : ℝ) ^ p + (862422023/869888366 : ℝ) ^ p := by
    exact cert_lt (x := (411672562/434944183 : ℝ)) (y := (862422023/869888366 : ℝ)) (X := (5361114430447/25000000000000 : ℝ)) (Y := (3142221744143/4000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (94142733/100000000 : ℝ)) (n' := (434944183/500000000 : ℝ)) (Ab := (205836281/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (470762667/500000000 : ℝ) ^ p + (992718353/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470762667/500000000 : ℝ)) (y := (992718353/1000000000 : ℝ)) (X := (9252653340591/50000000000000 : ℝ)) (Y := (20373677971787/25000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992718353/1000000000 : ℝ) ^ p + (470762667/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992718353/1000000000 : ℝ)) (y := (470762667/500000000 : ℝ)) (X := (20373677971787/25000000000000 : ℝ)) (Y := (9252653340591/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1934243687/1000000000 : ℝ)) (τ := (470762667/500000000 : ℝ)) (σ := (992718353/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823448096/870000723 : ℝ) ^ p + (287511460/290000241 : ℝ) ^ p := by
    exact cert_lt (x := (823448096/870000723 : ℝ)) (y := (287511460/290000241 : ℝ)) (X := (10720999036019/50000000000000 : ℝ)) (Y := (78558002895281/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (470762667/500000000 : ℝ)) (n' := (870000723/1000000000 : ℝ)) (Ab := (25732753/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (470764089/500000000 : ℝ) ^ p + (124089709/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (470764089/500000000 : ℝ)) (y := (124089709/125000000 : ℝ)) (X := (4626717970089/25000000000000 : ℝ)) (Y := (81493146562229/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124089709/125000000 : ℝ) ^ p + (470764089/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124089709/125000000 : ℝ)) (y := (470764089/500000000 : ℝ)) (X := (81493146562229/100000000000000 : ℝ)) (Y := (4626717970089/25000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (38684917/20000000 : ℝ)) (τ := (470764089/500000000 : ℝ)) (σ := (124089709/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (823451084/870003983 : ℝ) ^ p + (862537640/870003983 : ℝ) ^ p := by
    exact cert_lt (x := (823451084/870003983 : ℝ)) (y := (862537640/870003983 : ℝ)) (X := (167515054221/781250000000 : ℝ)) (Y := (4909879640151/6250000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (470764089/500000000 : ℝ)) (n' := (870003983/1000000000 : ℝ)) (Ab := (205862771/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (47076413/50000000 : ℝ) ^ p + (248179413/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (47076413/50000000 : ℝ)) (y := (248179413/250000000 : ℝ)) (X := (9253458505529/50000000000000 : ℝ)) (Y := (10186637573913/12500000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248179413/250000000 : ℝ) ^ p + (47076413/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (248179413/250000000 : ℝ)) (y := (47076413/50000000 : ℝ)) (X := (10186637573913/12500000000000 : ℝ)) (Y := (9253458505529/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (241780739/125000000 : ℝ)) (τ := (47076413/50000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (823451170/870004077 : ℝ) ^ p + (287512578/290001359 : ℝ) ^ p := by
    exact cert_lt (x := (823451170/870004077 : ℝ)) (y := (287512578/290001359 : ℝ)) (X := (21441924774753/100000000000000 : ℝ)) (Y := (39279038149829/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (47076413/50000000 : ℝ)) (n' := (870004077/1000000000 : ℝ)) (Ab := (82345117/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470764131/500000000 : ℝ) ^ p + (248179413/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (470764131/500000000 : ℝ)) (y := (248179413/250000000 : ℝ)) (X := (18506918111809/100000000000000 : ℝ)) (Y := (10186637573913/12500000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248179413/250000000 : ℝ) ^ p + (470764131/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248179413/250000000 : ℝ)) (y := (470764131/500000000 : ℝ)) (X := (10186637573913/12500000000000 : ℝ)) (Y := (18506918111809/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (823451172/870004079 : ℝ) ^ p + (862537736/870004079 : ℝ) ^ p := by
    exact cert_lt (x := (823451172/870004079 : ℝ)) (y := (862537736/870004079 : ℝ)) (X := (21441924852779/100000000000000 : ℝ)) (Y := (78558076343429/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1702223345/1843404737 : ℝ) ^ p + (1835938394/1843404737 : ℝ) ^ p := by
    exact cert_lt (x := (1702223345/1843404737 : ℝ)) (y := (1835938394/1843404737 : ℝ)) (X := (10741961915357/100000000000000 : ℝ)) (Y := (44629019204859/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1084710472/1156595263 : ℝ) ^ p + (1149128920/1156595263 : ℝ) ^ p := by
    exact cert_lt (x := (1084710472/1156595263 : ℝ)) (y := (1149128920/1156595263 : ℝ)) (X := (16584709283149/100000000000000 : ℝ)) (Y := (41707645612957/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248179413/250000000 : ℝ)) (U := (1156595263/1000000000 : ℝ)) (Ab := (340444669/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ)) (Ab := (135588809/125000000 : ℝ))
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

theorem localize26_slab031 (p : ℝ) (hpa : (447/16 : ℝ) ≤ p) (hpb : p ≤ (28 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1156595263/1000000000 : ℝ)) ∧ coordinateBox (346/625 : ℝ) (678/625 : ℝ) (8191/10000 : ℝ) (5741/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (333032847445267/198021000000000 : ℝ) ≤ X j i + X k i) ∧
    (115612599405937/19802100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 26 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (443/1000 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (121936827/125000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(447/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (121936827/125000000 : ℝ))
      (by norm_num) 16 447 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(447/16 : ℝ)) ≤ (975494617/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975494617/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 447 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(28 : ℝ)) ≤ (975548643/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (975548643/1000000000 : ℝ))
      (by norm_num) (by norm_num) 1 28 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail26 hpc X hB
  have FF : Facts p (cp p) (721130814593/49505250000000 : ℝ) (7466343/1000000000 : ℝ) (3200000594063/19802100000000 : ℝ) (591/500 : ℝ) (975548643/500000000 : ℝ) (121936827/125000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (447/16 : ℝ)) (β := (28 : ℝ)) (c := (443/1000 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (721130814593/49505250000000 : ℝ)) (δ := (7466343/1000000000 : ℝ)) (h := (3200000594063/19802100000000 : ℝ)) (A := (591/500 : ℝ))
      (tlo := (121936827/125000000 : ℝ)) (thia := (975494617/1000000000 : ℝ)) (thib := (975548643/1000000000 : ℝ))
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
  have hh := contract26_slab031 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
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

theorem localized_nonneg26_chunk01 (p : ℝ) (hpa : (27 : ℝ) ≤ p)
    (hpb : p ≤ (28 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (55/2 : ℝ) with hl | hr
  ·
    rcases le_total p (109/4 : ℝ) with hll | hlr
    ·
      rcases le_total p (217/8 : ℝ) with hlll | hllr
      ·
        rcases le_total p (433/16 : ℝ) with hllll | hlllr
        ·
          have hh := localize26_slab016 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab017 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (435/16 : ℝ) with hllrl | hllrr
        ·
          have hh := localize26_slab018 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab019 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (219/8 : ℝ) with hlrl | hlrr
      ·
        rcases le_total p (437/16 : ℝ) with hlrll | hlrlr
        ·
          have hh := localize26_slab020 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab021 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (439/16 : ℝ) with hlrrl | hlrrr
        ·
          have hh := localize26_slab022 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab023 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
  ·
    rcases le_total p (111/4 : ℝ) with hrl | hrr
    ·
      rcases le_total p (221/8 : ℝ) with hrll | hrlr
      ·
        rcases le_total p (441/16 : ℝ) with hrlll | hrllr
        ·
          have hh := localize26_slab024 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab025 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (443/16 : ℝ) with hrlrl | hrlrr
        ·
          have hh := localize26_slab026 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab027 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (223/8 : ℝ) with hrrl | hrrr
      ·
        rcases le_total p (445/16 : ℝ) with hrrll | hrrlr
        ·
          have hh := localize26_slab028 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab029 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (447/16 : ℝ) with hrrrl | hrrrr
        ·
          have hh := localize26_slab030 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab031 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD

end HlawkaSchatten.DiagonalRealBundle
theorem solution :
    ∀ p : ℝ, (27 : ℝ) ≤ p → p ≤ (28 : ℝ) →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ)) →
      (∀ j i, j ≠ i → (3/4 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : HlawkaSchatten.DiagonalRealBundle.coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ)
      (3/4 : ℝ) (1183/1000 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox, hji] using ho j i hji
  exact HlawkaSchatten.DiagonalRealBundle.localized_nonneg26_chunk01 p hp hpmax X hB hS hT hG

#print axioms solution
