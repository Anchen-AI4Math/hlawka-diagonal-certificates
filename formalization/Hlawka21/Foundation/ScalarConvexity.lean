/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
namespace HlawkaSchatten
/-- Convexity of the scalar power potential before its positive rescaling. -/
theorem convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hImage : (norm : ℝ → ℝ) '' Set.univ = Set.Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact norm_nonneg x
    · intro hy
      have hy' : 0 ≤ y := by simpa only [Set.mem_Ici] using hy
      exact ⟨y, Set.mem_univ y, by simp [abs_of_nonneg hy']⟩
  have hOuter : ConvexOn ℝ ((norm : ℝ → ℝ) '' Set.univ) (fun y : ℝ ↦ y ^ p) := by
    rw [hImage]
    exact convexOn_rpow hp
  have hMono : MonotoneOn (fun y : ℝ ↦ y ^ p) ((norm : ℝ → ℝ) '' Set.univ) := by
    rw [hImage]
    exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos (zero_lt_one.trans_le hp)).monotoneOn
  convert hOuter.comp convexOn_univ_norm hMono using 1
  ext x
  simp only [Function.comp_apply, Real.norm_eq_abs]


end HlawkaSchatten
