import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Abel

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Relabeling and normalization of a strict counterexample -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The target inequality with all terms moved to the nonnegative side. -/
noncomputable def hlawkaDeficit (p K : ℝ) (x y z : ι → ℝ) : ℝ :=
  (2 * K - 1) * (lpNorm p x + lpNorm p y + lpNorm p z) + lpNorm p (x + y + z) -
    K * (lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z))



















end HlawkaSchatten.DiagonalConstruction
