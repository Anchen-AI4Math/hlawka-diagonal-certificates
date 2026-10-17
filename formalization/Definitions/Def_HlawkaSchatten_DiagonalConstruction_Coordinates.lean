import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Large pair coordinates and signed coordinate permutations -/

namespace HlawkaSchatten.DiagonalConstruction









/-- A simultaneous coordinate permutation and reflection. -/
def orient (e : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ s i * x (e i)







end HlawkaSchatten.DiagonalConstruction
