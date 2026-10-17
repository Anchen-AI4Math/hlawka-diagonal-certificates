import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
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

/-! # A strict counterexample lies in the cyclic coordinate box -/

namespace HlawkaSchatten.DiagonalConstruction

/-- Columns first, then coordinates within each column. -/
abbrev Triple := Fin 3 → Fin 3 → ℝ

def cyclicCenter : Triple := fun j i ↦ if i = j then -1 else 1

def entryBox : Set Triple := {X | ∀ j i, |X j i - cyclicCenter j i| ≤ 19 / 100}

noncomputable def tripleDeficit (p K : ℝ) (X : Triple) : ℝ :=
  hlawkaDeficit p K (X 0) (X 1) (X 2)







end HlawkaSchatten.DiagonalConstruction
