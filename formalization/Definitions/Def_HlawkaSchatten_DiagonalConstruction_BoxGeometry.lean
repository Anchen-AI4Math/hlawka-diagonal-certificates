import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
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

/-!
# Quadratic geometry of the cyclic box

The joint radial estimate uses the convenient bound `300`. This weaker
intermediate constant leaves the exponent cutoff unchanged.
-/

namespace HlawkaSchatten.DiagonalConstruction

def euclideanSq (v : Fin 3 → ℝ) : ℝ := ∑ i, (v i) ^ 2

def frobeniusSq (X : Triple) : ℝ := ∑ j, euclideanSq (X j)

def applyTriple (X : Triple) (a : Fin 3 → ℝ) : Fin 3 → ℝ := fun i ↦ ∑ j, a j * X j i

def totalTriple (X : Triple) : Fin 3 → ℝ := ∑ j, X j

























end HlawkaSchatten.DiagonalConstruction
