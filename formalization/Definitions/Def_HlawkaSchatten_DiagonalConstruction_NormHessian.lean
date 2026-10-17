import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Directional second derivatives of the finite real coordinate norm -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

noncomputable def powerSum (p : ℝ) (v : ι → ℝ) : ℝ := ∑ i, |v i| ^ p

noncomputable def powerPair (p : ℝ) (v h : ι → ℝ) : ℝ :=
  ∑ i, |v i| ^ (p - 2) * v i * h i

noncomputable def powerQuad (p : ℝ) (v h : ι → ℝ) : ℝ :=
  ∑ i, |v i| ^ (p - 2) * (h i) ^ 2

noncomputable def powerResidual (p : ℝ) (v h : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i, |v i| ^ (p - 2) * (h i - a * v i) ^ 2

noncomputable def radialCoefficient (p : ℝ) (v h : ι → ℝ) : ℝ :=
  powerPair p v h / powerSum p v

noncomputable def normSlope (p : ℝ) (v h : ι → ℝ) : ℝ :=
  powerSum p v ^ (1 / p - 1) * powerPair p v h

noncomputable def normHessian (p : ℝ) (v h : ι → ℝ) : ℝ :=
  (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h (radialCoefficient p v h)









































end HlawkaSchatten.DiagonalConstruction
