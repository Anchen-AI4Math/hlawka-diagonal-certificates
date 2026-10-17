import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

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

noncomputable def cyclicA (p t : ℝ) : ℝ := (t ^ p + 2) ^ (1 / p)

noncomputable def cyclicB (p t : ℝ) : ℝ :=
  (2 * |1 - t| ^ p + (2 : ℝ) ^ p) ^ (1 / p)

noncomputable def cyclicRatio (p t : ℝ) : ℝ :=
  (3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t|) /
    (6 * cyclicA p t - 3 * cyclicB p t)

noncomputable def cyclicConstant (p : ℝ) : ℝ :=
  sSup (cyclicRatio p '' Set.Icc (1 / 2) 2)

























end HlawkaSchatten.DiagonalConstruction
