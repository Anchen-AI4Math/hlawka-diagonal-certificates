import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction


theorem HlawkaSchatten.DiagonalCutoff21.scalar_window21 :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
      (273 / 625 : ℝ) * p < cyclicConstant p ∧
      cyclicConstant p ≤ p / 2 ∧
      scalarEnvelope p (1011 / 2500 : ℝ) < cyclicConstant p := by sorry
