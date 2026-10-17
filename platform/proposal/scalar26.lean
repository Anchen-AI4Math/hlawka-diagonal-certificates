import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction


theorem HlawkaSchatten.DiagonalCutoff21.scalar_window26 :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
      (443 / 1000 : ℝ) * p < cyclicConstant p ∧
      cyclicConstant p ≤ p / 2 ∧
      scalarEnvelope p (197 / 500 : ℝ) < cyclicConstant p := by sorry
