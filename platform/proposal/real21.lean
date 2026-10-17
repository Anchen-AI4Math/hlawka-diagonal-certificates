import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction


theorem HlawkaSchatten.DiagonalCutoff21.real_three_window21 :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
