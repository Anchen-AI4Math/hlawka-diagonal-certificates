import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction


theorem HlawkaSchatten.DiagonalCutoff21.real_three_window26 :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
