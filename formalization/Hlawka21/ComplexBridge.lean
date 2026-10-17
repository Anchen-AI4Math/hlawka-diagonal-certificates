import Hlawka21.Foundation.ComplexTransfer

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem complex_least_of_real_three :
    ∀ p : ℝ, 1 < p →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  intro p hp hreal
  exact isLeast_of_real_three_bound hp hreal

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three
