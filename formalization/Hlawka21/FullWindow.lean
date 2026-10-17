import Hlawka21.RealWindows
import Hlawka21.ComplexBridge

/- The local proof checks every new ingredient with actual proof imports.
   The already Proved platform cutoff32 tail is an explicit input here;
   the final platform solution supplies that closed dependency. -/
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem campaign_cutoff21_from_tail
    (htail : ∀ p : ℝ, 32 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p)) :
    ∀ p : ℝ, 21 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  intro p hp
  by_cases hp32 : 32 ≤ p
  · exact htail p hp32
  · apply complex_least_of_real_three p (by linarith)
    by_cases hp26 : p ≤ 26
    · exact real_three_window21 p hp hp26
    · exact real_three_window26 p (by linarith) (by linarith)

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three
#print axioms HlawkaSchatten.DiagonalCutoff21.campaign_cutoff21_from_tail
