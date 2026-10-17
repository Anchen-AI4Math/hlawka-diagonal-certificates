import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_real_three_window21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_real_three_window26
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff21

theorem checked_root_assembly (htail : ∀ p : ℝ, 32 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p)) :
    ∀ p : ℝ, 21 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  by_cases hp32 : 32 ≤ p
  · exact htail p hp32
  · apply complex_least_of_real_three p (by linarith)
    by_cases hp26 : p ≤ 26
    · exact real_three_window21 p hp hp26
    · exact real_three_window26 p (by linarith) (by linarith)

#print axioms checked_root_assembly
