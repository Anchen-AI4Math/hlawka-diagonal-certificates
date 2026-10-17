import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_coarse_failure_window21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem checked_assembly_real_three_window21
    (certificate_localized_domain4_21_00 : ∀ p : ℝ, (21 : ℝ) ≤ p → p ≤ (169/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_01 : ∀ p : ℝ, (169/8 : ℝ) ≤ p → p ≤ (85/4 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_02 : ∀ p : ℝ, (85/4 : ℝ) ≤ p → p ≤ (171/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_03 : ∀ p : ℝ, (171/8 : ℝ) ≤ p → p ≤ (43/2 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_04 : ∀ p : ℝ, (43/2 : ℝ) ≤ p → p ≤ (173/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_05 : ∀ p : ℝ, (173/8 : ℝ) ≤ p → p ≤ (87/4 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_06 : ∀ p : ℝ, (87/4 : ℝ) ≤ p → p ≤ (175/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_07 : ∀ p : ℝ, (175/8 : ℝ) ≤ p → p ≤ (22 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_08 : ∀ p : ℝ, (22 : ℝ) ≤ p → p ≤ (177/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_09 : ∀ p : ℝ, (177/8 : ℝ) ≤ p → p ≤ (89/4 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_10 : ∀ p : ℝ, (89/4 : ℝ) ≤ p → p ≤ (179/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_11 : ∀ p : ℝ, (179/8 : ℝ) ≤ p → p ≤ (45/2 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_12 : ∀ p : ℝ, (45/2 : ℝ) ≤ p → p ≤ (181/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_13 : ∀ p : ℝ, (181/8 : ℝ) ≤ p → p ≤ (91/4 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_14 : ∀ p : ℝ, (91/4 : ℝ) ≤ p → p ≤ (183/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_15 : ∀ p : ℝ, (183/8 : ℝ) ≤ p → p ≤ (23 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_16 : ∀ p : ℝ, (23 : ℝ) ≤ p → p ≤ (185/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_17 : ∀ p : ℝ, (185/8 : ℝ) ≤ p → p ≤ (93/4 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_18 : ∀ p : ℝ, (93/4 : ℝ) ≤ p → p ≤ (187/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_19 : ∀ p : ℝ, (187/8 : ℝ) ≤ p → p ≤ (47/2 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_20 : ∀ p : ℝ, (47/2 : ℝ) ≤ p → p ≤ (377/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_21 : ∀ p : ℝ, (377/16 : ℝ) ≤ p → p ≤ (379/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_22 : ∀ p : ℝ, (379/16 : ℝ) ≤ p → p ≤ (381/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_23 : ∀ p : ℝ, (381/16 : ℝ) ≤ p → p ≤ (383/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_24 : ∀ p : ℝ, (383/16 : ℝ) ≤ p → p ≤ (385/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_25 : ∀ p : ℝ, (385/16 : ℝ) ≤ p → p ≤ (387/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_26 : ∀ p : ℝ, (387/16 : ℝ) ≤ p → p ≤ (389/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_27 : ∀ p : ℝ, (389/16 : ℝ) ≤ p → p ≤ (391/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_28 : ∀ p : ℝ, (391/16 : ℝ) ≤ p → p ≤ (393/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_29 : ∀ p : ℝ, (393/16 : ℝ) ≤ p → p ≤ (395/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_30 : ∀ p : ℝ, (395/16 : ℝ) ≤ p → p ≤ (397/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_31 : ∀ p : ℝ, (397/16 : ℝ) ≤ p → p ≤ (399/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_32 : ∀ p : ℝ, (399/16 : ℝ) ≤ p → p ≤ (401/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_33 : ∀ p : ℝ, (401/16 : ℝ) ≤ p → p ≤ (403/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_34 : ∀ p : ℝ, (403/16 : ℝ) ≤ p → p ≤ (405/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_35 : ∀ p : ℝ, (405/16 : ℝ) ≤ p → p ≤ (407/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_36 : ∀ p : ℝ, (407/16 : ℝ) ≤ p → p ≤ (409/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_37 : ∀ p : ℝ, (409/16 : ℝ) ≤ p → p ≤ (411/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_38 : ∀ p : ℝ, (411/16 : ℝ) ≤ p → p ≤ (413/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_39 : ∀ p : ℝ, (413/16 : ℝ) ≤ p → p ≤ (415/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1)
    (certificate_localized_domain4_21_40 : ∀ p : ℝ, (415/16 : ℝ) ≤ p → p ≤ (26 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp hpmax x y z
  by_contra hn
  have he : hlawkaDeficit p (cyclicConstant p) x y z =
      cyclicConstant p * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
    unfold hlawkaDeficit pairGapSum pairGap tripleGap
    ring
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [he]
    exact sub_neg.mpr (lt_of_not_ge hn)
  obtain ⟨X, hd, ho, hS, hT, hG, hfail⟩ := HlawkaSchatten.DiagonalCutoff21.coarse_failure_window21 p hp hpmax x y z hf
  norm_num at hT
  have hnonneg : 0 ≤ tripleDeficit p (cyclicConstant p) X := by
    rcases le_total p (47/2 : ℝ) with hl | hr
    ·
      rcases le_total p (89/4 : ℝ) with hll | hlr
      ·
        rcases le_total p (173/8 : ℝ) with hlll | hllr
        ·
          rcases le_total p (85/4 : ℝ) with hllll | hlllr
          ·
            rcases le_total p (169/8 : ℝ) with hlllll | hllllr
            ·
              have hh := certificate_localized_domain4_21_00 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := certificate_localized_domain4_21_01 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (171/8 : ℝ) with hlllrl | hlllrr
            ·
              have hh := certificate_localized_domain4_21_02 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (43/2 : ℝ) with hlllrrl | hlllrrr
              ·
                have hh := certificate_localized_domain4_21_03 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_04 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (175/8 : ℝ) with hllrl | hllrr
          ·
            rcases le_total p (87/4 : ℝ) with hllrll | hllrlr
            ·
              have hh := certificate_localized_domain4_21_05 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := certificate_localized_domain4_21_06 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (22 : ℝ) with hllrrl | hllrrr
            ·
              have hh := certificate_localized_domain4_21_07 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (177/8 : ℝ) with hllrrrl | hllrrrr
              ·
                have hh := certificate_localized_domain4_21_08 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_09 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
      ·
        rcases le_total p (183/8 : ℝ) with hlrl | hlrr
        ·
          rcases le_total p (45/2 : ℝ) with hlrll | hlrlr
          ·
            rcases le_total p (179/8 : ℝ) with hlrlll | hlrllr
            ·
              have hh := certificate_localized_domain4_21_10 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := certificate_localized_domain4_21_11 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (181/8 : ℝ) with hlrlrl | hlrlrr
            ·
              have hh := certificate_localized_domain4_21_12 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (91/4 : ℝ) with hlrlrrl | hlrlrrr
              ·
                have hh := certificate_localized_domain4_21_13 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_14 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (185/8 : ℝ) with hlrrl | hlrrr
          ·
            rcases le_total p (23 : ℝ) with hlrrll | hlrrlr
            ·
              have hh := certificate_localized_domain4_21_15 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := certificate_localized_domain4_21_16 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (93/4 : ℝ) with hlrrrl | hlrrrr
            ·
              have hh := certificate_localized_domain4_21_17 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (187/8 : ℝ) with hlrrrrl | hlrrrrr
              ·
                have hh := certificate_localized_domain4_21_18 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_19 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
    ·
      rcases le_total p (395/16 : ℝ) with hrl | hrr
      ·
        rcases le_total p (385/16 : ℝ) with hrll | hrlr
        ·
          rcases le_total p (379/16 : ℝ) with hrlll | hrllr
          ·
            rcases le_total p (377/16 : ℝ) with hrllll | hrlllr
            ·
              have hh := certificate_localized_domain4_21_20 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := certificate_localized_domain4_21_21 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (381/16 : ℝ) with hrllrl | hrllrr
            ·
              have hh := certificate_localized_domain4_21_22 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (383/16 : ℝ) with hrllrrl | hrllrrr
              ·
                have hh := certificate_localized_domain4_21_23 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_24 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (389/16 : ℝ) with hrlrl | hrlrr
          ·
            rcases le_total p (387/16 : ℝ) with hrlrll | hrlrlr
            ·
              have hh := certificate_localized_domain4_21_25 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := certificate_localized_domain4_21_26 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (391/16 : ℝ) with hrlrrl | hrlrrr
            ·
              have hh := certificate_localized_domain4_21_27 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (393/16 : ℝ) with hrlrrrl | hrlrrrr
              ·
                have hh := certificate_localized_domain4_21_28 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_29 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
      ·
        rcases le_total p (405/16 : ℝ) with hrrl | hrrr
        ·
          rcases le_total p (399/16 : ℝ) with hrrll | hrrlr
          ·
            rcases le_total p (397/16 : ℝ) with hrrlll | hrrllr
            ·
              have hh := certificate_localized_domain4_21_30 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := certificate_localized_domain4_21_31 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (401/16 : ℝ) with hrrlrl | hrrlrr
            ·
              have hh := certificate_localized_domain4_21_32 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (403/16 : ℝ) with hrrlrrl | hrrlrrr
              ·
                have hh := certificate_localized_domain4_21_33 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_34 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (411/16 : ℝ) with hrrrl | hrrrr
          ·
            rcases le_total p (407/16 : ℝ) with hrrrll | hrrrlr
            ·
              have hh := certificate_localized_domain4_21_35 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (409/16 : ℝ) with hrrrlrl | hrrrlrr
              ·
                have hh := certificate_localized_domain4_21_36 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_37 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (413/16 : ℝ) with hrrrrl | hrrrrr
            ·
              have hh := certificate_localized_domain4_21_38 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (415/16 : ℝ) with hrrrrrl | hrrrrrr
              ·
                have hh := certificate_localized_domain4_21_39 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := certificate_localized_domain4_21_40 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
  exact (not_lt_of_ge hnonneg) hfail

#print axioms checked_assembly_real_three_window21
