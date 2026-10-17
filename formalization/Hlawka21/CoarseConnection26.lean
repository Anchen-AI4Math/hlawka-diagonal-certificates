import Hlawka21.Coarse26
import Hlawka21.NormBasic
import Hlawka21.ContractionFacts
import Hlawka21.Tail

/- Paper Section 3: LP stage 0, actual norm half-tail, LP stage 1.
   The hypotheses describe an oriented normalized failure, with
   original coordinate norms throughout. No LP certificate predicate
   or assumed coarse box appears in the hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem coarse_box26_oriented (p : ℝ) (hp : (26 : ℝ) ≤ p) (X : Triple)
    (N P : Fin 3 → ℝ) (T : ℝ)
    (hNdef : ∀ i, N i = lpNorm p (X i))
    (hP0 : P 0 = lpNorm p (X 1 + X 2))
    (hP1 : P 1 = lpNorm p (X 0 + X 2))
    (hP2 : P 2 = lpNorm p (X 0 + X 1))
    (hTdef : T = lpNorm p (X 0 + X 1 + X 2))
    (hS : N 0 + N 1 + N 2 = 3) (hNT : ∀ i, N i ≤ T)
    (hT1 : 1 ≤ T) (hTcap : T ≤ (591 / 500 : ℝ))
    (hmain0 : P 0 - (X 1 0 + X 2 0) ≤ (1 / 10 : ℝ))
    (hmain1 : P 1 - (X 0 1 + X 2 1) ≤ (1 / 10 : ℝ))
    (hmain2 : P 2 - (X 0 2 + X 1 2) ≤ (1 / 10 : ℝ))
    (hfail : T - (5759 / 500 : ℝ) * (P 0 + P 1 + P 2) ≤ 3 - 6 * (5759 / 500 : ℝ)) :
    coordinateBox (477 / 1000 : ℝ) (1183 / 1000 : ℝ) (3 / 4 : ℝ) (1183 / 1000 : ℝ) X := by
  have hp1 : 1 ≤ p := by linarith
  have hpn : 0 < p := by linarith
  have hp21 : 21 ≤ p := by linarith
  have hnpos (i : Fin 3) : 0 ≤ N i := by rw [hNdef]; exact lpNorm_nonneg p (X i)
  have hcoord (j i : Fin 3) : -N j ≤ X j i ∧ X j i ≤ N j := by
    have hc := norm_apply_le_lpNorm hp1 (X j) i
    rw [Real.norm_eq_abs, ← hNdef] at hc
    exact abs_le.mp hc
  have hn0 := hnpos 0
  rcases hcoord 0 0 with ⟨hx00l, hx00u⟩
  rcases hcoord 0 1 with ⟨hx01l, hx01u⟩
  rcases hcoord 0 2 with ⟨hx02l, hx02u⟩
  have hn1 := hnpos 1
  rcases hcoord 1 0 with ⟨hx10l, hx10u⟩
  rcases hcoord 1 1 with ⟨hx11l, hx11u⟩
  rcases hcoord 1 2 with ⟨hx12l, hx12u⟩
  have hn2 := hnpos 2
  rcases hcoord 2 0 with ⟨hx20l, hx20u⟩
  rcases hcoord 2 1 with ⟨hx21l, hx21u⟩
  rcases hcoord 2 2 with ⟨hx22l, hx22u⟩
  have hnt0 := hNT 0
  have ht0 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 0
  rw [Real.norm_eq_abs, ← hTdef] at ht0
  simp only [Pi.add_apply] at ht0
  rcases abs_le.mp ht0 with ⟨ht0l, ht0u⟩
  have hnt1 := hNT 1
  have ht1 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 1
  rw [Real.norm_eq_abs, ← hTdef] at ht1
  simp only [Pi.add_apply] at ht1
  rcases abs_le.mp ht1 with ⟨ht1l, ht1u⟩
  have hnt2 := hNT 2
  have ht2 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 2
  rw [Real.norm_eq_abs, ← hTdef] at ht2
  simp only [Pi.add_apply] at ht2
  rcases abs_le.mp ht2 with ⟨ht2l, ht2u⟩
  have hp0n : 0 ≤ P 0 := by rw [hP0]; exact lpNorm_nonneg p _
  have hp0u : P 0 ≤ N 1 + N 2 := by rw [hP0, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  have hp1n : 0 ≤ P 1 := by rw [hP1]; exact lpNorm_nonneg p _
  have hp1u : P 1 ≤ N 0 + N 2 := by rw [hP1, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  have hp2n : 0 ≤ P 2 := by rw [hP2]; exact lpNorm_nonneg p _
  have hp2u : P 2 ≤ N 0 + N 1 := by rw [hP2, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  let v : Fin 16 → ℝ := fun z ↦ match z.val with
    | 0 => X 0 0
    | 1 => X 0 1
    | 2 => X 0 2
    | 3 => X 1 0
    | 4 => X 1 1
    | 5 => X 1 2
    | 6 => X 2 0
    | 7 => X 2 1
    | 8 => X 2 2
    | 9 => N 0
    | 10 => N 1
    | 11 => N 2
    | 12 => P 0
    | 13 => P 1
    | 14 => P 2
    | 15 => T
    | _ => 0
  have h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn0]
  have h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt0]
  have h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn1]
  have h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt1]
  have h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn2]
  have h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt2]
  have h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ) := by norm_num [v]; linarith only [hT1]
  have h7 : ((1 : ℝ) * v 15) ≤ (591 / 500 : ℝ) := by norm_num [v]; linarith only [hTcap]
  have h8 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx00l]
  have h9 : ((1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx00u]
  have h10 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx01l]
  have h11 : ((1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx01u]
  have h12 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx02l]
  have h13 : ((1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx02u]
  have h14 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx10l]
  have h15 : ((1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx10u]
  have h16 : ((-1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx11l]
  have h17 : ((1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx11u]
  have h18 : ((-1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx12l]
  have h19 : ((1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx12u]
  have h20 : ((-1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx20l]
  have h21 : ((1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx20u]
  have h22 : ((-1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx21l]
  have h23 : ((1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx21u]
  have h24 : ((-1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx22l]
  have h25 : ((1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx22u]
  have h26 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht0l]
  have h27 : ((1 : ℝ) * v 0 + (1 : ℝ) * v 3 + (1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht0u]
  have h28 : ((-1 : ℝ) * v 12) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp0n]
  have h29 : ((-1 : ℝ) * v 10 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 12) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp0u]
  have h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (1 / 10 : ℝ) := by norm_num [v]; linarith only [hmain0]
  have h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht1l]
  have h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht1u]
  have h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp1n]
  have h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp1u]
  have h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (1 / 10 : ℝ) := by norm_num [v]; linarith only [hmain1]
  have h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht2l]
  have h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht2u]
  have h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp2n]
  have h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp2u]
  have h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (1 / 10 : ℝ) := by norm_num [v]; linarith only [hmain2]
  have h41 : ((-5759 / 500 : ℝ) * v 12 + (-5759 / 500 : ℝ) * v 13 + (-5759 / 500 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-16527 / 250 : ℝ) := by norm_num [v]; linarith only [hfail]
  have heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = (3 : ℝ) := by norm_num [v]; linarith only [hS]
  have first := coarse26_stage0 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 heq
  norm_num [v] at first
  rcases first with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
  have tail0 : P 0 ≤ X 1 0 + X 2 0 + 1/100000 := by
    rw [hP0, lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply half_tail21 hp21 (by linarith only [a0]) (by linarith only [a1])
      (abs_le.mpr ⟨by linarith only [a3], by linarith only [a2]⟩)
      (abs_le.mpr ⟨by linarith only [a5], by linarith only [a4]⟩)
  have tail1 : P 1 ≤ X 0 1 + X 2 1 + 1/100000 := by
    rw [hP1, lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply half_tail21 hp21 (by linarith only [a6]) (by linarith only [a7])
      (abs_le.mpr ⟨by linarith only [a9], by linarith only [a8]⟩)
      (abs_le.mpr ⟨by linarith only [a11], by linarith only [a10]⟩)
  have tail2 : P 2 ≤ X 0 2 + X 1 2 + 1/100000 := by
    rw [hP2, lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply half_tail21 hp21 (by linarith only [a12]) (by linarith only [a13])
      (abs_le.mpr ⟨by linarith only [a15], by linarith only [a14]⟩)
      (abs_le.mpr ⟨by linarith only [a17], by linarith only [a16]⟩)
  have h42 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (1 / 100000 : ℝ) := by norm_num [v]; linarith only [tail0]
  have h43 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (1 / 100000 : ℝ) := by norm_num [v]; linarith only [tail1]
  have h44 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (1 / 100000 : ℝ) := by norm_num [v]; linarith only [tail2]
  have second := coarse26_stage1 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 heq
  norm_num [v] at second
  rcases second with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17⟩
  intro j i
  fin_cases j <;> fin_cases i
  · rw [if_pos rfl]
    change -(1183 / 1000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(477 / 1000 : ℝ)
    constructor <;> linarith only [b0, b1]
  · change (3 / 4 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1183 / 1000 : ℝ)
    constructor <;> linarith only [b2, b3]
  · change (3 / 4 : ℝ) ≤ X 0 2 ∧ X 0 2 ≤ (1183 / 1000 : ℝ)
    constructor <;> linarith only [b4, b5]
  · change (3 / 4 : ℝ) ≤ X 1 0 ∧ X 1 0 ≤ (1183 / 1000 : ℝ)
    constructor <;> linarith only [b6, b7]
  · rw [if_pos rfl]
    change -(1183 / 1000 : ℝ) ≤ X 1 1 ∧ X 1 1 ≤ -(477 / 1000 : ℝ)
    constructor <;> linarith only [b8, b9]
  · change (3 / 4 : ℝ) ≤ X 1 2 ∧ X 1 2 ≤ (1183 / 1000 : ℝ)
    constructor <;> linarith only [b10, b11]
  · change (3 / 4 : ℝ) ≤ X 2 0 ∧ X 2 0 ≤ (1183 / 1000 : ℝ)
    constructor <;> linarith only [b12, b13]
  · change (3 / 4 : ℝ) ≤ X 2 1 ∧ X 2 1 ≤ (1183 / 1000 : ℝ)
    constructor <;> linarith only [b14, b15]
  · rw [if_pos rfl]
    change -(1183 / 1000 : ℝ) ≤ X 2 2 ∧ X 2 2 ≤ -(477 / 1000 : ℝ)
    constructor <;> linarith only [b16, b17]

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.coarse_box26_oriented
