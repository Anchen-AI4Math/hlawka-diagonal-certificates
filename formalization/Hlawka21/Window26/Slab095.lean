import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 95, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab095 (p : ℝ) (hpa : (511/16 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (354928597993/28296625000000 : ℝ) (6409173/1000000000 : ℝ) (3200000679119/22637300000000 : ℝ) (591/500 : ℝ) (978572063/500000000 : ℝ) (489265291/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (72430689/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(219/200 : ℝ) ≤ X j i ∧ X j i ≤ -(5657/10000 : ℝ)
      else (1663/2000 : ℝ) ≤ X j i ∧ X j i ≤ (5757/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (354928597993/28296625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6409173/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (473072971/500000000 : ℝ) ^ p + (124273879/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (473072971/500000000 : ℝ)) (y := (124273879/125000000 : ℝ)) (X := (3401654402669/20000000000000 : ℝ)) (Y := (82991749913621/100000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124273879/125000000 : ℝ) ^ p + (473072971/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124273879/125000000 : ℝ)) (y := (473072971/500000000 : ℝ)) (X := (82991749913621/100000000000000 : ℝ)) (Y := (3401654402669/20000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (970168487/500000000 : ℝ)) (τ := (473072971/500000000 : ℝ)) (σ := (124273879/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (830957695/872465766 : ℝ) ^ p + (288685531/290821922 : ℝ) ^ p := by
    exact cert_lt (x := (830957695/872465766 : ℝ)) (y := (288685531/290821922 : ℝ)) (X := (21017284577667/100000000000000 : ℝ)) (Y := (15796543390591/20000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (473072971/500000000 : ℝ)) (n' := (436232883/500000000 : ℝ)) (Ab := (166191539/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (474595187/500000000 : ℝ) ^ p + (993494131/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474595187/500000000 : ℝ)) (y := (993494131/1000000000 : ℝ)) (X := (9424892664029/50000000000000 : ℝ)) (Y := (20287559057847/25000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993494131/1000000000 : ℝ) ^ p + (474595187/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993494131/1000000000 : ℝ)) (y := (474595187/500000000 : ℝ)) (X := (20287559057847/25000000000000 : ℝ)) (Y := (9424892664029/50000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (388536901/200000000 : ℝ)) (τ := (474595187/500000000 : ℝ)) (σ := (993494131/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (208539000/218980027 : ℝ) ^ p + (869510935/875920108 : ℝ) ^ p := by
    exact cert_lt (x := (208539000/218980027 : ℝ)) (y := (869510935/875920108 : ℝ)) (X := (10471744030007/50000000000000 : ℝ)) (Y := (79056513336373/100000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (474595187/500000000 : ℝ)) (n' := (218980027/250000000 : ℝ)) (Ab := (208539/250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (23731633/25000000 : ℝ) ^ p + (496737941/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (23731633/25000000 : ℝ)) (y := (496737941/500000000 : ℝ)) (X := (18897470474909/100000000000000 : ℝ)) (Y := (2534454698183/3125000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496737941/500000000 : ℝ) ^ p + (23731633/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (496737941/500000000 : ℝ)) (y := (23731633/25000000 : ℝ)) (X := (2534454698183/3125000000000 : ℝ)) (Y := (18897470474909/100000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (971370601/500000000 : ℝ)) (τ := (23731633/25000000 : ℝ)) (σ := (496737941/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (417117300/438002503 : ℝ) ^ p + (869595833/876005006 : ℝ) ^ p := by
    exact cert_lt (x := (417117300/438002503 : ℝ)) (y := (869595833/876005006 : ℝ)) (X := (10470840272787/50000000000000 : ℝ)) (Y := (79058320553199/100000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (23731633/25000000 : ℝ)) (n' := (438002503/500000000 : ℝ)) (Ab := (4171173/5000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (237316789/250000000 : ℝ) ^ p + (496737717/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (237316789/250000000 : ℝ)) (y := (496737717/500000000 : ℝ)) (X := (9449320056813/50000000000000 : ℝ)) (Y := (81101380028559/100000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496737717/500000000 : ℝ) ^ p + (237316789/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496737717/500000000 : ℝ)) (y := (237316789/250000000 : ℝ)) (X := (81101380028559/100000000000000 : ℝ)) (Y := (9449320056813/50000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (194274259/100000000 : ℝ)) (τ := (237316789/250000000 : ℝ)) (σ := (496737717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (139039421/146001181 : ℝ) ^ p + (289865971/292002362 : ℝ) ^ p := by
    exact cert_lt (x := (139039421/146001181 : ℝ)) (y := (289865971/292002362 : ℝ)) (X := (4188327301903/20000000000000 : ℝ)) (Y := (4941147801631/6250000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (237316789/250000000 : ℝ)) (n' := (438003543/500000000 : ℝ)) (Ab := (417118263/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (949267201/1000000000 : ℝ) ^ p + (993475423/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (949267201/1000000000 : ℝ)) (y := (993475423/1000000000 : ℝ)) (X := (9449334391061/50000000000000 : ℝ)) (Y := (81101351293393/100000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993475423/1000000000 : ℝ) ^ p + (949267201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993475423/1000000000 : ℝ)) (y := (949267201/1000000000 : ℝ)) (X := (81101351293393/100000000000000 : ℝ)) (Y := (9449334391061/50000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (60710707/31250000 : ℝ)) (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (834236573/876007137 : ℝ) ^ p + (289865988/292002379 : ℝ) ^ p := by
    exact cert_lt (x := (834236573/876007137 : ℝ)) (y := (289865988/292002379 : ℝ)) (X := (20941635249821/100000000000000 : ℝ)) (Y := (79058365911631/100000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (949267201/1000000000 : ℝ)) (n' := (876007137/1000000000 : ℝ)) (Ab := (834236573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (60710707/31250000 : ℝ)) (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (949267201/1000000000 : ℝ)) (n' := (876007137/1000000000 : ℝ)) (Ab := (834236573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (60710707/31250000 : ℝ)) (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (949267201/1000000000 : ℝ)) (n' := (876007137/1000000000 : ℝ)) (Ab := (834236573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (60710707/31250000 : ℝ)) (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (949267201/1000000000 : ℝ)) (n' := (876007137/1000000000 : ℝ)) (Ab := (834236573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (60710707/31250000 : ℝ)) (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (949267201/1000000000 : ℝ)) (n' := (876007137/1000000000 : ℝ)) (Ab := (834236573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (60710707/31250000 : ℝ)) (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (949267201/1000000000 : ℝ)) (n' := (876007137/1000000000 : ℝ)) (Ab := (834236573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (60710707/31250000 : ℝ)) (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc15 : 1 < (95344405/102283832 : ℝ) ^ p + (611566601/613702992 : ℝ) ^ p := by
    exact cert_lt (x := (95344405/102283832 : ℝ)) (y := (611566601/613702992 : ℝ)) (X := (10559008128597/100000000000000 : ℝ)) (Y := (44720496045283/50000000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (1094941549/1158891024 : ℝ) ^ p + (384160617/386297008 : ℝ) ^ p := by
    exact cert_lt (x := (1094941549/1158891024 : ℝ)) (y := (384160617/386297008 : ℝ)) (X := (16260982363081/100000000000000 : ℝ)) (Y := (10467377321749/12500000000000 : ℝ)) 32 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993475423/1000000000 : ℝ)) (U := (72430689/62500000 : ℝ)) (Ab := (171619929/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc15.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (949267201/1000000000 : ℝ)) (σ := (993475423/1000000000 : ℝ)) (Ab := (1094941549/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc16.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab095
