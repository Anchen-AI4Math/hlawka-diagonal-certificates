import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 82, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab082 (p : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (755/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524649825887/25730250000000 : ℝ) (5249783/500000000 : ℝ) (2000000308763/10292100000000 : ℝ) (3033/2500 : ℝ) (30345279/15625000 : ℝ) (242752773/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (74588439/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(11119/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4577/10000 : ℝ)
      else (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524649825887/25730250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5249783/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (28718771/31250000 : ℝ) ^ p + (993808919/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28718771/31250000 : ℝ)) (y := (993808919/1000000000 : ℝ)) (X := (13629591495481/100000000000000 : ℝ)) (Y := (43185212999281/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993808919/1000000000 : ℝ) ^ p + (28718771/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (993808919/1000000000 : ℝ)) (y := (28718771/31250000 : ℝ)) (X := (43185212999281/50000000000000 : ℝ)) (Y := (13629591495481/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1912809591/1000000000 : ℝ)) (τ := (28718771/31250000 : ℝ)) (σ := (993808919/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782457212/828448385 : ℝ) ^ p + (817948819/828448385 : ℝ) ^ p := by
    exact cert_lt (x := (782457212/828448385 : ℝ)) (y := (817948819/828448385 : ℝ)) (X := (25987253692531/100000000000000 : ℝ)) (Y := (37006373878639/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (28718771/31250000 : ℝ)) (n' := (165689677/200000000 : ℝ)) (Ab := (195614303/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924646163/1000000000 : ℝ) ^ p + (496381637/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924646163/1000000000 : ℝ)) (y := (496381637/500000000 : ℝ)) (X := (1968548687373/12500000000000 : ℝ)) (Y := (84251626975181/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496381637/500000000 : ℝ) ^ p + (924646163/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496381637/500000000 : ℝ)) (y := (924646163/1000000000 : ℝ)) (X := (84251626975181/100000000000000 : ℝ)) (Y := (1968548687373/12500000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917409437/1000000000 : ℝ)) (τ := (924646163/1000000000 : ℝ)) (σ := (496381637/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (112648192/119304473 : ℝ) ^ p + (117804535/119304473 : ℝ) ^ p := by
    exact cert_lt (x := (112648192/119304473 : ℝ)) (y := (117804535/119304473 : ℝ)) (X := (25807670494197/100000000000000 : ℝ)) (Y := (1483846610407/2000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924646163/1000000000 : ℝ)) (n' := (835131311/1000000000 : ℝ)) (Ab := (1540112/1953125 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184978559/200000000 : ℝ) ^ p + (310223/312500 : ℝ) ^ p := by
    exact cert_lt (x := (184978559/200000000 : ℝ)) (y := (310223/312500 : ℝ)) (X := (3169559262067/20000000000000 : ℝ)) (Y := (84152220829893/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (310223/312500 : ℝ) ^ p + (184978559/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (310223/312500 : ℝ)) (y := (184978559/200000000 : ℝ)) (X := (84152220829893/100000000000000 : ℝ)) (Y := (3169559262067/20000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (383521279/200000000 : ℝ)) (τ := (184978559/200000000 : ℝ)) (σ := (310223/312500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (788802088/835422353 : ℝ) ^ p + (824922787/835422353 : ℝ) ^ p := by
    exact cert_lt (x := (788802088/835422353 : ℝ)) (y := (824922787/835422353 : ℝ)) (X := (12899953021659/50000000000000 : ℝ)) (Y := (74200095469613/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184978559/200000000 : ℝ)) (n' := (835422353/1000000000 : ℝ)) (Ab := (98600261/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (924903457/1000000000 : ℝ) ^ p + (248177861/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (924903457/1000000000 : ℝ)) (y := (248177861/250000000 : ℝ)) (X := (15852107227663/100000000000000 : ℝ)) (Y := (84147908850421/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248177861/250000000 : ℝ) ^ p + (924903457/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248177861/250000000 : ℝ)) (y := (924903457/1000000000 : ℝ)) (X := (84147908850421/100000000000000 : ℝ)) (Y := (15852107227663/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1917614901/1000000000 : ℝ)) (τ := (924903457/1000000000 : ℝ)) (σ := (248177861/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (788813531/835434933 : ℝ) ^ p + (824935367/835434933 : ℝ) ^ p := by
    exact cert_lt (x := (788813531/835434933 : ℝ)) (y := (824935367/835434933 : ℝ)) (X := (6449892594319/25000000000000 : ℝ)) (Y := (18550107749339/25000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (924903457/1000000000 : ℝ)) (n' := (835434933/1000000000 : ℝ)) (Ab := (788813531/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (924903917/1000000000 : ℝ) ^ p + (992711351/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924903917/1000000000 : ℝ)) (y := (992711351/1000000000 : ℝ)) (X := (15852293242611/100000000000000 : ℝ)) (Y := (84147722856067/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992711351/1000000000 : ℝ) ^ p + (924903917/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992711351/1000000000 : ℝ)) (y := (924903917/1000000000 : ℝ)) (X := (84147722856067/100000000000000 : ℝ)) (Y := (15852293242611/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479403817/250000000 : ℝ)) (τ := (924903917/1000000000 : ℝ)) (σ := (992711351/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (788814025/835435476 : ℝ) ^ p + (412467955/417717738 : ℝ) ^ p := by
    exact cert_lt (x := (788814025/835435476 : ℝ)) (y := (412467955/417717738 : ℝ)) (X := (12899777974277/50000000000000 : ℝ)) (Y := (74200445479797/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (924903917/1000000000 : ℝ)) (n' := (208858869/250000000 : ℝ)) (Ab := (31552561/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924903937/1000000000 : ℝ) ^ p + (992711347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924903937/1000000000 : ℝ)) (y := (992711347/1000000000 : ℝ)) (X := (3170460266053/20000000000000 : ℝ)) (Y := (42073857428159/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992711347/1000000000 : ℝ) ^ p + (924903937/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992711347/1000000000 : ℝ)) (y := (924903937/1000000000 : ℝ)) (X := (42073857428159/50000000000000 : ℝ)) (Y := (3170460266053/20000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (479403821/250000000 : ℝ)) (τ := (924903937/1000000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (788814046/835435499 : ℝ) ^ p + (824935933/835435499 : ℝ) ^ p := by
    exact cert_lt (x := (788814046/835435499 : ℝ)) (y := (824935933/835435499 : ℝ)) (X := (1289977769783/5000000000000 : ℝ)) (Y := (74200446093233/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924903937/1000000000 : ℝ)) (n' := (835435499/1000000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (462451969/500000000 : ℝ) ^ p + (992711347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462451969/500000000 : ℝ)) (y := (992711347/1000000000 : ℝ)) (X := (15852301734647/100000000000000 : ℝ)) (Y := (42073857428159/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992711347/1000000000 : ℝ) ^ p + (462451969/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992711347/1000000000 : ℝ)) (y := (462451969/500000000 : ℝ)) (X := (42073857428159/50000000000000 : ℝ)) (Y := (15852301734647/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (394407023/417717750 : ℝ) ^ p + (412467967/417717750 : ℝ) ^ p := by
    exact cert_lt (x := (394407023/417717750 : ℝ)) (y := (412467967/417717750 : ℝ)) (X := (3224944333381/12500000000000 : ℝ)) (Y := (14840089223981/20000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (n' := (1670871/2000000 : ℝ)) (Ab := (394407023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (383523057/200000000 : ℝ)) (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (118293247/129041784 : ℝ) ^ p + (128291815/129041784 : ℝ) ^ p := by
    exact cert_lt (x := (118293247/129041784 : ℝ)) (y := (128291815/129041784 : ℝ)) (X := (6424280481607/50000000000000 : ℝ)) (Y := (43575719675521/50000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (370616797/397805008 : ℝ) ^ p + (591457729/596707512 : ℝ) ^ p := by
    exact cert_lt (x := (370616797/397805008 : ℝ)) (y := (591457729/596707512 : ℝ)) (X := (18819438846113/100000000000000 : ℝ)) (Y := (81180561609109/100000000000000 : ℝ)) 755 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992711347/1000000000 : ℝ)) (U := (74588439/62500000 : ℝ)) (Ab := (828052729/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (462451969/500000000 : ℝ)) (σ := (992711347/1000000000 : ℝ)) (Ab := (1111850391/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab082
