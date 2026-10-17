import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 131, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab131 (p : ℝ) (hpa : (803/32 : ℝ) ≤ p) (hpb : p ≤ (201/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2082601313813/109609500000000 : ℝ) (1220771/125000000 : ℝ) (4000000657657/21921900000000 : ℝ) (3033/2500 : ℝ) (7782313/4000000 : ℝ) (972755703/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298509439/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11169/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(233/500 : ℝ)
      else (7809/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5929/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2082601313813/109609500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1220771/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (462089959/500000000 : ℝ) ^ p + (198822117/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (462089959/500000000 : ℝ)) (y := (198822117/200000000 : ℝ)) (X := (13792174638313/100000000000000 : ℝ)) (Y := (21551961249237/25000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198822117/200000000 : ℝ) ^ p + (462089959/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198822117/200000000 : ℝ)) (y := (462089959/500000000 : ℝ)) (X := (21551961249237/25000000000000 : ℝ)) (Y := (13792174638313/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1918290503/1000000000 : ℝ)) (τ := (462089959/500000000 : ℝ)) (σ := (198822117/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (789288803/833226033 : ℝ) ^ p + (823459865/833226033 : ℝ) ^ p := by
    exact cert_lt (x := (789288803/833226033 : ℝ)) (y := (823459865/833226033 : ℝ)) (X := (3204770527921/12500000000000 : ℝ)) (Y := (74361836805713/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462089959/500000000 : ℝ)) (n' := (833226033/1000000000 : ℝ)) (Ab := (789288803/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (58100931/62500000 : ℝ) ^ p + (198618669/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (58100931/62500000 : ℝ)) (y := (198618669/200000000 : ℝ)) (X := (15981396938743/100000000000000 : ℝ)) (Y := (42009310405609/50000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198618669/200000000 : ℝ) ^ p + (58100931/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (198618669/200000000 : ℝ)) (y := (58100931/62500000 : ℝ)) (X := (42009310405609/50000000000000 : ℝ)) (Y := (15981396938743/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1922708241/1000000000 : ℝ)) (τ := (58100931/62500000 : ℝ)) (σ := (198618669/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (397564435/419805899 : ℝ) ^ p + (414922815/419805899 : ℝ) ^ p := by
    exact cert_lt (x := (397564435/419805899 : ℝ)) (y := (414922815/419805899 : ℝ)) (X := (1591840817273/6250000000000 : ℝ)) (Y := (18632637101369/25000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (58100931/62500000 : ℝ)) (n' := (419805899/500000000 : ℝ)) (Ab := (79512887/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (464916373/500000000 : ℝ) ^ p + (31032779/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (464916373/500000000 : ℝ)) (y := (31032779/31250000 : ℝ)) (X := (16075760307287/100000000000000 : ℝ)) (Y := (10490532097591/12500000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31032779/31250000 : ℝ) ^ p + (464916373/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (31032779/31250000 : ℝ)) (y := (464916373/500000000 : ℝ)) (X := (10490532097591/12500000000000 : ℝ)) (Y := (16075760307287/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (961440837/500000000 : ℝ)) (τ := (464916373/500000000 : ℝ)) (σ := (31032779/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795362221/839866994 : ℝ) ^ p + (415050413/419933497 : ℝ) ^ p := by
    exact cert_lt (x := (795362221/839866994 : ℝ)) (y := (415050413/419933497 : ℝ)) (X := (12731378147643/50000000000000 : ℝ)) (Y := (74537244928229/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (464916373/500000000 : ℝ)) (n' := (419933497/500000000 : ℝ)) (Ab := (795362221/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (92984139/100000000 : ℝ) ^ p + (24826179/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (92984139/100000000 : ℝ)) (y := (24826179/25000000 : ℝ)) (X := (16079515534463/100000000000000 : ℝ)) (Y := (41960251383479/50000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (24826179/25000000 : ℝ) ^ p + (92984139/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (24826179/25000000 : ℝ)) (y := (92984139/100000000 : ℝ)) (X := (41960251383479/50000000000000 : ℝ)) (Y := (16079515534463/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (38457771/20000000 : ℝ)) (τ := (92984139/100000000 : ℝ)) (σ := (24826179/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (795371479/839877119 : ℝ) ^ p + (830110951/839877119 : ℝ) ^ p := by
    exact cert_lt (x := (795371479/839877119 : ℝ)) (y := (830110951/839877119 : ℝ)) (X := (25462490482501/100000000000000 : ℝ)) (Y := (74537510543339/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (92984139/100000000 : ℝ)) (n' := (839877119/1000000000 : ℝ)) (Ab := (795371479/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (232460433/250000000 : ℝ) ^ p + (99304709/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (232460433/250000000 : ℝ)) (y := (99304709/100000000 : ℝ)) (X := (16079664127407/100000000000000 : ℝ)) (Y := (83920354138509/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99304709/100000000 : ℝ) ^ p + (232460433/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (99304709/100000000 : ℝ)) (y := (232460433/250000000 : ℝ)) (X := (83920354138509/100000000000000 : ℝ)) (Y := (16079664127407/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961444411/500000000 : ℝ)) (τ := (232460433/250000000 : ℝ)) (σ := (99304709/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (795371845/839877519 : ℝ) ^ p + (830111351/839877519 : ℝ) ^ p := by
    exact cert_lt (x := (795371845/839877519 : ℝ)) (y := (830111351/839877519 : ℝ)) (X := (12731240092007/50000000000000 : ℝ)) (Y := (37268760518331/50000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (232460433/250000000 : ℝ)) (n' := (839877519/1000000000 : ℝ)) (Ab := (159074369/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (464920873/500000000 : ℝ) ^ p + (993047087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464920873/500000000 : ℝ)) (y := (993047087/1000000000 : ℝ)) (X := (16079670210187/100000000000000 : ℝ)) (Y := (20980086942181/25000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993047087/1000000000 : ℝ) ^ p + (464920873/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993047087/1000000000 : ℝ)) (y := (464920873/500000000 : ℝ)) (X := (20980086942181/25000000000000 : ℝ)) (Y := (16079670210187/100000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1922888833/1000000000 : ℝ)) (τ := (464920873/500000000 : ℝ)) (σ := (993047087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795371861/839877536 : ℝ) ^ p + (103763921/104984692 : ℝ) ^ p := by
    exact cert_lt (x := (795371861/839877536 : ℝ)) (y := (103763921/104984692 : ℝ)) (X := (12731240052129/50000000000000 : ℝ)) (Y := (18634380370657/25000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (464920873/500000000 : ℝ)) (n' := (26246173/31250000 : ℝ)) (Ab := (795371861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (929841747/1000000000 : ℝ) ^ p + (993047087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (929841747/1000000000 : ℝ)) (y := (993047087/1000000000 : ℝ)) (X := (251244853823/1562500000000 : ℝ)) (Y := (20980086942181/25000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993047087/1000000000 : ℝ) ^ p + (929841747/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993047087/1000000000 : ℝ)) (y := (929841747/1000000000 : ℝ)) (X := (20980086942181/25000000000000 : ℝ)) (Y := (251244853823/1562500000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (961444417/500000000 : ℝ)) (τ := (929841747/1000000000 : ℝ)) (σ := (993047087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (795371861/839877537 : ℝ) ^ p + (830111369/839877537 : ℝ) ^ p := by
    exact cert_lt (x := (795371861/839877537 : ℝ)) (y := (830111369/839877537 : ℝ)) (X := (12731239671273/50000000000000 : ℝ)) (Y := (37268760754431/50000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (929841747/1000000000 : ℝ)) (n' := (839877537/1000000000 : ℝ)) (Ab := (795371861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (961444417/500000000 : ℝ)) (τ := (929841747/1000000000 : ℝ)) (σ := (993047087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (929841747/1000000000 : ℝ)) (n' := (839877537/1000000000 : ℝ)) (Ab := (795371861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (961444417/500000000 : ℝ)) (τ := (929841747/1000000000 : ℝ)) (σ := (993047087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (929841747/1000000000 : ℝ)) (n' := (839877537/1000000000 : ℝ)) (Ab := (795371861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (961444417/500000000 : ℝ)) (τ := (929841747/1000000000 : ℝ)) (σ := (993047087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (929841747/1000000000 : ℝ)) (n' := (839877537/1000000000 : ℝ)) (Ab := (795371861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (961444417/500000000 : ℝ)) (τ := (929841747/1000000000 : ℝ)) (σ := (993047087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (415938192/451490561 : ℝ) ^ p + (449049019/451490561 : ℝ) ^ p := by
    exact cert_lt (x := (415938192/451490561 : ℝ)) (y := (449049019/451490561 : ℝ)) (X := (12736515447001/100000000000000 : ℝ)) (Y := (43631742408441/50000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1116825995/1194037756 : ℝ) ^ p + (296067897/298509439 : ℝ) ^ p := by
    exact cert_lt (x := (1116825995/1194037756 : ℝ)) (y := (296067897/298509439 : ℝ)) (X := (18644781169317/100000000000000 : ℝ)) (Y := (20338804883931/25000000000000 : ℝ)) 201 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993047087/1000000000 : ℝ)) (U := (298509439/250000000 : ℝ)) (Ab := (25996137/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (929841747/1000000000 : ℝ)) (σ := (993047087/1000000000 : ℝ)) (Ab := (223365199/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab131
