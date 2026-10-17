import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 70, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab070 (p : ℝ) (hpa : (371/16 : ℝ) ≤ p) (hpb : p ≤ (743/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1051418151703/50641500000000 : ℝ) (10695999/1000000000 : ℝ) (2000000303849/10128300000000 : ℝ) (3033/2500 : ℝ) (97058829/50000000 : ℝ) (970549241/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193262619/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5553/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2277/5000 : ℝ)
      else (963/1250 : ℝ) ≤ X j i ∧ X j i ≤ (2369/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1051418151703/50641500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10695999/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (917622981/1000000000 : ℝ) ^ p + (496865267/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (917622981/1000000000 : ℝ)) (y := (496865267/500000000 : ℝ)) (X := (6793307774343/50000000000000 : ℝ)) (Y := (4320670126129/5000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496865267/500000000 : ℝ) ^ p + (917622981/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496865267/500000000 : ℝ)) (y := (917622981/1000000000 : ℝ)) (X := (4320670126129/5000000000000 : ℝ)) (Y := (6793307774343/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (382270703/200000000 : ℝ)) (τ := (917622981/1000000000 : ℝ)) (σ := (496865267/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (19516109/20679092 : ℝ) ^ p + (816467681/827163680 : ℝ) ^ p := by
    exact cert_lt (x := (19516109/20679092 : ℝ)) (y := (816467681/827163680 : ℝ)) (X := (6520212097247/25000000000000 : ℝ)) (Y := (36959576537741/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (917622981/1000000000 : ℝ)) (n' := (5169773/6250000 : ℝ)) (Ab := (19516109/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (461659987/500000000 : ℝ) ^ p + (248169573/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (461659987/500000000 : ℝ)) (y := (248169573/250000000 : ℝ)) (X := (392158935047/2500000000000 : ℝ)) (Y := (84313658574987/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248169573/250000000 : ℝ) ^ p + (461659987/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248169573/250000000 : ℝ)) (y := (461659987/500000000 : ℝ)) (X := (84313658574987/100000000000000 : ℝ)) (Y := (392158935047/2500000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957999133/500000000 : ℝ)) (τ := (461659987/500000000 : ℝ)) (σ := (248169573/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (393391903/416960509 : ℝ) ^ p + (823225019/833921018 : ℝ) ^ p := by
    exact cert_lt (x := (393391903/416960509 : ℝ)) (y := (823225019/833921018 : ℝ)) (X := (25898441200267/100000000000000 : ℝ)) (Y := (74101559924047/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (461659987/500000000 : ℝ)) (n' := (416960509/500000000 : ℝ)) (Ab := (393391903/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (923574449/1000000000 : ℝ) ^ p + (496313603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (923574449/1000000000 : ℝ)) (y := (496313603/500000000 : ℝ)) (X := (15787046889349/100000000000000 : ℝ)) (Y := (84212969611703/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496313603/500000000 : ℝ) ^ p + (923574449/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496313603/500000000 : ℝ)) (y := (923574449/1000000000 : ℝ)) (X := (84212969611703/100000000000000 : ℝ)) (Y := (15787046889349/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (383240331/200000000 : ℝ)) (τ := (923574449/1000000000 : ℝ)) (σ := (496313603/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (787057129/834221904 : ℝ) ^ p + (274508635/278073968 : ℝ) ^ p := by
    exact cert_lt (x := (787057129/834221904 : ℝ)) (y := (274508635/278073968 : ℝ)) (X := (25890377883477/100000000000000 : ℝ)) (Y := (74109623208497/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (923574449/1000000000 : ℝ)) (n' := (52138869/62500000 : ℝ)) (Ab := (787057129/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (184717139/200000000 : ℝ) ^ p + (49631247/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (184717139/200000000 : ℝ)) (y := (49631247/50000000 : ℝ)) (X := (197393886177/1250000000000 : ℝ)) (Y := (42104253030179/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49631247/50000000 : ℝ) ^ p + (184717139/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (49631247/50000000 : ℝ)) (y := (184717139/200000000 : ℝ)) (X := (42104253030179/50000000000000 : ℝ)) (Y := (197393886177/1250000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (383242127/200000000 : ℝ)) (τ := (184717139/200000000 : ℝ)) (σ := (49631247/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (112438458/119176457 : ℝ) ^ p + (823539200/834235199 : ℝ) ^ p := by
    exact cert_lt (x := (112438458/119176457 : ℝ)) (y := (823539200/834235199 : ℝ)) (X := (25890021712201/100000000000000 : ℝ)) (Y := (9263747422417/12500000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (184717139/200000000 : ℝ)) (n' := (834235199/1000000000 : ℝ)) (Ab := (393534603/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (57724137/62500000 : ℝ) ^ p + (24815621/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (57724137/62500000 : ℝ)) (y := (24815621/25000000 : ℝ)) (X := (15421590041/97656250000 : ℝ)) (Y := (5263019317891/6250000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (24815621/25000000 : ℝ) ^ p + (57724137/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (24815621/25000000 : ℝ)) (y := (57724137/62500000 : ℝ)) (X := (5263019317891/6250000000000 : ℝ)) (Y := (15421590041/97656250000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239526379/125000000 : ℝ)) (τ := (57724137/62500000 : ℝ)) (σ := (24815621/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (787069740/834235787 : ℝ) ^ p + (823539788/834235787 : ℝ) ^ p := by
    exact cert_lt (x := (787069740/834235787 : ℝ)) (y := (823539788/834235787 : ℝ)) (X := (25890005859827/100000000000000 : ℝ)) (Y := (37054997565767/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (57724137/62500000 : ℝ)) (n' := (834235787/1000000000 : ℝ)) (Ab := (39353487/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461793107/500000000 : ℝ) ^ p + (198524967/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (461793107/500000000 : ℝ)) (y := (198524967/200000000 : ℝ)) (X := (7895858467993/50000000000000 : ℝ)) (Y := (42104149618781/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198524967/200000000 : ℝ) ^ p + (461793107/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198524967/200000000 : ℝ)) (y := (461793107/500000000 : ℝ)) (X := (42104149618781/50000000000000 : ℝ)) (Y := (7895858467993/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1916211049/1000000000 : ℝ)) (τ := (461793107/500000000 : ℝ)) (σ := (198524967/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (787069764/834235813 : ℝ) ^ p + (823539814/834235813 : ℝ) ^ p := by
    exact cert_lt (x := (787069764/834235813 : ℝ)) (y := (823539814/834235813 : ℝ)) (X := (1035600218201/4000000000000 : ℝ)) (Y := (74109995828059/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461793107/500000000 : ℝ)) (n' := (834235813/1000000000 : ℝ)) (Ab := (196767441/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (184717243/200000000 : ℝ) ^ p + (198524967/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (184717243/200000000 : ℝ)) (y := (198524967/200000000 : ℝ)) (X := (15791717332987/100000000000000 : ℝ)) (Y := (42104149618781/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198524967/200000000 : ℝ) ^ p + (184717243/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198524967/200000000 : ℝ)) (y := (184717243/200000000 : ℝ)) (X := (42104149618781/50000000000000 : ℝ)) (Y := (15791717332987/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (38324221/20000000 : ℝ)) (τ := (184717243/200000000 : ℝ)) (σ := (198524967/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (787069765/834235814 : ℝ) ^ p + (823539815/834235814 : ℝ) ^ p := by
    exact cert_lt (x := (787069765/834235814 : ℝ)) (y := (823539815/834235814 : ℝ)) (X := (25890005498207/100000000000000 : ℝ)) (Y := (74109995854849/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (184717243/200000000 : ℝ)) (n' := (417117907/500000000 : ℝ)) (Ab := (157413953/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (38324221/20000000 : ℝ)) (τ := (184717243/200000000 : ℝ)) (σ := (198524967/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (184717243/200000000 : ℝ)) (n' := (417117907/500000000 : ℝ)) (Ab := (157413953/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (38324221/20000000 : ℝ)) (τ := (184717243/200000000 : ℝ)) (σ := (198524967/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (184717243/200000000 : ℝ)) (n' := (417117907/500000000 : ℝ)) (Ab := (157413953/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (38324221/20000000 : ℝ)) (τ := (184717243/200000000 : ℝ)) (σ := (198524967/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (184717243/200000000 : ℝ)) (n' := (417117907/500000000 : ℝ)) (Ab := (157413953/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (38324221/20000000 : ℝ)) (τ := (184717243/200000000 : ℝ)) (σ := (198524967/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1654085457/1806737381 : ℝ) ^ p + (1796041382/1806737381 : ℝ) ^ p := by
    exact cert_lt (x := (1654085457/1806737381 : ℝ)) (y := (1796041382/1806737381 : ℝ)) (X := (402448938939/3125000000000 : ℝ)) (Y := (43560817092669/50000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1110555253/1193262619 : ℝ) ^ p + (1182566620/1193262619 : ℝ) ^ p := by
    exact cert_lt (x := (1110555253/1193262619 : ℝ)) (y := (1182566620/1193262619 : ℝ)) (X := (18865616712551/100000000000000 : ℝ)) (Y := (81134383895029/100000000000000 : ℝ)) 743 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198524967/200000000 : ℝ)) (U := (1193262619/1000000000 : ℝ)) (Ab := (1654085457/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (184717243/200000000 : ℝ)) (σ := (198524967/200000000 : ℝ)) (Ab := (1110555253/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab070
