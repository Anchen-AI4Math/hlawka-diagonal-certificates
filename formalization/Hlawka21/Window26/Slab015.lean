import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 15, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab015 (p : ℝ) (hpa : (431/16 : ℝ) ≤ p) (hpb : p ≤ (27 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (724468058519/47733250000000 : ℝ) (194663/25000000 : ℝ) (3200000572799/19093300000000 : ℝ) (591/500 : ℝ) (97465461/50000000 : ℝ) (243649139/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (577981371/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5409/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5499/10000 : ℝ)
      else (8153/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11473/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (724468058519/47733250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (194663/25000000 : ℝ) := by norm_num
  have pc0 : 1 < (187131583/200000000 : ℝ) ^ p + (993298623/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187131583/200000000 : ℝ)) (y := (993298623/1000000000 : ℝ)) (X := (16602044960413/100000000000000 : ℝ)) (Y := (16679594868997/20000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993298623/1000000000 : ℝ) ^ p + (187131583/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993298623/1000000000 : ℝ)) (y := (187131583/200000000 : ℝ)) (X := (16679594868997/20000000000000 : ℝ)) (Y := (16602044960413/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (964478269/500000000 : ℝ)) (τ := (187131583/200000000 : ℝ)) (σ := (993298623/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (408252258/432032387 : ℝ) ^ p + (428139127/432032387 : ℝ) ^ p := by
    exact cert_lt (x := (408252258/432032387 : ℝ)) (y := (428139127/432032387 : ℝ)) (X := (10841811620701/50000000000000 : ℝ)) (Y := (78316377889109/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187131583/200000000 : ℝ)) (n' := (432032387/500000000 : ℝ)) (Ab := (204126129/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (93910049/100000000 : ℝ) ^ p + (248131867/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (93910049/100000000 : ℝ)) (y := (248131867/250000000 : ℝ)) (X := (2291584236313/12500000000000 : ℝ)) (Y := (81667344560993/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248131867/250000000 : ℝ) ^ p + (93910049/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248131867/250000000 : ℝ)) (y := (93910049/100000000 : ℝ)) (X := (81667344560993/100000000000000 : ℝ)) (Y := (2291584236313/12500000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (965813979/500000000 : ℝ)) (τ := (93910049/100000000 : ℝ)) (σ := (248131867/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (820130962/868033115 : ℝ) ^ p + (172049319/173606623 : ℝ) ^ p := by
    exact cert_lt (x := (820130962/868033115 : ℝ)) (y := (172049319/173606623 : ℝ)) (X := (863826808093/4000000000000 : ℝ)) (Y := (78404331214241/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (93910049/100000000 : ℝ)) (n' := (173606623/200000000 : ℝ)) (Ab := (410065481/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (939205829/1000000000 : ℝ) ^ p + (992502431/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939205829/1000000000 : ℝ)) (y := (992502431/1000000000 : ℝ)) (X := (4597069283459/25000000000000 : ℝ)) (Y := (16322348022407/20000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992502431/1000000000 : ℝ) ^ p + (939205829/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992502431/1000000000 : ℝ)) (y := (939205829/1000000000 : ℝ)) (X := (16322348022407/20000000000000 : ℝ)) (Y := (4597069283459/25000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (96585413/50000000 : ℝ)) (τ := (939205829/1000000000 : ℝ)) (σ := (992502431/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (164048342/173630863 : ℝ) ^ p + (24581937/24804409 : ℝ) ^ p := by
    exact cert_lt (x := (164048342/173630863 : ℝ)) (y := (24581937/24804409 : ℝ)) (X := (21592994944001/100000000000000 : ℝ)) (Y := (490043789351/625000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (939205829/1000000000 : ℝ)) (n' := (173630863/200000000 : ℝ)) (Ab := (82024171/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939209033/1000000000 : ℝ) ^ p + (248125417/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (939209033/1000000000 : ℝ)) (y := (248125417/250000000 : ℝ)) (X := (18389970909127/100000000000000 : ℝ)) (Y := (81610046144743/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248125417/250000000 : ℝ) ^ p + (939209033/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248125417/250000000 : ℝ)) (y := (939209033/1000000000 : ℝ)) (X := (81610046144743/100000000000000 : ℝ)) (Y := (18389970909127/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1931710701/1000000000 : ℝ)) (τ := (939209033/1000000000 : ℝ)) (σ := (248125417/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820245078/868158001 : ℝ) ^ p + (860371481/868158001 : ℝ) ^ p := by
    exact cert_lt (x := (820245078/868158001 : ℝ)) (y := (860371481/868158001 : ℝ)) (X := (21592913508237/100000000000000 : ℝ)) (Y := (78407087641873/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939209033/1000000000 : ℝ)) (n' := (868158001/1000000000 : ℝ)) (Ab := (410122539/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (93920913/100000000 : ℝ) ^ p + (198500329/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (93920913/100000000 : ℝ)) (y := (198500329/200000000 : ℝ)) (X := (3678004437987/20000000000000 : ℝ)) (Y := (16321999016407/20000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198500329/200000000 : ℝ) ^ p + (93920913/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198500329/200000000 : ℝ)) (y := (93920913/100000000 : ℝ)) (X := (16321999016407/20000000000000 : ℝ)) (Y := (3678004437987/20000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (77268431/40000000 : ℝ)) (τ := (93920913/100000000 : ℝ)) (σ := (198500329/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (820245179/868158112 : ℝ) ^ p + (107546449/108519764 : ℝ) ^ p := by
    exact cert_lt (x := (820245179/868158112 : ℝ)) (y := (107546449/108519764 : ℝ)) (X := (21592910754699/100000000000000 : ℝ)) (Y := (4900443130719/6250000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (93920913/100000000 : ℝ)) (n' := (27129941/31250000 : ℝ)) (Ab := (820245179/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (469604567/500000000 : ℝ) ^ p + (248125411/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (469604567/500000000 : ℝ)) (y := (248125411/250000000 : ℝ)) (X := (18390024304611/100000000000000 : ℝ)) (Y := (81609992861917/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248125411/250000000 : ℝ) ^ p + (469604567/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248125411/250000000 : ℝ)) (y := (469604567/500000000 : ℝ)) (X := (81609992861917/100000000000000 : ℝ)) (Y := (18390024304611/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (965855389/500000000 : ℝ)) (τ := (469604567/500000000 : ℝ)) (σ := (248125411/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (820245184/868158117 : ℝ) ^ p + (860371597/868158117 : ℝ) ^ p := by
    exact cert_lt (x := (820245184/868158117 : ℝ)) (y := (860371597/868158117 : ℝ)) (X := (10796455475417/50000000000000 : ℝ)) (Y := (78407090201847/100000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (469604567/500000000 : ℝ)) (n' := (868158117/1000000000 : ℝ)) (Ab := (12816331/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (965855389/500000000 : ℝ)) (τ := (469604567/500000000 : ℝ)) (σ := (248125411/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (469604567/500000000 : ℝ)) (n' := (868158117/1000000000 : ℝ)) (Ab := (12816331/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (965855389/500000000 : ℝ)) (τ := (469604567/500000000 : ℝ)) (σ := (248125411/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (469604567/500000000 : ℝ)) (n' := (868158117/1000000000 : ℝ)) (Ab := (12816331/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (965855389/500000000 : ℝ)) (τ := (469604567/500000000 : ℝ)) (σ := (248125411/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (469604567/500000000 : ℝ)) (n' := (868158117/1000000000 : ℝ)) (Ab := (12816331/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (965855389/500000000 : ℝ)) (τ := (469604567/500000000 : ℝ)) (σ := (248125411/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (469604567/500000000 : ℝ)) (n' := (868158117/1000000000 : ℝ)) (Ab := (12816331/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (965855389/500000000 : ℝ)) (τ := (469604567/500000000 : ℝ)) (σ := (248125411/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (40431148/43905649 : ℝ) ^ p + (131160767/131716947 : ℝ) ^ p := by
    exact cert_lt (x := (40431148/43905649 : ℝ)) (y := (131160767/131716947 : ℝ)) (X := (5398251824197/50000000000000 : ℝ)) (Y := (22300874170429/25000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (360591433/385320914 : ℝ) ^ p + (574088111/577981371 : ℝ) ^ p := by
    exact cert_lt (x := (360591433/385320914 : ℝ)) (y := (574088111/577981371 : ℝ)) (X := (2085048806027/12500000000000 : ℝ)) (Y := (41659804985847/50000000000000 : ℝ)) 27 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248125411/250000000 : ℝ)) (U := (577981371/500000000 : ℝ)) (Ab := (212263527/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (469604567/500000000 : ℝ)) (σ := (248125411/250000000 : ℝ)) (Ab := (1081774299/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab015
