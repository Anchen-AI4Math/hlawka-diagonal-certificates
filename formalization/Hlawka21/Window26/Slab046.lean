import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 46, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab046 (p : ℝ) (hpa : (231/8 : ℝ) ≤ p) (hpb : p ≤ (463/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (718210592261/51166500000000 : ℝ) (7188883/1000000000 : ℝ) (1600000306999/10233300000000 : ℝ) (591/500 : ℝ) (122041419/62500000 : ℝ) (976280733/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157166419/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5437/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(348/625 : ℝ)
      else (8223/10000 : ℝ) ≤ X j i ∧ X j i ≤ (1149/1000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (718210592261/51166500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7188883/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (37606859/40000000 : ℝ) ^ p + (124209293/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (37606859/40000000 : ℝ)) (y := (124209293/125000000 : ℝ)) (X := (4193914865949/25000000000000 : ℝ)) (Y := (20806090363121/25000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124209293/125000000 : ℝ) ^ p + (37606859/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (124209293/125000000 : ℝ)) (y := (37606859/40000000 : ℝ)) (X := (20806090363121/25000000000000 : ℝ)) (Y := (4193914865949/25000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1933845819/1000000000 : ℝ)) (τ := (37606859/40000000 : ℝ)) (σ := (124209293/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (411350141/433864449 : ℝ) ^ p + (860540015/867728898 : ℝ) ^ p := by
    exact cert_lt (x := (411350141/433864449 : ℝ)) (y := (860540015/867728898 : ℝ)) (X := (2139520098041/10000000000000 : ℝ)) (Y := (78604799794477/100000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (37606859/40000000 : ℝ)) (n' := (433864449/500000000 : ℝ)) (Ab := (411350141/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (235863147/250000000 : ℝ) ^ p + (124116559/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (235863147/250000000 : ℝ)) (y := (124116559/125000000 : ℝ)) (X := (9277529058681/50000000000000 : ℝ)) (Y := (40722480125783/50000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124116559/125000000 : ℝ) ^ p + (235863147/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124116559/125000000 : ℝ)) (y := (235863147/250000000 : ℝ)) (X := (40722480125783/50000000000000 : ℝ)) (Y := (9277529058681/50000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (96819253/50000000 : ℝ)) (τ := (235863147/250000000 : ℝ)) (σ := (124116559/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (826152351/871485476 : ℝ) ^ p + (864296593/871485476 : ℝ) ^ p := by
    exact cert_lt (x := (826152351/871485476 : ℝ)) (y := (864296593/871485476 : ℝ)) (X := (5328312686311/25000000000000 : ℝ)) (Y := (15737350041587/20000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (235863147/250000000 : ℝ)) (n' := (217871369/250000000 : ℝ)) (Ab := (826152351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (943544357/1000000000 : ℝ) ^ p + (31028451/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (943544357/1000000000 : ℝ)) (y := (31028451/31250000 : ℝ)) (X := (18607356643549/100000000000000 : ℝ)) (Y := (40696331284301/50000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31028451/31250000 : ℝ) ^ p + (943544357/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31028451/31250000 : ℝ)) (y := (943544357/1000000000 : ℝ)) (X := (40696331284301/50000000000000 : ℝ)) (Y := (18607356643549/100000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1936454789/1000000000 : ℝ)) (τ := (943544357/1000000000 : ℝ)) (σ := (31028451/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (275416241/290530119 : ℝ) ^ p + (864401474/871590357 : ℝ) ^ p := by
    exact cert_lt (x := (275416241/290530119 : ℝ)) (y := (864401474/871590357 : ℝ)) (X := (21310971757109/100000000000000 : ℝ)) (Y := (7868902924667/10000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (943544357/1000000000 : ℝ)) (n' := (871590357/1000000000 : ℝ)) (Ab := (826248723/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (943546909/1000000000 : ℝ) ^ p + (496454909/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (943546909/1000000000 : ℝ)) (y := (496454909/500000000 : ℝ)) (X := (18608813042799/100000000000000 : ℝ)) (Y := (40695603050531/50000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496454909/500000000 : ℝ) ^ p + (943546909/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496454909/500000000 : ℝ)) (y := (943546909/1000000000 : ℝ)) (X := (40695603050531/50000000000000 : ℝ)) (Y := (18608813042799/100000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1936456727/1000000000 : ℝ)) (τ := (943546909/1000000000 : ℝ)) (σ := (496454909/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (826251403/871593273 : ℝ) ^ p + (864404390/871593273 : ℝ) ^ p := by
    exact cert_lt (x := (826251403/871593273 : ℝ)) (y := (864404390/871593273 : ℝ)) (X := (5327727208763/25000000000000 : ℝ)) (Y := (39344546301859/50000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (943546909/1000000000 : ℝ)) (n' := (871593273/1000000000 : ℝ)) (Ab := (826251403/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (47177349/50000000 : ℝ) ^ p + (992909801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (47177349/50000000 : ℝ)) (y := (992909801/1000000000 : ℝ)) (X := (18608853563317/100000000000000 : ℝ)) (Y := (20347791443943/25000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992909801/1000000000 : ℝ) ^ p + (47177349/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992909801/1000000000 : ℝ)) (y := (47177349/50000000 : ℝ)) (X := (20347791443943/25000000000000 : ℝ)) (Y := (18608853563317/100000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1936456781/1000000000 : ℝ)) (τ := (47177349/50000000 : ℝ)) (σ := (992909801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (275417159/290531118 : ℝ) ^ p + (864404471/871593354 : ℝ) ^ p := by
    exact cert_lt (x := (275417159/290531118 : ℝ)) (y := (864404471/871593354 : ℝ)) (X := (5327726688877/25000000000000 : ℝ)) (Y := (7868909436363/10000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (47177349/50000000 : ℝ)) (n' := (435796677/500000000 : ℝ)) (Ab := (826251477/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (471773491/500000000 : ℝ) ^ p + (4964549/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (471773491/500000000 : ℝ)) (y := (4964549/5000000 : ℝ)) (X := (9304427352371/50000000000000 : ℝ)) (Y := (5086947712731/6250000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (4964549/5000000 : ℝ) ^ p + (471773491/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (4964549/5000000 : ℝ)) (y := (471773491/500000000 : ℝ)) (X := (5086947712731/6250000000000 : ℝ)) (Y := (9304427352371/50000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (968228391/500000000 : ℝ)) (τ := (471773491/500000000 : ℝ)) (σ := (4964549/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (826251479/871593356 : ℝ) ^ p + (864404473/871593356 : ℝ) ^ p := by
    exact cert_lt (x := (826251479/871593356 : ℝ)) (y := (864404473/871593356 : ℝ)) (X := (10655453416581/50000000000000 : ℝ)) (Y := (15737818881417/20000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (471773491/500000000 : ℝ)) (n' := (217898339/250000000 : ℝ)) (Ab := (826251479/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (968228391/500000000 : ℝ)) (τ := (471773491/500000000 : ℝ)) (σ := (4964549/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (471773491/500000000 : ℝ)) (n' := (217898339/250000000 : ℝ)) (Ab := (826251479/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (968228391/500000000 : ℝ)) (τ := (471773491/500000000 : ℝ)) (σ := (4964549/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (471773491/500000000 : ℝ)) (n' := (217898339/250000000 : ℝ)) (Ab := (826251479/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (968228391/500000000 : ℝ)) (τ := (471773491/500000000 : ℝ)) (σ := (4964549/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (471773491/500000000 : ℝ)) (n' := (217898339/250000000 : ℝ)) (Ab := (826251479/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (968228391/500000000 : ℝ)) (τ := (471773491/500000000 : ℝ)) (σ := (4964549/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (471773491/500000000 : ℝ)) (n' := (217898339/250000000 : ℝ)) (Ab := (826251479/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (968228391/500000000 : ℝ)) (τ := (471773491/500000000 : ℝ)) (σ := (4964549/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1705832643/1842833581 : ℝ) ^ p + (1835644698/1842833581 : ℝ) ^ p := by
    exact cert_lt (x := (1705832643/1842833581 : ℝ)) (y := (1835644698/1842833581 : ℝ)) (X := (2673595243857/25000000000000 : ℝ)) (Y := (17861123857833/20000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1087314231/1157166419 : ℝ) ^ p + (1149977536/1157166419 : ℝ) ^ p := by
    exact cert_lt (x := (1087314231/1157166419 : ℝ)) (y := (1149977536/1157166419 : ℝ)) (X := (16500925562753/100000000000000 : ℝ)) (Y := (16699815043819/20000000000000 : ℝ)) 463 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (4964549/5000000 : ℝ)) (U := (1157166419/1000000000 : ℝ)) (Ab := (1705832643/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (471773491/500000000 : ℝ)) (σ := (4964549/5000000 : ℝ)) (Ab := (1087314231/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab046
