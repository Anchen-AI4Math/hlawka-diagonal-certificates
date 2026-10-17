import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 110, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab110 (p : ℝ) (hpa : (391/16 : ℝ) ≤ p) (hpb : p ≤ (783/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1044607400119/53371500000000 : ℝ) (5033871/500000000 : ℝ) (2000000320229/10674300000000 : ℝ) (3033/2500 : ℝ) (486034809/250000000 : ℝ) (194406881/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238754259/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2787/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2313/5000 : ℝ)
      else (311/400 : ℝ) ≤ X j i ∧ X j i ≤ (5927/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1044607400119/53371500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5033871/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (115255419/125000000 : ℝ) ^ p + (198796959/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (115255419/125000000 : ℝ)) (y := (198796959/200000000 : ℝ)) (X := (6862452901447/50000000000000 : ℝ)) (Y := (43137556675067/50000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198796959/200000000 : ℝ) ^ p + (115255419/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (198796959/200000000 : ℝ)) (y := (115255419/125000000 : ℝ)) (X := (43137556675067/50000000000000 : ℝ)) (Y := (6862452901447/50000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1916028147/1000000000 : ℝ)) (τ := (115255419/125000000 : ℝ)) (σ := (198796959/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (262155803/277088368 : ℝ) ^ p + (136866227/138544184 : ℝ) ^ p := by
    exact cert_lt (x := (262155803/277088368 : ℝ)) (y := (136866227/138544184 : ℝ)) (X := (1611353346791/6250000000000 : ℝ)) (Y := (74218347413603/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115255419/125000000 : ℝ)) (n' := (51954069/62500000 : ℝ)) (Ab := (786467409/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185513673/200000000 : ℝ) ^ p + (992955149/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185513673/200000000 : ℝ)) (y := (992955149/1000000000 : ℝ)) (X := (7942654869929/50000000000000 : ℝ)) (Y := (84114707273809/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992955149/1000000000 : ℝ) ^ p + (185513673/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992955149/1000000000 : ℝ)) (y := (185513673/200000000 : ℝ)) (X := (84114707273809/100000000000000 : ℝ)) (Y := (7942654869929/50000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (960261757/500000000 : ℝ)) (τ := (185513673/200000000 : ℝ)) (σ := (992955149/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (396204865/418888359 : ℝ) ^ p + (45983832/46543151 : ℝ) ^ p := by
    exact cert_lt (x := (396204865/418888359 : ℝ)) (y := (45983832/46543151 : ℝ)) (X := (6402102806069/25000000000000 : ℝ)) (Y := (18597897398757/25000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185513673/200000000 : ℝ)) (n' := (418888359/500000000 : ℝ)) (Ab := (79240973/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185559589/200000000 : ℝ) ^ p + (39716343/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (185559589/200000000 : ℝ)) (y := (39716343/40000000 : ℝ)) (X := (15981794215549/100000000000000 : ℝ)) (Y := (84018222537719/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39716343/40000000 : ℝ) ^ p + (185559589/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (39716343/40000000 : ℝ)) (y := (185559589/200000000 : ℝ)) (X := (84018222537719/100000000000000 : ℝ)) (Y := (15981794215549/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (48017663/25000000 : ℝ)) (τ := (185559589/200000000 : ℝ)) (σ := (39716343/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (396327929/419023235 : ℝ) ^ p + (413989364/419023235 : ℝ) ^ p := by
    exact cert_lt (x := (396327929/419023235 : ℝ)) (y := (413989364/419023235 : ℝ)) (X := (1600080287241/6250000000000 : ℝ)) (Y := (37199358295883/50000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185559589/200000000 : ℝ)) (n' := (83804647/100000000 : ℝ)) (Ab := (396327929/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (927807387/1000000000 : ℝ) ^ p + (992906653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927807387/1000000000 : ℝ)) (y := (992906653/1000000000 : ℝ)) (X := (1598577436859/10000000000000 : ℝ)) (Y := (8401424311999/10000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992906653/1000000000 : ℝ) ^ p + (927807387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992906653/1000000000 : ℝ)) (y := (927807387/1000000000 : ℝ)) (X := (8401424311999/10000000000000 : ℝ)) (Y := (1598577436859/10000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (48017851/25000000 : ℝ)) (τ := (927807387/1000000000 : ℝ)) (σ := (992906653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (37745999/39907503 : ℝ) ^ p + (91998869/93117507 : ℝ) ^ p := by
    exact cert_lt (x := (37745999/39907503 : ℝ)) (y := (91998869/93117507 : ℝ)) (X := (25600991262709/100000000000000 : ℝ)) (Y := (74399009590747/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (927807387/1000000000 : ℝ)) (n' := (838057563/1000000000 : ℝ)) (Ab := (792665979/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (37112311/40000000 : ℝ) ^ p + (496453287/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (37112311/40000000 : ℝ)) (y := (496453287/500000000 : ℝ)) (X := (15985937945309/100000000000000 : ℝ)) (Y := (84014079557781/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496453287/500000000 : ℝ) ^ p + (37112311/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496453287/500000000 : ℝ)) (y := (37112311/40000000 : ℝ)) (X := (84014079557781/100000000000000 : ℝ)) (Y := (15985937945309/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1920714349/1000000000 : ℝ)) (τ := (37112311/40000000 : ℝ)) (σ := (496453287/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (792666395/838058019 : ℝ) ^ p + (275996759/279352673 : ℝ) ^ p := by
    exact cert_lt (x := (792666395/838058019 : ℝ)) (y := (275996759/279352673 : ℝ)) (X := (25600979170131/100000000000000 : ℝ)) (Y := (14879804326983/20000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (37112311/40000000 : ℝ)) (n' := (838058019/1000000000 : ℝ)) (Ab := (158533279/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (927807791/1000000000 : ℝ) ^ p + (992906571/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927807791/1000000000 : ℝ)) (y := (992906571/1000000000 : ℝ)) (X := (639437787631/4000000000000 : ℝ)) (Y := (21003518336641/25000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992906571/1000000000 : ℝ) ^ p + (927807791/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992906571/1000000000 : ℝ)) (y := (927807791/1000000000 : ℝ)) (X := (21003518336641/25000000000000 : ℝ)) (Y := (639437787631/4000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (960357181/500000000 : ℝ)) (τ := (927807791/1000000000 : ℝ)) (σ := (992906571/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (792666413/838058038 : ℝ) ^ p + (413995148/419029019 : ℝ) ^ p := by
    exact cert_lt (x := (792666413/838058038 : ℝ)) (y := (413995148/419029019 : ℝ)) (X := (6400244798281/25000000000000 : ℝ)) (Y := (14879804427351/20000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (927807791/1000000000 : ℝ)) (n' := (419029019/500000000 : ℝ)) (Ab := (792666413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (960357181/500000000 : ℝ)) (τ := (927807791/1000000000 : ℝ)) (σ := (992906571/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (927807791/1000000000 : ℝ)) (n' := (419029019/500000000 : ℝ)) (Ab := (792666413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (960357181/500000000 : ℝ)) (τ := (927807791/1000000000 : ℝ)) (σ := (992906571/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (927807791/1000000000 : ℝ)) (n' := (419029019/500000000 : ℝ)) (Ab := (792666413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (960357181/500000000 : ℝ)) (τ := (927807791/1000000000 : ℝ)) (σ := (992906571/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (927807791/1000000000 : ℝ)) (n' := (419029019/500000000 : ℝ)) (Ab := (792666413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (960357181/500000000 : ℝ)) (τ := (927807791/1000000000 : ℝ)) (σ := (992906571/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (927807791/1000000000 : ℝ)) (n' := (419029019/500000000 : ℝ)) (Ab := (792666413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (960357181/500000000 : ℝ)) (τ := (927807791/1000000000 : ℝ)) (σ := (992906571/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1660587796/1806228705 : ℝ) ^ p + (598720321/602076235 : ℝ) ^ p := by
    exact cert_lt (x := (1660587796/1806228705 : ℝ)) (y := (598720321/602076235 : ℝ)) (X := (6391370124853/50000000000000 : ℝ)) (Y := (87217260074417/100000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (123861427/132641255 : ℝ) ^ p + (131522617/132641255 : ℝ) ^ p := by
    exact cert_lt (x := (123861427/132641255 : ℝ)) (y := (131522617/132641255 : ℝ)) (X := (18717039067809/100000000000000 : ℝ)) (Y := (3251318459521/4000000000000 : ℝ)) 783 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992906571/1000000000 : ℝ)) (U := (238754259/200000000 : ℝ)) (Ab := (415146949/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (927807791/1000000000 : ℝ)) (σ := (992906571/1000000000 : ℝ)) (Ab := (1114752843/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab110
