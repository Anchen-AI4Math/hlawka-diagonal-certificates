import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 98, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab098 (p : ℝ) (hpa : (385/16 : ℝ) ≤ p) (hpb : p ≤ (771/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (20931539429/1051050000000 : ℝ) (10248449/1000000000 : ℝ) (400000063063/2102100000000 : ℝ) (3033/2500 : ℝ) (971641127/500000000 : ℝ) (121450603/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (59680931/50000000 : ℝ)) ∧
    (∀ j i, if j = i then -(696/625 : ℝ) ≤ X j i ∧ X j i ≤ -(921/2000 : ℝ)
      else (1551/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11851/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (20931539429/1051050000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10248449/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (9207677/10000000 : ℝ) ^ p + (496955297/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (9207677/10000000 : ℝ)) (y := (496955297/500000000 : ℝ)) (X := (3421219229937/25000000000000 : ℝ)) (Y := (1726302821767/2000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496955297/500000000 : ℝ) ^ p + (9207677/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (496955297/500000000 : ℝ)) (y := (9207677/10000000 : ℝ)) (X := (1726302821767/2000000000000 : ℝ)) (Y := (3421219229937/25000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (957339147/500000000 : ℝ)) (τ := (9207677/10000000 : ℝ)) (σ := (496955297/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784785029/830087641 : ℝ) ^ p + (819839192/830087641 : ℝ) ^ p := by
    exact cert_lt (x := (784785029/830087641 : ℝ)) (y := (819839192/830087641 : ℝ)) (X := (25867668843609/100000000000000 : ℝ)) (Y := (3706616610069/5000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (9207677/10000000 : ℝ)) (n' := (830087641/1000000000 : ℝ)) (Ab := (784785029/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (926344343/1000000000 : ℝ) ^ p + (992874001/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926344343/1000000000 : ℝ)) (y := (992874001/1000000000 : ℝ)) (X := (15827918542819/100000000000000 : ℝ)) (Y := (84172097872851/100000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992874001/1000000000 : ℝ) ^ p + (926344343/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992874001/1000000000 : ℝ)) (y := (926344343/1000000000 : ℝ)) (X := (84172097872851/100000000000000 : ℝ)) (Y := (15827918542819/100000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (239902293/125000000 : ℝ)) (τ := (926344343/1000000000 : ℝ)) (σ := (992874001/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (790786259/836672229 : ℝ) ^ p + (826423780/836672229 : ℝ) ^ p := by
    exact cert_lt (x := (790786259/836672229 : ℝ)) (y := (826423780/836672229 : ℝ)) (X := (12845876042249/50000000000000 : ℝ)) (Y := (74308249362017/100000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (926344343/1000000000 : ℝ)) (n' := (836672229/1000000000 : ℝ)) (Ab := (790786259/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (28955657/31250000 : ℝ) ^ p + (992826131/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28955657/31250000 : ℝ)) (y := (992826131/1000000000 : ℝ)) (X := (7962821237773/50000000000000 : ℝ)) (Y := (42037187066381/50000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992826131/1000000000 : ℝ) ^ p + (28955657/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (992826131/1000000000 : ℝ)) (y := (28955657/31250000 : ℝ)) (X := (42037187066381/50000000000000 : ℝ)) (Y := (7962821237773/50000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (383881431/200000000 : ℝ)) (τ := (28955657/31250000 : ℝ)) (σ := (992826131/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (60849241/64380833 : ℝ) ^ p + (826702380/836950829 : ℝ) ^ p := by
    exact cert_lt (x := (60849241/64380833 : ℝ)) (y := (826702380/836950829 : ℝ)) (X := (25684360950567/100000000000000 : ℝ)) (Y := (74315640284333/100000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (28955657/31250000 : ℝ)) (n' := (836950829/1000000000 : ℝ)) (Ab := (791040133/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (185318193/200000000 : ℝ) ^ p + (992824113/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185318193/200000000 : ℝ)) (y := (992824113/1000000000 : ℝ)) (X := (3982439918583/25000000000000 : ℝ)) (Y := (42035128448139/50000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992824113/1000000000 : ℝ) ^ p + (185318193/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992824113/1000000000 : ℝ)) (y := (185318193/200000000 : ℝ)) (X := (42035128448139/50000000000000 : ℝ)) (Y := (3982439918583/25000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (959707539/500000000 : ℝ)) (τ := (185318193/200000000 : ℝ)) (σ := (992824113/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (791050794/836962529 : ℝ) ^ p + (826714080/836962529 : ℝ) ^ p := by
    exact cert_lt (x := (791050794/836962529 : ℝ)) (y := (826714080/836962529 : ℝ)) (X := (5136810045261/20000000000000 : ℝ)) (Y := (74315950578989/100000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (185318193/200000000 : ℝ)) (n' := (836962529/1000000000 : ℝ)) (Ab := (395525397/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (926591383/1000000000 : ℝ) ^ p + (248206007/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (926591383/1000000000 : ℝ)) (y := (248206007/250000000 : ℝ)) (X := (15929932817/100000000000 : ℝ)) (Y := (21017520869691/25000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248206007/250000000 : ℝ) ^ p + (926591383/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248206007/250000000 : ℝ)) (y := (926591383/1000000000 : ℝ)) (X := (21017520869691/25000000000000 : ℝ)) (Y := (15929932817/100000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1919415411/1000000000 : ℝ)) (τ := (926591383/1000000000 : ℝ)) (σ := (248206007/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (791051243/836963021 : ℝ) ^ p + (826714572/836963021 : ℝ) ^ p := by
    exact cert_lt (x := (791051243/836963021 : ℝ)) (y := (826714572/836963021 : ℝ)) (X := (12842018850499/50000000000000 : ℝ)) (Y := (37157981813557/50000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (926591383/1000000000 : ℝ)) (n' := (836963021/1000000000 : ℝ)) (Ab := (791051243/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (4632957/5000000 : ℝ) ^ p + (39712961/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (4632957/5000000 : ℝ)) (y := (39712961/40000000 : ℝ)) (X := (7964969929363/50000000000000 : ℝ)) (Y := (10508759669769/12500000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (39712961/40000000 : ℝ) ^ p + (4632957/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (39712961/40000000 : ℝ)) (y := (4632957/5000000 : ℝ)) (X := (10508759669769/12500000000000 : ℝ)) (Y := (7964969929363/50000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (76776617/40000000 : ℝ)) (τ := (4632957/5000000 : ℝ)) (σ := (39712961/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (791051261/836963041 : ℝ) ^ p + (826714592/836963041 : ℝ) ^ p := by
    exact cert_lt (x := (791051261/836963041 : ℝ)) (y := (826714592/836963041 : ℝ)) (X := (25684036994679/100000000000000 : ℝ)) (Y := (2972638566301/4000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (4632957/5000000 : ℝ)) (n' := (836963041/1000000000 : ℝ)) (Ab := (791051261/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (76776617/40000000 : ℝ)) (τ := (4632957/5000000 : ℝ)) (σ := (39712961/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (4632957/5000000 : ℝ)) (n' := (836963041/1000000000 : ℝ)) (Ab := (791051261/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (76776617/40000000 : ℝ)) (τ := (4632957/5000000 : ℝ)) (σ := (39712961/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (4632957/5000000 : ℝ)) (n' := (836963041/1000000000 : ℝ)) (Ab := (791051261/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (76776617/40000000 : ℝ)) (τ := (4632957/5000000 : ℝ)) (σ := (39712961/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (4632957/5000000 : ℝ)) (n' := (836963041/1000000000 : ℝ)) (Ab := (791051261/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (76776617/40000000 : ℝ)) (τ := (4632957/5000000 : ℝ)) (σ := (39712961/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (4632957/5000000 : ℝ)) (n' := (836963041/1000000000 : ℝ)) (Ab := (791051261/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (76776617/40000000 : ℝ)) (τ := (4632957/5000000 : ℝ)) (σ := (39712961/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (414676254/451595345 : ℝ) ^ p + (1796132931/1806381380 : ℝ) ^ p := by
    exact cert_lt (x := (414676254/451595345 : ℝ)) (y := (1796132931/1806381380 : ℝ)) (X := (2562067158853/20000000000000 : ℝ)) (Y := (87189664569657/100000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1113528887/1193618620 : ℝ) ^ p + (1183370171/1193618620 : ℝ) ^ p := by
    exact cert_lt (x := (1113528887/1193618620 : ℝ)) (y := (1183370171/1193618620 : ℝ)) (X := (9380020553557/50000000000000 : ℝ)) (Y := (16247991912289/20000000000000 : ℝ)) 771 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (39712961/40000000 : ℝ)) (U := (59680931/50000000 : ℝ)) (Ab := (207338127/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (4632957/5000000 : ℝ)) (σ := (39712961/40000000 : ℝ)) (Ab := (1113528887/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab098
