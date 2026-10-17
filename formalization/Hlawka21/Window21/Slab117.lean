import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 117, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab117 (p : ℝ) (hpa : (789/32 : ℝ) ≤ p) (hpb : p ≤ (395/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (41739431971/2153970000000 : ℝ) (9965199/1000000000 : ℝ) (4000000646191/21539700000000 : ℝ) (3033/2500 : ℝ) (243078411/125000000 : ℝ) (243069761/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149232531/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2231/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(4637/10000 : ℝ)
      else (7787/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2371/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (41739431971/2153970000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9965199/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (922768753/1000000000 : ℝ) ^ p + (994027289/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922768753/1000000000 : ℝ)) (y := (994027289/1000000000 : ℝ)) (X := (13747713504401/100000000000000 : ℝ)) (Y := (86252304976317/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994027289/1000000000 : ℝ) ^ p + (922768753/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994027289/1000000000 : ℝ)) (y := (922768753/1000000000 : ℝ)) (X := (86252304976317/100000000000000 : ℝ)) (Y := (13747713504401/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958398021/500000000 : ℝ)) (τ := (922768753/1000000000 : ℝ)) (σ := (994027289/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (393712405/415966223 : ℝ) ^ p + (821967247/831932446 : ℝ) ^ p := by
    exact cert_lt (x := (393712405/415966223 : ℝ)) (y := (821967247/831932446 : ℝ)) (X := (12866427547853/50000000000000 : ℝ)) (Y := (74267146226807/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (922768753/1000000000 : ℝ)) (n' := (415966223/500000000 : ℝ)) (Ab := (78742481/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (464131847/500000000 : ℝ) ^ p + (248250437/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (464131847/500000000 : ℝ)) (y := (248250437/250000000 : ℝ)) (X := (7958969167081/50000000000000 : ℝ)) (Y := (84082079835373/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248250437/250000000 : ℝ) ^ p + (464131847/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248250437/250000000 : ℝ)) (y := (464131847/500000000 : ℝ)) (X := (84082079835373/100000000000000 : ℝ)) (Y := (7958969167081/50000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (960632721/500000000 : ℝ)) (τ := (464131847/500000000 : ℝ)) (σ := (248250437/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (793332913/838401835 : ℝ) ^ p + (828436636/838401835 : ℝ) ^ p := by
    exact cert_lt (x := (793332913/838401835 : ℝ)) (y := (828436636/838401835 : ℝ)) (X := (5112228779069/20000000000000 : ℝ)) (Y := (14887771406119/20000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (464131847/500000000 : ℝ)) (n' := (167680367/200000000 : ℝ)) (Ab := (793332913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (232122317/250000000 : ℝ) ^ p + (248238977/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (232122317/250000000 : ℝ)) (y := (248238977/250000000 : ℝ)) (X := (640548355979/4000000000000 : ℝ)) (Y := (83986308018841/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248238977/250000000 : ℝ) ^ p + (232122317/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248238977/250000000 : ℝ)) (y := (232122317/250000000 : ℝ)) (X := (83986308018841/100000000000000 : ℝ)) (Y := (640548355979/4000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (240180647/125000000 : ℝ)) (τ := (232122317/250000000 : ℝ)) (σ := (248238977/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (793574675/838666608 : ℝ) ^ p + (276233803/279555536 : ℝ) ^ p := by
    exact cert_lt (x := (793574675/838666608 : ℝ)) (y := (276233803/279555536 : ℝ)) (X := (25554164787413/100000000000000 : ℝ)) (Y := (37222918129141/50000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (232122317/250000000 : ℝ)) (n' := (52416663/62500000 : ℝ)) (Ab := (31742987/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (464249217/500000000 : ℝ) ^ p + (992954039/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464249217/500000000 : ℝ)) (y := (992954039/1000000000 : ℝ)) (X := (16017612117279/100000000000000 : ℝ)) (Y := (8398240540789/10000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992954039/1000000000 : ℝ) ^ p + (464249217/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992954039/1000000000 : ℝ)) (y := (464249217/500000000 : ℝ)) (X := (8398240540789/10000000000000 : ℝ)) (Y := (16017612117279/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1921452473/1000000000 : ℝ)) (τ := (464249217/500000000 : ℝ)) (σ := (992954039/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (132264083/139779561 : ℝ) ^ p + (276237389/279559122 : ℝ) ^ p := by
    exact cert_lt (x := (132264083/139779561 : ℝ)) (y := (276237389/279559122 : ℝ)) (X := (2555388131959/10000000000000 : ℝ)) (Y := (14889223950321/20000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (464249217/500000000 : ℝ)) (n' := (419338683/500000000 : ℝ)) (Ab := (396792249/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464249403/500000000 : ℝ) ^ p + (992953963/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464249403/500000000 : ℝ)) (y := (992953963/1000000000 : ℝ)) (X := (16017770547749/100000000000000 : ℝ)) (Y := (83982246717921/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992953963/1000000000 : ℝ) ^ p + (464249403/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992953963/1000000000 : ℝ)) (y := (464249403/500000000 : ℝ)) (X := (83982246717921/100000000000000 : ℝ)) (Y := (16017770547749/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1921452769/1000000000 : ℝ)) (τ := (464249403/500000000 : ℝ)) (σ := (992953963/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (396792448/419338901 : ℝ) ^ p + (828712603/838677802 : ℝ) ^ p := by
    exact cert_lt (x := (396792448/419338901 : ℝ)) (y := (828712603/838677802 : ℝ)) (X := (12776934873447/50000000000000 : ℝ)) (Y := (14889226248177/20000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464249403/500000000 : ℝ)) (n' := (419338901/500000000 : ℝ)) (Ab := (3099941/3906250 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (928498821/1000000000 : ℝ) ^ p + (24823849/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (928498821/1000000000 : ℝ)) (y := (24823849/25000000 : ℝ)) (X := (8008888468053/50000000000000 : ℝ)) (Y := (1679644809077/2000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (24823849/25000000 : ℝ) ^ p + (928498821/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24823849/25000000 : ℝ)) (y := (928498821/1000000000 : ℝ)) (X := (1679644809077/2000000000000 : ℝ)) (Y := (8008888468053/50000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921452781/1000000000 : ℝ)) (τ := (928498821/1000000000 : ℝ)) (σ := (24823849/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (793584913/838677820 : ℝ) ^ p + (828712621/838677820 : ℝ) ^ p := by
    exact cert_lt (x := (793584913/838677820 : ℝ)) (y := (828712621/838677820 : ℝ)) (X := (25553869721297/100000000000000 : ℝ)) (Y := (74446131715213/100000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (928498821/1000000000 : ℝ)) (n' := (41933891/50000000 : ℝ)) (Ab := (793584913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1921452781/1000000000 : ℝ)) (τ := (928498821/1000000000 : ℝ)) (σ := (24823849/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (928498821/1000000000 : ℝ)) (n' := (41933891/50000000 : ℝ)) (Ab := (793584913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1921452781/1000000000 : ℝ)) (τ := (928498821/1000000000 : ℝ)) (σ := (24823849/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (928498821/1000000000 : ℝ)) (n' := (41933891/50000000 : ℝ)) (Ab := (793584913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1921452781/1000000000 : ℝ)) (τ := (928498821/1000000000 : ℝ)) (σ := (24823849/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (928498821/1000000000 : ℝ)) (n' := (41933891/50000000 : ℝ)) (Ab := (793584913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1921452781/1000000000 : ℝ)) (τ := (928498821/1000000000 : ℝ)) (σ := (24823849/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (928498821/1000000000 : ℝ)) (n' := (41933891/50000000 : ℝ)) (Ab := (793584913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1921452781/1000000000 : ℝ)) (τ := (928498821/1000000000 : ℝ)) (σ := (24823849/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1661660729/1806139752 : ℝ) ^ p + (598724851/602046584 : ℝ) ^ p := by
    exact cert_lt (x := (1661660729/1806139752 : ℝ)) (y := (598724851/602046584 : ℝ)) (X := (12767046211071/100000000000000 : ℝ)) (Y := (21808238497689/25000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1115453441/1193860248 : ℝ) ^ p + (394631683/397953416 : ℝ) ^ p := by
    exact cert_lt (x := (1115453441/1193860248 : ℝ)) (y := (394631683/397953416 : ℝ)) (X := (4673134634143/25000000000000 : ℝ)) (Y := (40653731090913/50000000000000 : ℝ)) 395 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (24823849/25000000 : ℝ)) (U := (149232531/125000000 : ℝ)) (Ab := (1661660729/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (928498821/1000000000 : ℝ)) (σ := (24823849/25000000 : ℝ)) (Ab := (1115453441/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab117
