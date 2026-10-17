import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 103, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab103 (p : ℝ) (hpa : (775/32 : ℝ) ≤ p) (hpb : p ≤ (97/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (16731980287/846300000000 : ℝ) (5086191/500000000 : ℝ) (160000025389/846300000000 : ℝ) (3033/2500 : ℝ) (242955313/125000000 : ℝ) (971785409/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238736449/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11141/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2307/5000 : ℝ)
      else (7763/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2963/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (16731980287/846300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5086191/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (3685217/4000000 : ℝ) ^ p + (24848543/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (3685217/4000000 : ℝ)) (y := (24848543/25000000 : ℝ)) (X := (13701703286443/100000000000000 : ℝ)) (Y := (17259662939563/20000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (24848543/25000000 : ℝ) ^ p + (3685217/4000000 : ℝ) ^ p := by
    exact cert_lt (x := (24848543/25000000 : ℝ)) (y := (3685217/4000000 : ℝ)) (X := (17259662939563/20000000000000 : ℝ)) (Y := (13701703286443/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (191524597/100000000 : ℝ)) (τ := (3685217/4000000 : ℝ)) (σ := (24848543/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (130915409/138430584 : ℝ) ^ p + (136735187/138430584 : ℝ) ^ p := by
    exact cert_lt (x := (130915409/138430584 : ℝ)) (y := (136735187/138430584 : ℝ)) (X := (25831454344903/100000000000000 : ℝ)) (Y := (18542136613419/25000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (3685217/4000000 : ℝ)) (n' := (51911469/62500000 : ℝ)) (Ab := (392746227/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (231714843/250000000 : ℝ) ^ p + (992908007/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231714843/250000000 : ℝ)) (y := (992908007/1000000000 : ℝ)) (X := (15852061843717/100000000000000 : ℝ)) (Y := (42073977291967/50000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992908007/1000000000 : ℝ) ^ p + (231714843/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992908007/1000000000 : ℝ)) (y := (231714843/250000000 : ℝ)) (X := (42073977291967/50000000000000 : ℝ)) (Y := (15852061843717/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1919767379/1000000000 : ℝ)) (τ := (231714843/250000000 : ℝ)) (σ := (992908007/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (791469104/837137599 : ℝ) ^ p + (826965217/837137599 : ℝ) ^ p := by
    exact cert_lt (x := (791469104/837137599 : ℝ)) (y := (826965217/837137599 : ℝ)) (X := (25656659739447/100000000000000 : ℝ)) (Y := (74343341327477/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (231714843/250000000 : ℝ)) (n' := (837137599/1000000000 : ℝ)) (Ab := (49466819/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (927093057/1000000000 : ℝ) ^ p + (992860683/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927093057/1000000000 : ℝ)) (y := (992860683/1000000000 : ℝ)) (X := (7974633343701/50000000000000 : ℝ)) (Y := (84050749914431/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992860683/1000000000 : ℝ) ^ p + (927093057/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992860683/1000000000 : ℝ)) (y := (927093057/1000000000 : ℝ)) (X := (84050749914431/100000000000000 : ℝ)) (Y := (7974633343701/50000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (95997687/50000000 : ℝ)) (τ := (927093057/1000000000 : ℝ)) (σ := (992860683/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (395859854/418706231 : ℝ) ^ p + (413620040/418706231 : ℝ) ^ p := by
    exact cert_lt (x := (395859854/418706231 : ℝ)) (y := (413620040/418706231 : ℝ)) (X := (25649380407559/100000000000000 : ℝ)) (Y := (3717531028747/5000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (927093057/1000000000 : ℝ)) (n' := (418706231/500000000 : ℝ)) (Ab := (197929927/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (463551393/500000000 : ℝ) ^ p + (496429353/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (463551393/500000000 : ℝ)) (y := (496429353/500000000 : ℝ)) (X := (15953325979653/100000000000000 : ℝ)) (Y := (10505836431373/12500000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496429353/500000000 : ℝ) ^ p + (463551393/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496429353/500000000 : ℝ)) (y := (463551393/500000000 : ℝ)) (X := (10505836431373/12500000000000 : ℝ)) (Y := (15953325979653/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (479990373/250000000 : ℝ)) (τ := (463551393/500000000 : ℝ)) (σ := (496429353/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (197932535/209355976 : ℝ) ^ p + (413625761/418711952 : ℝ) ^ p := by
    exact cert_lt (x := (197932535/209355976 : ℝ)) (y := (413625761/418711952 : ℝ)) (X := (3206134676901/12500000000000 : ℝ)) (Y := (14870184701349/20000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (463551393/500000000 : ℝ)) (n' := (26169497/31250000 : ℝ)) (Ab := (39586507/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (92710319/100000000 : ℝ) ^ p + (1939177/1953125 : ℝ) ^ p := by
    exact cert_lt (x := (92710319/100000000 : ℝ)) (y := (1939177/1953125 : ℝ)) (X := (15953494564549/100000000000000 : ℝ)) (Y := (84046523122213/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (1939177/1953125 : ℝ) ^ p + (92710319/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (1939177/1953125 : ℝ)) (y := (92710319/100000000 : ℝ)) (X := (84046523122213/100000000000000 : ℝ)) (Y := (15953494564549/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (959980907/500000000 : ℝ)) (τ := (92710319/100000000 : ℝ)) (σ := (1939177/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (791730573/837424379 : ℝ) ^ p + (75204727/76129489 : ℝ) ^ p := by
    exact cert_lt (x := (791730573/837424379 : ℝ)) (y := (75204727/76129489 : ℝ)) (X := (1603066548827/6250000000000 : ℝ)) (Y := (37175468041209/50000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (92710319/100000000 : ℝ)) (n' := (837424379/1000000000 : ℝ)) (Ab := (791730573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (115887901/125000000 : ℝ) ^ p + (49642931/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (115887901/125000000 : ℝ)) (y := (49642931/50000000 : ℝ)) (X := (15953502075797/100000000000000 : ℝ)) (Y := (42023257455531/50000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (49642931/50000000 : ℝ) ^ p + (115887901/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (49642931/50000000 : ℝ)) (y := (115887901/125000000 : ℝ)) (X := (42023257455531/50000000000000 : ℝ)) (Y := (15953502075797/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (479990457/250000000 : ℝ)) (τ := (115887901/125000000 : ℝ)) (σ := (49642931/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (791730593/837424400 : ℝ) ^ p + (413626009/418712200 : ℝ) ^ p := by
    exact cert_lt (x := (791730593/837424400 : ℝ)) (y := (413626009/418712200 : ℝ)) (X := (1282453244791/5000000000000 : ℝ)) (Y := (14870187327679/20000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (115887901/125000000 : ℝ)) (n' := (2093561/2500000 : ℝ)) (Ab := (791730593/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (479990457/250000000 : ℝ)) (τ := (115887901/125000000 : ℝ)) (σ := (49642931/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115887901/125000000 : ℝ)) (n' := (2093561/2500000 : ℝ)) (Ab := (791730593/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (479990457/250000000 : ℝ)) (τ := (115887901/125000000 : ℝ)) (σ := (49642931/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115887901/125000000 : ℝ)) (n' := (2093561/2500000 : ℝ)) (Ab := (791730593/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (479990457/250000000 : ℝ)) (τ := (115887901/125000000 : ℝ)) (σ := (49642931/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115887901/125000000 : ℝ)) (n' := (2093561/2500000 : ℝ)) (Ab := (791730593/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (479990457/250000000 : ℝ)) (τ := (115887901/125000000 : ℝ)) (σ := (49642931/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115887901/125000000 : ℝ)) (n' := (2093561/2500000 : ℝ)) (Ab := (791730593/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (479990457/250000000 : ℝ)) (τ := (115887901/125000000 : ℝ)) (σ := (49642931/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (331899258/361263551 : ℝ) ^ p + (163285943/164210705 : ℝ) ^ p := by
    exact cert_lt (x := (331899258/361263551 : ℝ)) (y := (163285943/164210705 : ℝ)) (X := (3199681742383/25000000000000 : ℝ)) (Y := (87201273334231/100000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (222808484/238736449 : ℝ) ^ p + (1183509863/1193682245 : ℝ) ^ p := by
    exact cert_lt (x := (222808484/238736449 : ℝ)) (y := (1183509863/1193682245 : ℝ)) (X := (18741964080393/100000000000000 : ℝ)) (Y := (40629018294689/50000000000000 : ℝ)) 97 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (49642931/50000000 : ℝ)) (U := (238736449/200000000 : ℝ)) (Ab := (165949629/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115887901/125000000 : ℝ)) (σ := (49642931/50000000 : ℝ)) (Ab := (55702121/50000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab103
