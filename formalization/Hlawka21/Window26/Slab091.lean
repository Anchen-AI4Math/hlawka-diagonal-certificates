import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 91, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab091 (p : ℝ) (hpa : (507/16 : ℝ) ≤ p) (hpb : p ≤ (127/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1420957505347/112300500000000 : ℝ) (3233251/500000000 : ℝ) (3200000673803/22460100000000 : ℝ) (591/500 : ℝ) (489202587/250000000 : ℝ) (978363043/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (579378999/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(684/625 : ℝ) ≤ X j i ∧ X j i ≤ -(113/200 : ℝ)
      else (2077/2500 : ℝ) ≤ X j i ∧ X j i ≤ (1439/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1420957505347/112300500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3233251/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (47285161/50000000 : ℝ) ^ p + (99415197/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (47285161/50000000 : ℝ)) (y := (99415197/100000000 : ℝ)) (X := (4247731527877/25000000000000 : ℝ)) (Y := (10376136989627/12500000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99415197/100000000 : ℝ) ^ p + (47285161/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (99415197/100000000 : ℝ)) (y := (47285161/50000000 : ℝ)) (X := (10376136989627/12500000000000 : ℝ)) (Y := (4247731527877/25000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193985519/100000000 : ℝ)) (τ := (47285161/50000000 : ℝ)) (σ := (99415197/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (830343521/872119218 : ℝ) ^ p + (432826358/436059609 : ℝ) ^ p := by
    exact cert_lt (x := (830343521/872119218 : ℝ)) (y := (432826358/436059609 : ℝ)) (X := (2104513622087/10000000000000 : ℝ)) (Y := (15790973059363/20000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (47285161/50000000 : ℝ)) (n' := (436059609/500000000 : ℝ)) (Ab := (830343521/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (474383027/500000000 : ℝ) ^ p + (993451497/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474383027/500000000 : ℝ)) (y := (993451497/1000000000 : ℝ)) (X := (9413965970741/50000000000000 : ℝ)) (Y := (16234417907337/20000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993451497/1000000000 : ℝ) ^ p + (474383027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993451497/1000000000 : ℝ)) (y := (474383027/500000000 : ℝ)) (X := (16234417907337/20000000000000 : ℝ)) (Y := (9413965970741/50000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1942217551/1000000000 : ℝ)) (τ := (474383027/500000000 : ℝ)) (σ := (993451497/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (833561492/875596761 : ℝ) ^ p + (869130259/875596761 : ℝ) ^ p := by
    exact cert_lt (x := (833561492/875596761 : ℝ)) (y := (869130259/875596761 : ℝ)) (X := (20970729049829/100000000000000 : ℝ)) (Y := (79029272473591/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (474383027/500000000 : ℝ)) (n' := (875596761/1000000000 : ℝ)) (Ab := (208390373/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (948842199/1000000000 : ℝ) ^ p + (39737319/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (948842199/1000000000 : ℝ)) (y := (39737319/40000000 : ℝ)) (X := (4718991923429/25000000000000 : ℝ)) (Y := (1014050668733/1250000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39737319/40000000 : ℝ) ^ p + (948842199/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39737319/40000000 : ℝ)) (y := (948842199/1000000000 : ℝ)) (X := (1014050668733/1250000000000 : ℝ)) (Y := (4718991923429/25000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (971137587/500000000 : ℝ)) (τ := (948842199/1000000000 : ℝ)) (σ := (39737319/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (833641357/875683074 : ℝ) ^ p + (62086898/62548791 : ℝ) ^ p := by
    exact cert_lt (x := (833641357/875683074 : ℝ)) (y := (62086898/62548791 : ℝ)) (X := (20968888694423/100000000000000 : ℝ)) (Y := (79031112611671/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (948842199/1000000000 : ℝ)) (n' := (437841537/500000000 : ℝ)) (Ab := (833641357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (474422041/500000000 : ℝ) ^ p + (248358129/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (474422041/500000000 : ℝ)) (y := (248358129/250000000 : ℝ)) (X := (18877157078929/100000000000000 : ℝ)) (Y := (20280715862713/25000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248358129/250000000 : ℝ) ^ p + (474422041/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248358129/250000000 : ℝ)) (y := (474422041/500000000 : ℝ)) (X := (20280715862713/25000000000000 : ℝ)) (Y := (18877157078929/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (971138299/500000000 : ℝ)) (τ := (474422041/500000000 : ℝ)) (σ := (248358129/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (833643331/875685208 : ℝ) ^ p + (434609353/437842604 : ℝ) ^ p := by
    exact cert_lt (x := (833643331/875685208 : ℝ)) (y := (434609353/437842604 : ℝ)) (X := (20968842737037/100000000000000 : ℝ)) (Y := (79031158103119/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (474422041/500000000 : ℝ)) (n' := (109460651/125000000 : ℝ)) (Ab := (833643331/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (29651379/31250000 : ℝ) ^ p + (198686501/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (29651379/31250000 : ℝ)) (y := (198686501/200000000 : ℝ)) (X := (377543722709/2000000000000 : ℝ)) (Y := (20280708732849/25000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198686501/200000000 : ℝ) ^ p + (29651379/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (198686501/200000000 : ℝ)) (y := (29651379/31250000 : ℝ)) (X := (20280708732849/25000000000000 : ℝ)) (Y := (377543722709/2000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1942276633/1000000000 : ℝ)) (τ := (29651379/31250000 : ℝ)) (σ := (198686501/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (41682169/43784263 : ℝ) ^ p + (434609379/437842630 : ℝ) ^ p := by
    exact cert_lt (x := (41682169/43784263 : ℝ)) (y := (434609379/437842630 : ℝ)) (X := (20968842334961/100000000000000 : ℝ)) (Y := (632249273693/800000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (29651379/31250000 : ℝ)) (n' := (43784263/50000000 : ℝ)) (Ab := (41682169/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (94884413/100000000 : ℝ) ^ p + (124179063/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (94884413/100000000 : ℝ)) (y := (124179063/125000000 : ℝ)) (X := (9438593699389/50000000000000 : ℝ)) (Y := (81122832338719/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124179063/125000000 : ℝ) ^ p + (94884413/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (124179063/125000000 : ℝ)) (y := (94884413/100000000 : ℝ)) (X := (81122832338719/100000000000000 : ℝ)) (Y := (9438593699389/50000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (971138317/500000000 : ℝ)) (τ := (94884413/100000000 : ℝ)) (σ := (124179063/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (833643382/875685263 : ℝ) ^ p + (869218761/875685263 : ℝ) ^ p := by
    exact cert_lt (x := (833643382/875685263 : ℝ)) (y := (869218761/875685263 : ℝ)) (X := (2096884165137/10000000000000 : ℝ)) (Y := (79031159275577/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (94884413/100000000 : ℝ)) (n' := (875685263/1000000000 : ℝ)) (Ab := (416821691/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (971138317/500000000 : ℝ)) (τ := (94884413/100000000 : ℝ)) (σ := (124179063/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (94884413/100000000 : ℝ)) (n' := (875685263/1000000000 : ℝ)) (Ab := (416821691/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (971138317/500000000 : ℝ)) (τ := (94884413/100000000 : ℝ)) (σ := (124179063/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (94884413/100000000 : ℝ)) (n' := (875685263/1000000000 : ℝ)) (Ab := (416821691/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (971138317/500000000 : ℝ)) (τ := (94884413/100000000 : ℝ)) (σ := (124179063/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (94884413/100000000 : ℝ)) (n' := (875685263/1000000000 : ℝ)) (Ab := (416821691/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (971138317/500000000 : ℝ)) (τ := (94884413/100000000 : ℝ)) (σ := (124179063/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (94884413/100000000 : ℝ)) (n' := (875685263/1000000000 : ℝ)) (Ab := (416821691/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (971138317/500000000 : ℝ)) (τ := (94884413/100000000 : ℝ)) (σ := (124179063/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (857712710/920621001 : ℝ) ^ p + (917387750/920621001 : ℝ) ^ p := by
    exact cert_lt (x := (857712710/920621001 : ℝ)) (y := (917387750/920621001 : ℝ)) (X := (10569044691747/100000000000000 : ℝ)) (Y := (89430955620597/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (364788167/386252666 : ℝ) ^ p + (576145748/579378999 : ℝ) ^ p := by
    exact cert_lt (x := (364788167/386252666 : ℝ)) (y := (576145748/579378999 : ℝ)) (X := (1017428209207/6250000000000 : ℝ)) (Y := (83721149261793/100000000000000 : ℝ)) 127 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124179063/125000000 : ℝ)) (U := (579378999/500000000 : ℝ)) (Ab := (85771271/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (94884413/100000000 : ℝ)) (σ := (124179063/125000000 : ℝ)) (Ab := (1094364501/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab091
