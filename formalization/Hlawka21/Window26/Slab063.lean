import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 63, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab063 (p : ℝ) (hpa : (479/16 : ℝ) ≤ p) (hpb : p ≤ (30 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1430240565031/106098500000000 : ℝ) (6898031/1000000000 : ℝ) (3200000636591/21219700000000 : ℝ) (591/500 : ℝ) (977159969/500000000 : ℝ) (195422567/200000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144723591/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5451/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5601/10000 : ℝ)
      else (4129/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11499/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1430240565031/106098500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6898031/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (47119423/50000000 : ℝ) ^ p + (124232933/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (47119423/50000000 : ℝ)) (y := (124232933/125000000 : ℝ)) (X := (8430799949597/50000000000000 : ℝ)) (Y := (83138419899791/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124232933/125000000 : ℝ) ^ p + (47119423/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (124232933/125000000 : ℝ)) (y := (47119423/50000000 : ℝ)) (X := (83138419899791/100000000000000 : ℝ)) (Y := (8430799949597/50000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (484062981/250000000 : ℝ)) (τ := (47119423/50000000 : ℝ)) (σ := (124232933/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (275252254/289833923 : ℝ) ^ p + (862603738/869501769 : ℝ) ^ p := by
    exact cert_lt (x := (275252254/289833923 : ℝ)) (y := (862603738/869501769 : ℝ)) (X := (21254459492811/100000000000000 : ℝ)) (Y := (39372770961101/50000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (47119423/50000000 : ℝ)) (n' := (869501769/1000000000 : ℝ)) (Ab := (412878381/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (945584721/1000000000 : ℝ) ^ p + (496568731/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (945584721/1000000000 : ℝ)) (y := (496568731/500000000 : ℝ)) (X := (18664372118999/100000000000000 : ℝ)) (Y := (81335646839791/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496568731/500000000 : ℝ) ^ p + (945584721/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496568731/500000000 : ℝ)) (y := (945584721/1000000000 : ℝ)) (X := (81335646839791/100000000000000 : ℝ)) (Y := (18664372118999/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1938722183/1000000000 : ℝ)) (τ := (945584721/1000000000 : ℝ)) (σ := (496568731/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (829117634/873148989 : ℝ) ^ p + (866250958/873148989 : ℝ) ^ p := by
    exact cert_lt (x := (829117634/873148989 : ℝ)) (y := (866250958/873148989 : ℝ)) (X := (10587755399477/50000000000000 : ℝ)) (Y := (78824490626241/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (945584721/1000000000 : ℝ)) (n' := (873148989/1000000000 : ℝ)) (Ab := (414558817/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (945670087/1000000000 : ℝ) ^ p + (198623371/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (945670087/1000000000 : ℝ)) (y := (198623371/200000000 : ℝ)) (X := (18714988109561/100000000000000 : ℝ)) (Y := (40642516054713/50000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198623371/200000000 : ℝ) ^ p + (945670087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198623371/200000000 : ℝ)) (y := (945670087/1000000000 : ℝ)) (X := (40642516054713/50000000000000 : ℝ)) (Y := (18714988109561/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (969393471/500000000 : ℝ)) (τ := (945670087/1000000000 : ℝ)) (σ := (198623371/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (207301809/218311558 : ℝ) ^ p + (866348201/873246232 : ℝ) ^ p := by
    exact cert_lt (x := (207301809/218311558 : ℝ)) (y := (866348201/873246232 : ℝ)) (X := (2117341389933/10000000000000 : ℝ)) (Y := (78826587590623/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (945670087/1000000000 : ℝ)) (n' := (109155779/125000000 : ℝ)) (Ab := (207301809/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (236418089/250000000 : ℝ) ^ p + (496558153/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (236418089/250000000 : ℝ)) (y := (496558153/500000000 : ℝ)) (X := (18716335274477/100000000000000 : ℝ)) (Y := (5080230254811/6250000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496558153/500000000 : ℝ) ^ p + (236418089/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496558153/500000000 : ℝ)) (y := (236418089/250000000 : ℝ)) (X := (5080230254811/6250000000000 : ℝ)) (Y := (18716335274477/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (969394331/500000000 : ℝ)) (τ := (236418089/250000000 : ℝ)) (σ := (496558153/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (829209617/873248816 : ℝ) ^ p + (866350785/873248816 : ℝ) ^ p := by
    exact cert_lt (x := (829209617/873248816 : ℝ)) (y := (866350785/873248816 : ℝ)) (X := (21173358219977/100000000000000 : ℝ)) (Y := (39413321653399/50000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (236418089/250000000 : ℝ)) (n' := (54578051/62500000 : ℝ)) (Ab := (829209617/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (189134483/200000000 : ℝ) ^ p + (248279073/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (189134483/200000000 : ℝ)) (y := (248279073/250000000 : ℝ)) (X := (18716370305577/100000000000000 : ℝ)) (Y := (81283649701203/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248279073/250000000 : ℝ) ^ p + (189134483/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248279073/250000000 : ℝ)) (y := (189134483/200000000 : ℝ)) (X := (81283649701203/100000000000000 : ℝ)) (Y := (18716370305577/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1938788707/1000000000 : ℝ)) (τ := (189134483/200000000 : ℝ)) (σ := (248279073/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (276403226/291082961 : ℝ) ^ p + (866350852/873248883 : ℝ) ^ p := by
    exact cert_lt (x := (276403226/291082961 : ℝ)) (y := (866350852/873248883 : ℝ)) (X := (21173356212137/100000000000000 : ℝ)) (Y := (9853330593931/12500000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (189134483/200000000 : ℝ)) (n' := (873248883/1000000000 : ℝ)) (Ab := (414604839/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (945672417/1000000000 : ℝ) ^ p + (993116291/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (945672417/1000000000 : ℝ)) (y := (993116291/1000000000 : ℝ)) (X := (18716371493073/100000000000000 : ℝ)) (Y := (81283647245791/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993116291/1000000000 : ℝ) ^ p + (945672417/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993116291/1000000000 : ℝ)) (y := (945672417/1000000000 : ℝ)) (X := (81283647245791/100000000000000 : ℝ)) (Y := (18716371493073/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (484697177/250000000 : ℝ)) (τ := (945672417/1000000000 : ℝ)) (σ := (993116291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (92134409/97027654 : ℝ) ^ p + (866350855/873248886 : ℝ) ^ p := by
    exact cert_lt (x := (92134409/97027654 : ℝ)) (y := (866350855/873248886 : ℝ)) (X := (21173356328033/100000000000000 : ℝ)) (Y := (39413322408067/50000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (945672417/1000000000 : ℝ)) (n' := (436624443/500000000 : ℝ)) (Ab := (829209681/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (484697177/250000000 : ℝ)) (τ := (945672417/1000000000 : ℝ)) (σ := (993116291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (945672417/1000000000 : ℝ)) (n' := (436624443/500000000 : ℝ)) (Ab := (829209681/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (484697177/250000000 : ℝ)) (τ := (945672417/1000000000 : ℝ)) (σ := (993116291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (945672417/1000000000 : ℝ)) (n' := (436624443/500000000 : ℝ)) (Ab := (829209681/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (484697177/250000000 : ℝ)) (τ := (945672417/1000000000 : ℝ)) (σ := (993116291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (945672417/1000000000 : ℝ)) (n' := (436624443/500000000 : ℝ)) (Ab := (829209681/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (484697177/250000000 : ℝ)) (τ := (945672417/1000000000 : ℝ)) (σ := (993116291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (945672417/1000000000 : ℝ)) (n' := (436624443/500000000 : ℝ)) (Ab := (829209681/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (484697177/250000000 : ℝ)) (τ := (945672417/1000000000 : ℝ)) (σ := (993116291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (77711833/83736876 : ℝ) ^ p + (1835313241/1842211272 : ℝ) ^ p := by
    exact cert_lt (x := (77711833/83736876 : ℝ)) (y := (1835313241/1842211272 : ℝ)) (X := (532208682197/5000000000000 : ℝ)) (Y := (3574233064817/4000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (545052353/578894364 : ℝ) ^ p + (1150890697/1157788728 : ℝ) ^ p := by
    exact cert_lt (x := (545052353/578894364 : ℝ)) (y := (1150890697/1157788728 : ℝ)) (X := (16412204649989/100000000000000 : ℝ)) (Y := (83587796145123/100000000000000 : ℝ)) 30 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993116291/1000000000 : ℝ)) (U := (144723591/125000000 : ℝ)) (Ab := (854830163/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (945672417/1000000000 : ℝ)) (σ := (993116291/1000000000 : ℝ)) (Ab := (545052353/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab063
