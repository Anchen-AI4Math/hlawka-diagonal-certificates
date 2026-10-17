import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 58, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab058 (p : ℝ) (hpa : (237/8 : ℝ) ≤ p) (hpb : p ≤ (475/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (716006530817/52495500000000 : ℝ) (6981139/1000000000 : ℝ) (1600000314973/10499100000000 : ℝ) (591/500 : ℝ) (976922343/500000000 : ℝ) (976874223/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157608419/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5447/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5591/10000 : ℝ)
      else (1031/1250 : ℝ) ≤ X j i ∧ X j i ≤ (1437/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (716006530817/52495500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6981139/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (941753597/1000000000 : ℝ) ^ p + (993808997/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (941753597/1000000000 : ℝ)) (y := (993808997/1000000000 : ℝ)) (X := (4209235610221/25000000000000 : ℝ)) (Y := (83163078917549/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993808997/1000000000 : ℝ) ^ p + (941753597/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993808997/1000000000 : ℝ)) (y := (941753597/1000000000 : ℝ)) (X := (83163078917549/100000000000000 : ℝ)) (Y := (4209235610221/25000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (967781297/500000000 : ℝ)) (τ := (941753597/1000000000 : ℝ)) (σ := (993808997/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (274960198/289665299 : ℝ) ^ p + (78364978/78999627 : ℝ) ^ p := by
    exact cert_lt (x := (274960198/289665299 : ℝ)) (y := (78364978/78999627 : ℝ)) (X := (21294705827299/100000000000000 : ℝ)) (Y := (78705295306031/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (941753597/1000000000 : ℝ)) (n' := (868995897/1000000000 : ℝ)) (Ab := (412440297/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (944974521/1000000000 : ℝ) ^ p + (993078351/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944974521/1000000000 : ℝ)) (y := (993078351/1000000000 : ℝ)) (X := (4658265053591/25000000000000 : ℝ)) (Y := (16273391776139/20000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993078351/1000000000 : ℝ) ^ p + (944974521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993078351/1000000000 : ℝ)) (y := (944974521/1000000000 : ℝ)) (X := (16273391776139/20000000000000 : ℝ)) (Y := (4658265053591/25000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (242256609/125000000 : ℝ)) (τ := (944974521/1000000000 : ℝ)) (σ := (993078351/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (276089315/290891593 : ℝ) ^ p + (865693640/872674779 : ℝ) ^ p := by
    exact cert_lt (x := (276089315/290891593 : ℝ)) (y := (865693640/872674779 : ℝ)) (X := (4242978823691/20000000000000 : ℝ)) (Y := (78785106772349/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (944974521/1000000000 : ℝ)) (n' := (872674779/1000000000 : ℝ)) (Ab := (165653589/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (945061703/1000000000 : ℝ) ^ p + (124132167/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (945061703/1000000000 : ℝ)) (y := (124132167/125000000 : ℝ)) (X := (467104059687/2500000000000 : ℝ)) (Y := (40657928565317/50000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124132167/125000000 : ℝ) ^ p + (945061703/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124132167/125000000 : ℝ)) (y := (945061703/1000000000 : ℝ)) (X := (40657928565317/50000000000000 : ℝ)) (Y := (467104059687/2500000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1938119039/1000000000 : ℝ)) (τ := (945061703/1000000000 : ℝ)) (σ := (124132167/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (138059911/145462364 : ℝ) ^ p + (865793045/872774184 : ℝ) ^ p := by
    exact cert_lt (x := (138059911/145462364 : ℝ)) (y := (865793045/872774184 : ℝ)) (X := (21212745807577/100000000000000 : ℝ)) (Y := (39393627528617/50000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (945061703/1000000000 : ℝ)) (n' := (109096773/125000000 : ℝ)) (Ab := (414179733/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (18901281/20000000 : ℝ) ^ p + (993056769/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18901281/20000000 : ℝ)) (y := (993056769/1000000000 : ℝ)) (X := (9342769981879/50000000000000 : ℝ)) (Y := (81314478797967/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993056769/1000000000 : ℝ) ^ p + (18901281/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (993056769/1000000000 : ℝ)) (y := (18901281/20000000 : ℝ)) (X := (81314478797967/100000000000000 : ℝ)) (Y := (9342769981879/50000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1938120819/1000000000 : ℝ)) (τ := (18901281/20000000 : ℝ)) (σ := (993056769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (82836193/87277686 : ℝ) ^ p + (865795721/872776860 : ℝ) ^ p := by
    exact cert_lt (x := (82836193/87277686 : ℝ)) (y := (865795721/872776860 : ℝ)) (X := (1060634408289/5000000000000 : ℝ)) (Y := (78787312883457/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (18901281/20000000 : ℝ)) (n' := (43638843/50000000 : ℝ)) (Ab := (82836193/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (945064113/1000000000 : ℝ) ^ p + (496528377/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (945064113/1000000000 : ℝ)) (y := (496528377/500000000 : ℝ)) (X := (3737115388617/20000000000000 : ℝ)) (Y := (81314442334447/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496528377/500000000 : ℝ) ^ p + (945064113/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496528377/500000000 : ℝ)) (y := (945064113/1000000000 : ℝ)) (X := (81314442334447/100000000000000 : ℝ)) (Y := (3737115388617/20000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1938120867/1000000000 : ℝ)) (τ := (945064113/1000000000 : ℝ)) (σ := (496528377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (207090499/218194233 : ℝ) ^ p + (865795793/872776932 : ℝ) ^ p := by
    exact cert_lt (x := (207090499/218194233 : ℝ)) (y := (865795793/872776932 : ℝ)) (X := (21212686389883/100000000000000 : ℝ)) (Y := (15757462887863/20000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (945064113/1000000000 : ℝ)) (n' := (218194233/250000000 : ℝ)) (Ab := (207090499/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (472532057/500000000 : ℝ) ^ p + (496528377/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (472532057/500000000 : ℝ)) (y := (496528377/500000000 : ℝ)) (X := (18685577530059/100000000000000 : ℝ)) (Y := (81314442334447/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496528377/500000000 : ℝ) ^ p + (472532057/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496528377/500000000 : ℝ)) (y := (472532057/500000000 : ℝ)) (X := (81314442334447/100000000000000 : ℝ)) (Y := (18685577530059/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (484530217/250000000 : ℝ)) (τ := (472532057/500000000 : ℝ)) (σ := (496528377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (828361997/872776933 : ℝ) ^ p + (865795794/872776933 : ℝ) ^ p := by
    exact cert_lt (x := (828361997/872776933 : ℝ)) (y := (865795794/872776933 : ℝ)) (X := (21212686428571/100000000000000 : ℝ)) (Y := (19696828615231/25000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (472532057/500000000 : ℝ)) (n' := (872776933/1000000000 : ℝ)) (Ab := (828361997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (484530217/250000000 : ℝ)) (τ := (472532057/500000000 : ℝ)) (σ := (496528377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (472532057/500000000 : ℝ)) (n' := (872776933/1000000000 : ℝ)) (Ab := (828361997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (484530217/250000000 : ℝ)) (τ := (472532057/500000000 : ℝ)) (σ := (496528377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (472532057/500000000 : ℝ)) (n' := (872776933/1000000000 : ℝ)) (Ab := (828361997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (484530217/250000000 : ℝ)) (τ := (472532057/500000000 : ℝ)) (σ := (496528377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (472532057/500000000 : ℝ)) (n' := (872776933/1000000000 : ℝ)) (Ab := (828361997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (484530217/250000000 : ℝ)) (τ := (472532057/500000000 : ℝ)) (σ := (496528377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (472532057/500000000 : ℝ)) (n' := (872776933/1000000000 : ℝ)) (Ab := (828361997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (484530217/250000000 : ℝ)) (τ := (472532057/500000000 : ℝ)) (σ := (496528377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (569520648/614130527 : ℝ) ^ p + (1835410442/1842391581 : ℝ) ^ p := by
    exact cert_lt (x := (569520648/614130527 : ℝ)) (y := (1835410442/1842391581 : ℝ)) (X := (10658556828619/100000000000000 : ℝ)) (Y := (8934144337477/10000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1089300893/1157608419 : ℝ) ^ p + (104602480/105237129 : ℝ) ^ p := by
    exact cert_lt (x := (1089300893/1157608419 : ℝ)) (y := (104602480/105237129 : ℝ)) (X := (16437653012449/100000000000000 : ℝ)) (Y := (83562347878593/100000000000000 : ℝ)) 475 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496528377/500000000 : ℝ)) (U := (1157608419/1000000000 : ℝ)) (Ab := (213570243/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (472532057/500000000 : ℝ)) (σ := (496528377/500000000 : ℝ)) (Ab := (1089300893/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab058
