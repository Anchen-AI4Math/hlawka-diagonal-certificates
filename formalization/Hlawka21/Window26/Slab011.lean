import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 11, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab011 (p : ℝ) (hpa : (427/16 : ℝ) ≤ p) (hpb : p ≤ (107/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1450681874161/94580500000000 : ℝ) (1967707/250000000 : ℝ) (3200000567483/18916100000000 : ℝ) (591/500 : ℝ) (121802599/62500000 : ℝ) (974361661/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (577900403/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10811/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5489/10000 : ℝ)
      else (8143/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11471/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1450681874161/94580500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1967707/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (584391/625000 : ℝ) ^ p + (124155871/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (584391/625000 : ℝ)) (y := (124155871/125000000 : ℝ)) (X := (8288933795273/50000000000000 : ℝ)) (Y := (83422151030779/100000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124155871/125000000 : ℝ) ^ p + (584391/625000 : ℝ) ^ p := by
    exact cert_lt (x := (124155871/125000000 : ℝ)) (y := (584391/625000 : ℝ)) (X := (83422151030779/100000000000000 : ℝ)) (Y := (8288933795273/50000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (241034071/125000000 : ℝ)) (τ := (584391/625000 : ℝ)) (σ := (124155871/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (62741488/66426587 : ℝ) ^ p + (855674803/863545631 : ℝ) ^ p := by
    exact cert_lt (x := (62741488/66426587 : ℝ)) (y := (855674803/863545631 : ℝ)) (X := (10862115633179/50000000000000 : ℝ)) (Y := (78275769993829/100000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (584391/625000 : ℝ)) (n' := (863545631/1000000000 : ℝ)) (Ab := (50977459/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (469244777/500000000 : ℝ) ^ p + (992472037/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469244777/500000000 : ℝ)) (y := (992472037/1000000000 : ℝ)) (X := (366030770479/2000000000000 : ℝ)) (Y := (20424619772319/25000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992472037/1000000000 : ℝ) ^ p + (469244777/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992472037/1000000000 : ℝ)) (y := (469244777/500000000 : ℝ)) (X := (20424619772319/25000000000000 : ℝ)) (Y := (366030770479/2000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1930961591/1000000000 : ℝ)) (τ := (469244777/500000000 : ℝ)) (σ := (992472037/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (74480816/78867493 : ℝ) ^ p + (859671595/867542423 : ℝ) ^ p := by
    exact cert_lt (x := (74480816/78867493 : ℝ)) (y := (859671595/867542423 : ℝ)) (X := (21635450193029/100000000000000 : ℝ)) (Y := (39182275556123/50000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (469244777/500000000 : ℝ)) (n' := (867542423/1000000000 : ℝ)) (Ab := (51205561/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (187719369/200000000 : ℝ) ^ p + (496223287/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (187719369/200000000 : ℝ)) (y := (496223287/500000000 : ℝ)) (X := (1835758968479/10000000000000 : ℝ)) (Y := (81642427801091/100000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496223287/500000000 : ℝ) ^ p + (187719369/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496223287/500000000 : ℝ)) (y := (187719369/200000000 : ℝ)) (X := (81642427801091/100000000000000 : ℝ)) (Y := (1835758968479/10000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1931043419/1000000000 : ℝ)) (τ := (187719369/200000000 : ℝ)) (σ := (496223287/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (163880359/173533197 : ℝ) ^ p + (859795157/867665985 : ℝ) ^ p := by
    exact cert_lt (x := (163880359/173533197 : ℝ)) (y := (859795157/867665985 : ℝ)) (X := (1081635835127/5000000000000 : ℝ)) (Y := (15673456861841/20000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (187719369/200000000 : ℝ)) (n' := (173533197/200000000 : ℝ)) (Ab := (163880359/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (234650037/250000000 : ℝ) ^ p + (992445789/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (234650037/250000000 : ℝ)) (y := (992445789/1000000000 : ℝ)) (X := (9179658931661/50000000000000 : ℝ)) (Y := (20410175095421/25000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992445789/1000000000 : ℝ) ^ p + (234650037/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992445789/1000000000 : ℝ)) (y := (234650037/250000000 : ℝ)) (X := (20410175095421/25000000000000 : ℝ)) (Y := (9179658931661/50000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1931045937/1000000000 : ℝ)) (τ := (234650037/250000000 : ℝ)) (σ := (992445789/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (819405267/867669788 : ℝ) ^ p + (214949740/216917447 : ℝ) ^ p := by
    exact cert_lt (x := (819405267/867669788 : ℝ)) (y := (214949740/216917447 : ℝ)) (X := (21632632340589/100000000000000 : ℝ)) (Y := (39183684210421/50000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (234650037/250000000 : ℝ)) (n' := (216917447/250000000 : ℝ)) (Ab := (819405267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (938600251/1000000000 : ℝ) ^ p + (248111441/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (938600251/1000000000 : ℝ)) (y := (248111441/250000000 : ℝ)) (X := (3671874351393/20000000000000 : ℝ)) (Y := (40820322684453/50000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248111441/250000000 : ℝ) ^ p + (938600251/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248111441/250000000 : ℝ)) (y := (938600251/1000000000 : ℝ)) (X := (40820322684453/50000000000000 : ℝ)) (Y := (3671874351393/20000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (386209203/200000000 : ℝ)) (τ := (938600251/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (819405376/867669907 : ℝ) ^ p + (859799079/867669907 : ℝ) ^ p := by
    exact cert_lt (x := (819405376/867669907 : ℝ)) (y := (859799079/867669907 : ℝ)) (X := (21632629953193/100000000000000 : ℝ)) (Y := (9795921381597/12500000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (938600251/1000000000 : ℝ)) (n' := (867669907/1000000000 : ℝ)) (Ab := (12803209/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (938600253/1000000000 : ℝ) ^ p + (248111441/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (938600253/1000000000 : ℝ)) (y := (248111441/250000000 : ℝ)) (X := (3671874560689/20000000000000 : ℝ)) (Y := (40820322684453/50000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248111441/250000000 : ℝ) ^ p + (938600253/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248111441/250000000 : ℝ)) (y := (938600253/1000000000 : ℝ)) (X := (40820322684453/50000000000000 : ℝ)) (Y := (3671874560689/20000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1931046017/1000000000 : ℝ)) (τ := (938600253/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (273135126/289223303 : ℝ) ^ p + (859799081/867669909 : ℝ) ^ p := by
    exact cert_lt (x := (273135126/289223303 : ℝ)) (y := (859799081/867669909 : ℝ)) (X := (21632630031759/100000000000000 : ℝ)) (Y := (7836737109701/10000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (938600253/1000000000 : ℝ)) (n' := (867669909/1000000000 : ℝ)) (Ab := (409702689/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1931046017/1000000000 : ℝ)) (τ := (938600253/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (938600253/1000000000 : ℝ)) (n' := (867669909/1000000000 : ℝ)) (Ab := (409702689/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1931046017/1000000000 : ℝ)) (τ := (938600253/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (938600253/1000000000 : ℝ)) (n' := (867669909/1000000000 : ℝ)) (Ab := (409702689/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1931046017/1000000000 : ℝ)) (τ := (938600253/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (938600253/1000000000 : ℝ)) (n' := (867669909/1000000000 : ℝ)) (Ab := (409702689/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1931046017/1000000000 : ℝ)) (τ := (938600253/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (938600253/1000000000 : ℝ)) (n' := (867669909/1000000000 : ℝ)) (Ab := (409702689/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1931046017/1000000000 : ℝ)) (τ := (938600253/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (848516645/922099597 : ℝ) ^ p + (918164183/922099597 : ℝ) ^ p := by
    exact cert_lt (x := (848516645/922099597 : ℝ)) (y := (918164183/922099597 : ℝ)) (X := (10810798724767/100000000000000 : ℝ)) (Y := (89189201566001/100000000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1081013005/1155800806 : ℝ) ^ p + (573964989/577900403 : ℝ) ^ p := by
    exact cert_lt (x := (1081013005/1155800806 : ℝ)) (y := (573964989/577900403 : ℝ)) (X := (2088175645239/12500000000000 : ℝ)) (Y := (1041182441027/1250000000000 : ℝ)) 107 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248111441/250000000 : ℝ)) (U := (577900403/500000000 : ℝ)) (Ab := (169703329/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (938600253/1000000000 : ℝ)) (σ := (248111441/250000000 : ℝ)) (Ab := (216202601/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab011
