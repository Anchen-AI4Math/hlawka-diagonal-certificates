import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 66, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab066 (p : ℝ) (hpa : (241/8 : ℝ) ≤ p) (hpb : p ≤ (483/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (35729875387/2669075000000 : ℝ) (6849099/1000000000 : ℝ) (1600000320289/10676300000000 : ℝ) (591/500 : ℝ) (97730021/50000000 : ℝ) (488626827/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578947927/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5453/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2803/5000 : ℝ)
      else (8263/10000 : ℝ) ≤ X j i ∧ X j i ≤ (23/20 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (35729875387/2669075000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6849099/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (942762791/1000000000 : ℝ) ^ p + (993895699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942762791/1000000000 : ℝ)) (y := (993895699/1000000000 : ℝ)) (X := (8438076604101/50000000000000 : ℝ)) (Y := (8312386705507/10000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993895699/1000000000 : ℝ) ^ p + (942762791/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993895699/1000000000 : ℝ)) (y := (942762791/1000000000 : ℝ)) (X := (8312386705507/10000000000000 : ℝ)) (Y := (8438076604101/50000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193665849/100000000 : ℝ)) (τ := (942762791/1000000000 : ℝ)) (σ := (993895699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (413136861/434899676 : ℝ) ^ p + (862950253/869799352 : ℝ) ^ p := by
    exact cert_lt (x := (413136861/434899676 : ℝ)) (y := (862950253/869799352 : ℝ)) (X := (10615379025909/50000000000000 : ℝ)) (Y := (78769242940951/100000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (942762791/1000000000 : ℝ)) (n' := (108724919/125000000 : ℝ)) (Ab := (413136861/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (472972187/500000000 : ℝ) ^ p + (124146559/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (472972187/500000000 : ℝ)) (y := (124146559/125000000 : ℝ)) (X := (18682834095843/100000000000000 : ℝ)) (Y := (40658592352289/50000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124146559/125000000 : ℝ) ^ p + (472972187/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124146559/125000000 : ℝ)) (y := (472972187/500000000 : ℝ)) (X := (40658592352289/50000000000000 : ℝ)) (Y := (18682834095843/100000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (969558423/500000000 : ℝ)) (τ := (472972187/500000000 : ℝ)) (σ := (124146559/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (829618846/873427775 : ℝ) ^ p + (866578676/873427775 : ℝ) ^ p := by
    exact cert_lt (x := (829618846/873427775 : ℝ)) (y := (866578676/873427775 : ℝ)) (X := (21152319595629/100000000000000 : ℝ)) (Y := (39423840912199/50000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (472972187/500000000 : ℝ)) (n' := (34937111/40000000 : ℝ)) (Ab := (414809423/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (473014339/500000000 : ℝ) ^ p + (124144013/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (473014339/500000000 : ℝ)) (y := (124144013/125000000 : ℝ)) (X := (9366581498273/50000000000000 : ℝ)) (Y := (40633428726063/50000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124144013/125000000 : ℝ) ^ p + (473014339/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124144013/125000000 : ℝ)) (y := (473014339/500000000 : ℝ)) (X := (40633428726063/50000000000000 : ℝ)) (Y := (9366581498273/50000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (969590391/500000000 : ℝ)) (τ := (473014339/500000000 : ℝ)) (σ := (124144013/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (165941465/174704751 : ℝ) ^ p + (96297184/97058195 : ℝ) ^ p := by
    exact cert_lt (x := (165941465/174704751 : ℝ)) (y := (96297184/97058195 : ℝ)) (X := (10575125947857/50000000000000 : ℝ)) (Y := (15769949776851/20000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (473014339/500000000 : ℝ)) (n' := (174704751/200000000 : ℝ)) (Ab := (33188293/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (9460309/10000000 : ℝ) ^ p + (496575783/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (9460309/10000000 : ℝ)) (y := (496575783/500000000 : ℝ)) (X := (9367245643267/50000000000000 : ℝ)) (Y := (81265528517279/100000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496575783/500000000 : ℝ) ^ p + (9460309/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (496575783/500000000 : ℝ)) (y := (9460309/10000000 : ℝ)) (X := (81265528517279/100000000000000 : ℝ)) (Y := (9367245643267/50000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (969591233/500000000 : ℝ)) (τ := (9460309/10000000 : ℝ)) (σ := (496575783/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (829709657/873526284 : ℝ) ^ p + (96297465/97058476 : ℝ) ^ p := by
    exact cert_lt (x := (829709657/873526284 : ℝ)) (y := (96297465/97058476 : ℝ)) (X := (5287549479753/25000000000000 : ℝ)) (Y := (19712450836069/25000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (9460309/10000000 : ℝ)) (n' := (218381571/250000000 : ℝ)) (Ab := (829709657/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (473015479/500000000 : ℝ) ^ p + (15517993/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (473015479/500000000 : ℝ)) (y := (15517993/15625000 : ℝ)) (X := (18734525959589/100000000000000 : ℝ)) (Y := (20316373483903/25000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (15517993/15625000 : ℝ) ^ p + (473015479/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (15517993/15625000 : ℝ)) (y := (473015479/500000000 : ℝ)) (X := (20316373483903/25000000000000 : ℝ)) (Y := (18734525959589/100000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (193918251/100000000 : ℝ)) (τ := (473015479/500000000 : ℝ)) (σ := (15517993/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (138284953/145587725 : ℝ) ^ p + (288892417/291175450 : ℝ) ^ p := by
    exact cert_lt (x := (138284953/145587725 : ℝ)) (y := (288892417/291175450 : ℝ)) (X := (21150196619/100000000000 : ℝ)) (Y := (7884980476553/10000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (473015479/500000000 : ℝ)) (n' := (17470527/20000000 : ℝ)) (Ab := (414854859/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (946030959/1000000000 : ℝ) ^ p + (15517993/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (946030959/1000000000 : ℝ)) (y := (15517993/15625000 : ℝ)) (X := (18734526557401/100000000000000 : ℝ)) (Y := (20316373483903/25000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (15517993/15625000 : ℝ) ^ p + (946030959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (15517993/15625000 : ℝ)) (y := (946030959/1000000000 : ℝ)) (X := (20316373483903/25000000000000 : ℝ)) (Y := (18734526557401/100000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1939182511/1000000000 : ℝ)) (τ := (946030959/1000000000 : ℝ)) (σ := (15517993/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (829709719/873526351 : ℝ) ^ p + (866677252/873526351 : ℝ) ^ p := by
    exact cert_lt (x := (829709719/873526351 : ℝ)) (y := (866677252/873526351 : ℝ)) (X := (21150196657599/100000000000000 : ℝ)) (Y := (9856225598383/12500000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (946030959/1000000000 : ℝ)) (n' := (873526351/1000000000 : ℝ)) (Ab := (829709719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1939182511/1000000000 : ℝ)) (τ := (946030959/1000000000 : ℝ)) (σ := (15517993/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (946030959/1000000000 : ℝ)) (n' := (873526351/1000000000 : ℝ)) (Ab := (829709719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1939182511/1000000000 : ℝ)) (τ := (946030959/1000000000 : ℝ)) (σ := (15517993/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (946030959/1000000000 : ℝ)) (n' := (873526351/1000000000 : ℝ)) (Ab := (829709719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1939182511/1000000000 : ℝ)) (τ := (946030959/1000000000 : ℝ)) (σ := (15517993/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (946030959/1000000000 : ℝ)) (n' := (873526351/1000000000 : ℝ)) (Ab := (829709719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1939182511/1000000000 : ℝ)) (τ := (946030959/1000000000 : ℝ)) (σ := (15517993/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (946030959/1000000000 : ℝ)) (n' := (873526351/1000000000 : ℝ)) (Ab := (829709719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1939182511/1000000000 : ℝ)) (τ := (946030959/1000000000 : ℝ)) (σ := (15517993/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (855154420/921052073 : ℝ) ^ p + (1835255047/1842104146 : ℝ) ^ p := by
    exact cert_lt (x := (855154420/921052073 : ℝ)) (y := (1835255047/1842104146 : ℝ)) (X := (10635695146639/100000000000000 : ℝ)) (Y := (17872861028219/20000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (11601920/12318041 : ℝ) ^ p + (1151046755/1157895854 : ℝ) ^ p := by
    exact cert_lt (x := (11601920/12318041 : ℝ)) (y := (1151046755/1157895854 : ℝ)) (X := (16397189962779/100000000000000 : ℝ)) (Y := (83602810666893/100000000000000 : ℝ)) 483 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (15517993/15625000 : ℝ)) (U := (578947927/500000000 : ℝ)) (Ab := (42757721/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (946030959/1000000000 : ℝ)) (σ := (15517993/15625000 : ℝ)) (Ab := (426008/390625 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab066
