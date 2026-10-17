import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 88, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab088 (p : ℝ) (hpa : (63/2 : ℝ) ≤ p) (hpb : p ≤ (505/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (17773794209/1395450000000 : ℝ) (6510171/1000000000 : ℝ) (400000083727/2790900000000 : ℝ) (591/500 : ℝ) (978278291/500000000 : ℝ) (61139729/62500000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144832171/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(547/500 : ℝ) ≤ X j i ∧ X j i ≤ -(1129/2000 : ℝ)
      else (8303/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11511/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (17773794209/1395450000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6510171/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (7562931/8000000 : ℝ) ^ p + (31066323/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (7562931/8000000 : ℝ)) (y := (31066323/31250000 : ℝ)) (X := (16977735798959/100000000000000 : ℝ)) (Y := (4151114294323/5000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31066323/31250000 : ℝ) ^ p + (7562931/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (31066323/31250000 : ℝ)) (y := (7562931/8000000 : ℝ)) (X := (4151114294323/5000000000000 : ℝ)) (Y := (16977735798959/100000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1939488711/1000000000 : ℝ)) (τ := (7562931/8000000 : ℝ)) (σ := (31066323/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (414938242/435927529 : ℝ) ^ p + (865344887/871855058 : ℝ) ^ p := by
    exact cert_lt (x := (414938242/435927529 : ℝ)) (y := (865344887/871855058 : ℝ)) (X := (2106635161581/10000000000000 : ℝ)) (Y := (78933649897513/100000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (7562931/8000000 : ℝ)) (n' := (435927529/500000000 : ℝ)) (Ab := (207469121/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (11855539/12500000 : ℝ) ^ p + (993419171/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (11855539/12500000 : ℝ)) (y := (993419171/1000000000 : ℝ)) (X := (3762260408949/20000000000000 : ℝ)) (Y := (20297179850387/25000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993419171/1000000000 : ℝ) ^ p + (11855539/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (993419171/1000000000 : ℝ)) (y := (11855539/12500000 : ℝ)) (X := (20297179850387/25000000000000 : ℝ)) (Y := (3762260408949/20000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1941862291/1000000000 : ℝ)) (τ := (11855539/12500000 : ℝ)) (σ := (993419171/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (92567703/97261130 : ℝ) ^ p + (289613333/291783390 : ℝ) ^ p := by
    exact cert_lt (x := (92567703/97261130 : ℝ)) (y := (289613333/291783390 : ℝ)) (X := (10495740026449/50000000000000 : ℝ)) (Y := (39504260600063/50000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (11855539/12500000 : ℝ)) (n' := (87535017/100000000 : ℝ)) (Ab := (833109327/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (474260091/500000000 : ℝ) ^ p + (24835011/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (474260091/500000000 : ℝ)) (y := (24835011/25000000 : ℝ)) (X := (942980165807/5000000000000 : ℝ)) (Y := (81140416815133/100000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24835011/25000000 : ℝ) ^ p + (474260091/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (24835011/25000000 : ℝ)) (y := (474260091/500000000 : ℝ)) (X := (81140416815133/100000000000000 : ℝ)) (Y := (942980165807/5000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (970960311/500000000 : ℝ)) (τ := (474260091/500000000 : ℝ)) (σ := (24835011/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (416595080/437718783 : ℝ) ^ p + (289642465/291812522 : ℝ) ^ p := by
    exact cert_lt (x := (416595080/437718783 : ℝ)) (y := (289642465/291812522 : ℝ)) (X := (20989614924081/100000000000000 : ℝ)) (Y := (19752596647119/25000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (474260091/500000000 : ℝ)) (n' := (437718783/500000000 : ℝ)) (Ab := (10414877/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (474261051/500000000 : ℝ) ^ p + (993399973/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474261051/500000000 : ℝ)) (y := (993399973/1000000000 : ℝ)) (X := (18860808274491/100000000000000 : ℝ)) (Y := (81139212893987/100000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993399973/1000000000 : ℝ) ^ p + (474261051/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993399973/1000000000 : ℝ)) (y := (474261051/500000000 : ℝ)) (X := (81139212893987/100000000000000 : ℝ)) (Y := (18860808274491/100000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (77676883/40000000 : ℝ)) (τ := (474261051/500000000 : ℝ)) (σ := (993399973/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (833192173/875439743 : ℝ) ^ p + (868929572/875439743 : ℝ) ^ p := by
    exact cert_lt (x := (833192173/875439743 : ℝ)) (y := (868929572/875439743 : ℝ)) (X := (20989568059189/100000000000000 : ℝ)) (Y := (19752608262589/25000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (474261051/500000000 : ℝ)) (n' := (875439743/1000000000 : ℝ)) (Ab := (833192173/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (18970443/20000000 : ℝ) ^ p + (993399961/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18970443/20000000 : ℝ)) (y := (993399961/1000000000 : ℝ)) (X := (3772167679881/20000000000000 : ℝ)) (Y := (4056959097917/5000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993399961/1000000000 : ℝ) ^ p + (18970443/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (993399961/1000000000 : ℝ)) (y := (18970443/20000000 : ℝ)) (X := (4056959097917/5000000000000 : ℝ)) (Y := (3772167679881/20000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1941922111/1000000000 : ℝ)) (τ := (18970443/20000000 : ℝ)) (σ := (993399961/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (416596112/437719899 : ℝ) ^ p + (289643209/291813266 : ℝ) ^ p := by
    exact cert_lt (x := (416596112/437719899 : ℝ)) (y := (289643209/291813266 : ℝ)) (X := (10494783494573/50000000000000 : ℝ)) (Y := (19752608556043/25000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (18970443/20000000 : ℝ)) (n' := (437719899/500000000 : ℝ)) (Ab := (26037257/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (948522151/1000000000 : ℝ) ^ p + (993399961/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (948522151/1000000000 : ℝ)) (y := (993399961/1000000000 : ℝ)) (X := (18860839027007/100000000000000 : ℝ)) (Y := (4056959097917/5000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993399961/1000000000 : ℝ) ^ p + (948522151/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993399961/1000000000 : ℝ)) (y := (948522151/1000000000 : ℝ)) (X := (4056959097917/5000000000000 : ℝ)) (Y := (18860839027007/100000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (30342533/15625000 : ℝ)) (τ := (948522151/1000000000 : ℝ)) (σ := (993399961/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (833192225/875439799 : ℝ) ^ p + (868929628/875439799 : ℝ) ^ p := by
    exact cert_lt (x := (833192225/875439799 : ℝ)) (y := (868929628/875439799 : ℝ)) (X := (20989567027517/100000000000000 : ℝ)) (Y := (39505217122757/50000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (948522151/1000000000 : ℝ)) (n' := (875439799/1000000000 : ℝ)) (Ab := (33327689/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (30342533/15625000 : ℝ)) (τ := (948522151/1000000000 : ℝ)) (σ := (993399961/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (948522151/1000000000 : ℝ)) (n' := (875439799/1000000000 : ℝ)) (Ab := (33327689/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (30342533/15625000 : ℝ)) (τ := (948522151/1000000000 : ℝ)) (σ := (993399961/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (948522151/1000000000 : ℝ)) (n' := (875439799/1000000000 : ℝ)) (Ab := (33327689/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (30342533/15625000 : ℝ)) (τ := (948522151/1000000000 : ℝ)) (σ := (993399961/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (948522151/1000000000 : ℝ)) (n' := (875439799/1000000000 : ℝ)) (Ab := (33327689/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (30342533/15625000 : ℝ)) (τ := (948522151/1000000000 : ℝ)) (σ := (993399961/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (948522151/1000000000 : ℝ)) (n' := (875439799/1000000000 : ℝ)) (Ab := (33327689/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (30342533/15625000 : ℝ)) (τ := (948522151/1000000000 : ℝ)) (σ := (993399961/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (428709315/460335658 : ℝ) ^ p + (1834832461/1841342632 : ℝ) ^ p := by
    exact cert_lt (x := (428709315/460335658 : ℝ)) (y := (1834832461/1841342632 : ℝ)) (X := (1057668479199/10000000000000 : ℝ)) (Y := (89423315511299/100000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (546963391/579328684 : ℝ) ^ p + (1152147197/1158657368 : ℝ) ^ p := by
    exact cert_lt (x := (546963391/579328684 : ℝ)) (y := (1152147197/1158657368 : ℝ)) (X := (16292444061471/100000000000000 : ℝ)) (Y := (20926889174089/25000000000000 : ℝ)) 505 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993399961/1000000000 : ℝ)) (U := (144832171/125000000 : ℝ)) (Ab := (85741863/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (948522151/1000000000 : ℝ)) (σ := (993399961/1000000000 : ℝ)) (Ab := (546963391/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab088
