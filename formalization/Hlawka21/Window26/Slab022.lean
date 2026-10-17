import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 22, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab022 (p : ℝ) (hpa : (219/8 : ℝ) ≤ p) (hpb : p ≤ (439/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (361489081567/24254250000000 : ℝ) (7643177/1000000000 : ℝ) (1600000291051/9701700000000 : ℝ) (591/500 : ℝ) (975053667/500000000 : ℝ) (243749357/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156242449/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10831/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1103/2000 : ℝ)
      else (817/1000 : ℝ) ≤ X j i ∧ X j i ≤ (11477/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (361489081567/24254250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7643177/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (936735453/1000000000 : ℝ) ^ p + (993387197/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (936735453/1000000000 : ℝ)) (y := (993387197/1000000000 : ℝ)) (X := (3328666351679/20000000000000 : ℝ)) (Y := (83356687197711/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993387197/1000000000 : ℝ) ^ p + (936735453/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993387197/1000000000 : ℝ)) (y := (936735453/1000000000 : ℝ)) (X := (83356687197711/100000000000000 : ℝ)) (Y := (3328666351679/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (38602453/20000000 : ℝ)) (τ := (936735453/1000000000 : ℝ)) (σ := (993387197/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817980431/864946171 : ℝ) ^ p + (857302994/864946171 : ℝ) ^ p := by
    exact cert_lt (x := (817980431/864946171 : ℝ)) (y := (857302994/864946171 : ℝ)) (X := (21614530475611/100000000000000 : ℝ)) (Y := (78385470735979/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936735453/1000000000 : ℝ)) (n' := (864946171/1000000000 : ℝ)) (Ab := (817980431/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (188028177/200000000 : ℝ) ^ p + (496311331/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (188028177/200000000 : ℝ)) (y := (496311331/500000000 : ℝ)) (X := (18385747215901/100000000000000 : ℝ)) (Y := (81614271086833/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496311331/500000000 : ℝ) ^ p + (188028177/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496311331/500000000 : ℝ)) (y := (188028177/200000000 : ℝ)) (X := (81614271086833/100000000000000 : ℝ)) (Y := (18385747215901/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1932763547/1000000000 : ℝ)) (τ := (188028177/200000000 : ℝ)) (σ := (496311331/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821566652/868865327 : ℝ) ^ p + (861222150/868865327 : ℝ) ^ p := by
    exact cert_lt (x := (821566652/868865327 : ℝ)) (y := (861222150/868865327 : ℝ)) (X := (21527995540339/100000000000000 : ℝ)) (Y := (7847200550713/10000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (188028177/200000000 : ℝ)) (n' := (868865327/1000000000 : ℝ)) (Ab := (205391663/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (940242923/1000000000 : ℝ) ^ p + (992598349/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940242923/1000000000 : ℝ)) (y := (992598349/1000000000 : ℝ)) (X := (9220288594099/50000000000000 : ℝ)) (Y := (81559440309859/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992598349/1000000000 : ℝ) ^ p + (940242923/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992598349/1000000000 : ℝ)) (y := (940242923/1000000000 : ℝ)) (X := (81559440309859/100000000000000 : ℝ)) (Y := (9220288594099/50000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (241605159/125000000 : ℝ)) (τ := (940242923/1000000000 : ℝ)) (σ := (992598349/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (273891300/289660847 : ℝ) ^ p + (861339364/868982541 : ℝ) ^ p := by
    exact cert_lt (x := (273891300/289660847 : ℝ)) (y := (861339364/868982541 : ℝ)) (X := (1076270921341/5000000000000 : ℝ)) (Y := (78474582975377/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (940242923/1000000000 : ℝ)) (n' := (868982541/1000000000 : ℝ)) (Ab := (8216739/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (470122981/500000000 : ℝ) ^ p + (124074703/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (470122981/500000000 : ℝ)) (y := (124074703/125000000 : ℝ)) (X := (18442212604151/100000000000000 : ℝ)) (Y := (8155780583201/10000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124074703/125000000 : ℝ) ^ p + (470122981/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124074703/125000000 : ℝ)) (y := (470122981/500000000 : ℝ)) (X := (8155780583201/10000000000000 : ℝ)) (Y := (18442212604151/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966421793/500000000 : ℝ)) (τ := (470122981/500000000 : ℝ)) (σ := (124074703/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (410838547/434493016 : ℝ) ^ p + (861342855/868986032 : ℝ) ^ p := by
    exact cert_lt (x := (410838547/434493016 : ℝ)) (y := (861342855/868986032 : ℝ)) (X := (21525341557207/100000000000000 : ℝ)) (Y := (78474659731041/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (470122981/500000000 : ℝ)) (n' := (54311627/62500000 : ℝ)) (Ab := (410838547/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (235061513/250000000 : ℝ) ^ p + (496298801/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (235061513/250000000 : ℝ)) (y := (496298801/500000000 : ℝ)) (X := (18442261039133/100000000000000 : ℝ)) (Y := (16311551246911/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496298801/500000000 : ℝ) ^ p + (235061513/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496298801/500000000 : ℝ)) (y := (235061513/250000000 : ℝ)) (X := (16311551246911/20000000000000 : ℝ)) (Y := (18442261039133/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (966421827/500000000 : ℝ)) (τ := (235061513/250000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (273892396/289662045 : ℝ) ^ p + (861342958/868986135 : ℝ) ^ p := by
    exact cert_lt (x := (273892396/289662045 : ℝ)) (y := (861342958/868986135 : ℝ)) (X := (10762669559373/50000000000000 : ℝ)) (Y := (15694932399133/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (235061513/250000000 : ℝ)) (n' := (173797227/200000000 : ℝ)) (Ab := (205419297/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470123027/500000000 : ℝ) ^ p + (496298801/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (470123027/500000000 : ℝ)) (y := (496298801/500000000 : ℝ)) (X := (4610565528867/25000000000000 : ℝ)) (Y := (16311551246911/20000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496298801/500000000 : ℝ) ^ p + (470123027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496298801/500000000 : ℝ)) (y := (470123027/500000000 : ℝ)) (X := (16311551246911/20000000000000 : ℝ)) (Y := (4610565528867/25000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (273892397/289662046 : ℝ) ^ p + (861342961/868986138 : ℝ) ^ p := by
    exact cert_lt (x := (273892397/289662046 : ℝ)) (y := (861342961/868986138 : ℝ)) (X := (1076266961807/5000000000000 : ℝ)) (Y := (627797296493/800000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (n' := (434493069/500000000 : ℝ)) (Ab := (821677191/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (241605457/125000000 : ℝ)) (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1699944040/1843757551 : ℝ) ^ p + (1836114374/1843757551 : ℝ) ^ p := by
    exact cert_lt (x := (1699944040/1843757551 : ℝ)) (y := (1836114374/1843757551 : ℝ)) (X := (10772132536983/100000000000000 : ℝ)) (Y := (44613933860927/50000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083079899/1156242449 : ℝ) ^ p + (1148599272/1156242449 : ℝ) ^ p := by
    exact cert_lt (x := (1083079899/1156242449 : ℝ)) (y := (1148599272/1156242449 : ℝ)) (X := (3327537001833/20000000000000 : ℝ)) (Y := (83362315612349/100000000000000 : ℝ)) 439 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496298801/500000000 : ℝ)) (U := (1156242449/1000000000 : ℝ)) (Ab := (42498601/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470123027/500000000 : ℝ)) (σ := (496298801/500000000 : ℝ)) (Ab := (1083079899/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab022
