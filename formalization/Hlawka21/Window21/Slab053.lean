import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 53, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab053 (p : ℝ) (hpa : (725/32 : ℝ) ≤ p) (hpb : p ≤ (363/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (42181518343/1979250000000 : ℝ) (5493491/500000000 : ℝ) (160000023751/791700000000 : ℝ) (3033/2500 : ℝ) (242477513/125000000 : ℝ) (48493459/50000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298261927/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11087/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4521/10000 : ℝ)
      else (959/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (42181518343/1979250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5493491/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (915589363/1000000000 : ℝ) ^ p + (124202029/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (915589363/1000000000 : ℝ)) (y := (124202029/125000000 : ℝ)) (X := (2704677582929/20000000000000 : ℝ)) (Y := (43238314242269/50000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124202029/125000000 : ℝ) ^ p + (915589363/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124202029/125000000 : ℝ)) (y := (915589363/1000000000 : ℝ)) (X := (43238314242269/50000000000000 : ℝ)) (Y := (2704677582929/20000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381841119/200000000 : ℝ)) (τ := (915589363/1000000000 : ℝ)) (σ := (124202029/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (155594325/165051346 : ℝ) ^ p + (407134874/412628365 : ℝ) ^ p := by
    exact cert_lt (x := (155594325/165051346 : ℝ)) (y := (407134874/412628365 : ℝ)) (X := (2621957270841/10000000000000 : ℝ)) (Y := (36890214406941/50000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915589363/1000000000 : ℝ)) (n' := (82525673/100000000 : ℝ)) (Ab := (6223773/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921358829/1000000000 : ℝ) ^ p + (992554997/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921358829/1000000000 : ℝ)) (y := (992554997/1000000000 : ℝ)) (X := (243667982953/1562500000000 : ℝ)) (Y := (84405264898711/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992554997/1000000000 : ℝ) ^ p + (921358829/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992554997/1000000000 : ℝ)) (y := (921358829/1000000000 : ℝ)) (X := (84405264898711/100000000000000 : ℝ)) (Y := (243667982953/1562500000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956956913/500000000 : ℝ)) (τ := (921358829/1000000000 : ℝ)) (σ := (992554997/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (392097511/416060094 : ℝ) ^ p + (410566603/416060094 : ℝ) ^ p := by
    exact cert_lt (x := (392097511/416060094 : ℝ)) (y := (410566603/416060094 : ℝ)) (X := (6508263773853/25000000000000 : ℝ)) (Y := (18491736521849/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921358829/1000000000 : ℝ)) (n' := (208030047/250000000 : ℝ)) (Ab := (392097511/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (921625011/1000000000 : ℝ) ^ p + (49625091/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (921625011/1000000000 : ℝ)) (y := (49625091/50000000 : ℝ)) (X := (15697286843351/100000000000000 : ℝ)) (Y := (8430272966091/10000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (49625091/50000000 : ℝ) ^ p + (921625011/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49625091/50000000 : ℝ)) (y := (921625011/1000000000 : ℝ)) (X := (8430272966091/10000000000000 : ℝ)) (Y := (15697286843351/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914126831/1000000000 : ℝ)) (τ := (921625011/1000000000 : ℝ)) (σ := (49625091/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (196120293/208108957 : ℝ) ^ p + (410724423/416217914 : ℝ) ^ p := by
    exact cert_lt (x := (196120293/208108957 : ℝ)) (y := (410724423/416217914 : ℝ)) (X := (6506135160767/25000000000000 : ℝ)) (Y := (14795092098433/20000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (921625011/1000000000 : ℝ)) (n' := (208108957/250000000 : ℝ)) (Ab := (196120293/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (460818579/500000000 : ℝ) ^ p + (124062423/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (460818579/500000000 : ℝ)) (y := (124062423/125000000 : ℝ)) (X := (15701981329769/100000000000000 : ℝ)) (Y := (4214901772449/5000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124062423/125000000 : ℝ) ^ p + (460818579/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124062423/125000000 : ℝ)) (y := (460818579/500000000 : ℝ)) (X := (4214901772449/5000000000000 : ℝ)) (Y := (15701981329769/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957068271/500000000 : ℝ)) (τ := (460818579/500000000 : ℝ)) (σ := (124062423/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (130749038/138741705 : ℝ) ^ p + (410731624/416225115 : ℝ) ^ p := by
    exact cert_lt (x := (130749038/138741705 : ℝ)) (y := (410731624/416225115 : ℝ)) (X := (26024152038361/100000000000000 : ℝ)) (Y := (18493962213787/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (460818579/500000000 : ℝ)) (n' := (83245023/100000000 : ℝ)) (Ab := (196123557/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921637713/1000000000 : ℝ) ^ p + (124062409/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (921637713/1000000000 : ℝ)) (y := (124062409/125000000 : ℝ)) (X := (15702195854291/100000000000000 : ℝ)) (Y := (2634306863411/3125000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124062409/125000000 : ℝ) ^ p + (921637713/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124062409/125000000 : ℝ)) (y := (921637713/1000000000 : ℝ)) (X := (2634306863411/3125000000000 : ℝ)) (Y := (15702195854291/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (382827397/200000000 : ℝ)) (τ := (921637713/1000000000 : ℝ)) (σ := (124062409/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784494825/832450888 : ℝ) ^ p + (4066653/4121044 : ℝ) ^ p := by
    exact cert_lt (x := (784494825/832450888 : ℝ)) (y := (4066653/4121044 : ℝ)) (X := (13012067328819/50000000000000 : ℝ)) (Y := (73975866598439/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921637713/1000000000 : ℝ)) (n' := (104056361/125000000 : ℝ)) (Ab := (31379793/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (921637739/1000000000 : ℝ) ^ p + (992499267/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921637739/1000000000 : ℝ)) (y := (992499267/1000000000 : ℝ)) (X := (15702205904157/100000000000000 : ℝ)) (Y := (84297809994351/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992499267/1000000000 : ℝ) ^ p + (921637739/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992499267/1000000000 : ℝ)) (y := (921637739/1000000000 : ℝ)) (X := (84297809994351/100000000000000 : ℝ)) (Y := (15702205904157/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392247426/416225459 : ℝ) ^ p + (410731968/416225459 : ℝ) ^ p := by
    exact cert_lt (x := (392247426/416225459 : ℝ)) (y := (410731968/416225459 : ℝ)) (X := (26024133700499/100000000000000 : ℝ)) (Y := (18493966851851/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (n' := (416225459/500000000 : ℝ)) (Ab := (196123713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (957068503/500000000 : ℝ)) (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (825557227/903476146 : ℝ) ^ p + (897982655/903476146 : ℝ) ^ p := by
    exact cert_lt (x := (825557227/903476146 : ℝ)) (y := (897982655/903476146 : ℝ)) (X := (6461179617289/50000000000000 : ℝ)) (Y := (87077640980407/100000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1108664851/1193047708 : ℝ) ^ p + (591030363/596523854 : ℝ) ^ p := by
    exact cert_lt (x := (1108664851/1193047708 : ℝ)) (y := (591030363/596523854 : ℝ)) (X := (18933558546649/100000000000000 : ℝ)) (Y := (20266610491329/25000000000000 : ℝ)) 363 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992499267/1000000000 : ℝ)) (U := (298261927/250000000 : ℝ)) (Ab := (825557227/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921637739/1000000000 : ℝ)) (σ := (992499267/1000000000 : ℝ)) (Ab := (1108664851/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab053
