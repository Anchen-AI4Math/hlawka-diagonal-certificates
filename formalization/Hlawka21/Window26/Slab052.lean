import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 52, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab052 (p : ℝ) (hpa : (117/4 : ℝ) ≤ p) (hpb : p ≤ (469/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (358547217799/25915500000000 : ℝ) (7083509/1000000000 : ℝ) (800000155493/5183100000000 : ℝ) (591/500 : ℝ) (976630583/500000000 : ℝ) (976581237/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (4521051/3906250 : ℝ)) ∧
    (∀ j i, if j = i then -(2721/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(279/500 : ℝ)
      else (2059/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11493/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (358547217799/25915500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7083509/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (940973109/1000000000 : ℝ) ^ p + (7949939/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (940973109/1000000000 : ℝ)) (y := (7949939/8000000 : ℝ)) (X := (16806684149101/100000000000000 : ℝ)) (Y := (83193335307559/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (7949939/8000000 : ℝ) ^ p + (940973109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7949939/8000000 : ℝ)) (y := (940973109/1000000000 : ℝ)) (X := (83193335307559/100000000000000 : ℝ)) (Y := (16806684149101/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (483678871/250000000 : ℝ)) (τ := (940973109/1000000000 : ℝ)) (σ := (7949939/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (823804443/868371998 : ℝ) ^ p + (861288489/868371998 : ℝ) ^ p := by
    exact cert_lt (x := (823804443/868371998 : ℝ)) (y := (861288489/868371998 : ℝ)) (X := (10672121016619/50000000000000 : ℝ)) (Y := (78655759051569/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (940973109/1000000000 : ℝ)) (n' := (434185999/500000000 : ℝ)) (Ab := (823804443/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (944223953/1000000000 : ℝ) ^ p + (99300613/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (944223953/1000000000 : ℝ)) (y := (99300613/100000000 : ℝ)) (X := (18594578138047/100000000000000 : ℝ)) (Y := (81405440906739/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99300613/100000000 : ℝ) ^ p + (944223953/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99300613/100000000 : ℝ)) (y := (944223953/1000000000 : ℝ)) (X := (81405440906739/100000000000000 : ℝ)) (Y := (18594578138047/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1937230083/1000000000 : ℝ)) (τ := (944223953/1000000000 : ℝ)) (σ := (99300613/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (413611974/436044713 : ℝ) ^ p + (50882701/51299378 : ℝ) ^ p := by
    exact cert_lt (x := (413611974/436044713 : ℝ)) (y := (50882701/51299378 : ℝ)) (X := (10631686551923/50000000000000 : ℝ)) (Y := (39368313859519/50000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (944223953/1000000000 : ℝ)) (n' := (436044713/500000000 : ℝ)) (Ab := (206805987/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (472156693/500000000 : ℝ) ^ p + (992984611/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (472156693/500000000 : ℝ)) (y := (992984611/1000000000 : ℝ)) (X := (18646272645167/100000000000000 : ℝ)) (Y := (40676873269697/50000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992984611/1000000000 : ℝ) ^ p + (472156693/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992984611/1000000000 : ℝ)) (y := (472156693/500000000 : ℝ)) (X := (40676873269697/50000000000000 : ℝ)) (Y := (18646272645167/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1937297997/1000000000 : ℝ)) (τ := (472156693/500000000 : ℝ)) (σ := (992984611/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (827317849/872191515 : ℝ) ^ p + (865108006/872191515 : ℝ) ^ p := by
    exact cert_lt (x := (827317849/872191515 : ℝ)) (y := (865108006/872191515 : ℝ)) (X := (2657645169597/12500000000000 : ℝ)) (Y := (78738839957951/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (472156693/500000000 : ℝ)) (n' := (174438303/200000000 : ℝ)) (Ab := (827317849/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (944315833/1000000000 : ℝ) ^ p + (992984021/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944315833/1000000000 : ℝ)) (y := (992984021/1000000000 : ℝ)) (X := (18647689021447/100000000000000 : ℝ)) (Y := (8135232964899/10000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992984021/1000000000 : ℝ) ^ p + (944315833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992984021/1000000000 : ℝ)) (y := (944315833/1000000000 : ℝ)) (X := (8135232964899/10000000000000 : ℝ)) (Y := (18647689021447/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (968649927/500000000 : ℝ)) (τ := (944315833/1000000000 : ℝ)) (σ := (992984021/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (827320419/872194309 : ℝ) ^ p + (865110800/872194309 : ℝ) ^ p := by
    exact cert_lt (x := (827320419/872194309 : ℝ)) (y := (865110800/872194309 : ℝ)) (X := (10630550452181/50000000000000 : ℝ)) (Y := (78738900496681/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (944315833/1000000000 : ℝ)) (n' := (872194309/1000000000 : ℝ)) (Ab := (827320419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (9443159/10000000 : ℝ) ^ p + (198596801/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (9443159/10000000 : ℝ)) (y := (198596801/200000000 : ℝ)) (X := (18647727803951/100000000000000 : ℝ)) (Y := (3254091649007/4000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198596801/200000000 : ℝ) ^ p + (9443159/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (198596801/200000000 : ℝ)) (y := (9443159/10000000 : ℝ)) (X := (3254091649007/4000000000000 : ℝ)) (Y := (18647727803951/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (387459981/200000000 : ℝ)) (τ := (9443159/10000000 : ℝ)) (σ := (198596801/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (827320489/872194385 : ℝ) ^ p + (865110876/872194385 : ℝ) ^ p := by
    exact cert_lt (x := (827320489/872194385 : ℝ)) (y := (865110876/872194385 : ℝ)) (X := (10630549665047/50000000000000 : ℝ)) (Y := (78738902143399/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (9443159/10000000 : ℝ)) (n' := (174438877/200000000 : ℝ)) (Ab := (827320489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (944315901/1000000000 : ℝ) ^ p + (198596801/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (944315901/1000000000 : ℝ)) (y := (198596801/200000000 : ℝ)) (X := (3729545676559/20000000000000 : ℝ)) (Y := (3254091649007/4000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198596801/200000000 : ℝ) ^ p + (944315901/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198596801/200000000 : ℝ)) (y := (944315901/1000000000 : ℝ)) (X := (3254091649007/4000000000000 : ℝ)) (Y := (3729545676559/20000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (968649953/500000000 : ℝ)) (τ := (944315901/1000000000 : ℝ)) (σ := (198596801/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (827320489/872194386 : ℝ) ^ p + (865110877/872194386 : ℝ) ^ p := by
    exact cert_lt (x := (827320489/872194386 : ℝ)) (y := (865110877/872194386 : ℝ)) (X := (5315274653889/25000000000000 : ℝ)) (Y := (78738902165067/100000000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (944315901/1000000000 : ℝ)) (n' := (436097193/500000000 : ℝ)) (Ab := (827320489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (968649953/500000000 : ℝ)) (τ := (944315901/1000000000 : ℝ)) (σ := (198596801/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (944315901/1000000000 : ℝ)) (n' := (436097193/500000000 : ℝ)) (Ab := (827320489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (968649953/500000000 : ℝ)) (τ := (944315901/1000000000 : ℝ)) (σ := (198596801/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (944315901/1000000000 : ℝ)) (n' := (436097193/500000000 : ℝ)) (Ab := (827320489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (968649953/500000000 : ℝ)) (τ := (944315901/1000000000 : ℝ)) (σ := (198596801/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (944315901/1000000000 : ℝ)) (n' := (436097193/500000000 : ℝ)) (Ab := (827320489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (968649953/500000000 : ℝ)) (τ := (944315901/1000000000 : ℝ)) (σ := (198596801/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (944315901/1000000000 : ℝ)) (n' := (436097193/500000000 : ℝ)) (Ab := (827320489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (968649953/500000000 : ℝ)) (τ := (944315901/1000000000 : ℝ)) (σ := (198596801/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (71133921/76775456 : ℝ) ^ p + (1835527435/1842610944 : ℝ) ^ p := by
    exact cert_lt (x := (71133921/76775456 : ℝ)) (y := (1835527435/1842610944 : ℝ)) (X := (5338115348719/50000000000000 : ℝ)) (Y := (139568389923/156250000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1088317883/1157389056 : ℝ) ^ p + (1150305547/1157389056 : ℝ) ^ p := by
    exact cert_lt (x := (1088317883/1157389056 : ℝ)) (y := (1150305547/1157389056 : ℝ)) (X := (4117222219367/25000000000000 : ℝ)) (Y := (668248892877/800000000000 : ℝ)) 469 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198596801/200000000 : ℝ)) (U := (4521051/3906250 : ℝ)) (Ab := (213401763/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (944315901/1000000000 : ℝ)) (σ := (198596801/200000000 : ℝ)) (Ab := (1088317883/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab052
