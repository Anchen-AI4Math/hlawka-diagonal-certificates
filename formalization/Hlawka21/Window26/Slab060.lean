import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 60, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab060 (p : ℝ) (hpa : (119/4 : ℝ) ≤ p) (hpb : p ≤ (477/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (89456213617/6589625000000 : ℝ) (6947659/1000000000 : ℝ) (800000158151/5271700000000 : ℝ) (591/500 : ℝ) (7632953/3906250 : ℝ) (488485131/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157680807/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10897/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1119/2000 : ℝ)
      else (2063/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11497/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (89456213617/6589625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6947659/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (235502303/250000000 : ℝ) ^ p + (62114431/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (235502303/250000000 : ℝ)) (y := (62114431/62500000 : ℝ)) (X := (8423433631579/50000000000000 : ℝ)) (Y := (41576576703853/50000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (62114431/62500000 : ℝ) ^ p + (235502303/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (62114431/62500000 : ℝ)) (y := (235502303/250000000 : ℝ)) (X := (41576576703853/50000000000000 : ℝ)) (Y := (8423433631579/50000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (483960027/250000000 : ℝ)) (τ := (235502303/250000000 : ℝ)) (σ := (62114431/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (412616637/434599877 : ℝ) ^ p + (862252095/869199754 : ℝ) ^ p := by
    exact cert_lt (x := (412616637/434599877 : ℝ)) (y := (862252095/869199754 : ℝ)) (X := (21278492988133/100000000000000 : ℝ)) (Y := (78721508146351/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (235502303/250000000 : ℝ)) (n' := (434599877/500000000 : ℝ)) (Ab := (412616637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (945220241/1000000000 : ℝ) ^ p + (99310211/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (945220241/1000000000 : ℝ)) (y := (99310211/100000000 : ℝ)) (X := (372913364321/2000000000000 : ℝ)) (Y := (2542323448581/3125000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99310211/100000000 : ℝ) ^ p + (945220241/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99310211/100000000 : ℝ)) (y := (945220241/1000000000 : ℝ)) (X := (2542323448581/3125000000000 : ℝ)) (Y := (372913364321/2000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1938322351/1000000000 : ℝ)) (τ := (945220241/1000000000 : ℝ)) (σ := (99310211/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (414305000/436432961 : ℝ) ^ p + (865918263/872865922 : ℝ) ^ p := by
    exact cert_lt (x := (414305000/436432961 : ℝ)) (y := (865918263/872865922 : ℝ)) (X := (10599514382917/50000000000000 : ℝ)) (Y := (78800972548073/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (945220241/1000000000 : ℝ)) (n' := (436432961/500000000 : ℝ)) (Ab := (82861/100000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (945306691/1000000000 : ℝ) ^ p + (993081259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (945306691/1000000000 : ℝ)) (y := (993081259/1000000000 : ℝ)) (X := (18696575586733/100000000000000 : ℝ)) (Y := (81303442967627/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993081259/1000000000 : ℝ) ^ p + (945306691/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993081259/1000000000 : ℝ)) (y := (945306691/1000000000 : ℝ)) (X := (81303442967627/100000000000000 : ℝ)) (Y := (18696575586733/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (38767759/20000000 : ℝ)) (τ := (945306691/1000000000 : ℝ)) (σ := (993081259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (828700747/872964455 : ℝ) ^ p + (866016796/872964455 : ℝ) ^ p := by
    exact cert_lt (x := (828700747/872964455 : ℝ)) (y := (866016796/872964455 : ℝ)) (X := (21196900977067/100000000000000 : ℝ)) (Y := (15760620022167/20000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (945306691/1000000000 : ℝ)) (n' := (174592891/200000000 : ℝ)) (Ab := (828700747/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (189061801/200000000 : ℝ) ^ p + (9930807/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (189061801/200000000 : ℝ)) (y := (9930807/10000000 : ℝ)) (X := (18697940064313/100000000000000 : ℝ)) (Y := (81302078601799/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (9930807/10000000 : ℝ) ^ p + (189061801/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (9930807/10000000 : ℝ)) (y := (189061801/200000000 : ℝ)) (X := (81302078601799/100000000000000 : ℝ)) (Y := (18697940064313/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (387677941/200000000 : ℝ)) (τ := (189061801/200000000 : ℝ)) (σ := (9930807/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (207175794/218241773 : ℝ) ^ p + (866019433/872967092 : ℝ) ^ p := by
    exact cert_lt (x := (207175794/218241773 : ℝ)) (y := (866019433/872967092 : ℝ)) (X := (2649605540783/12500000000000 : ℝ)) (Y := (39401578522063/50000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (189061801/200000000 : ℝ)) (n' := (218241773/250000000 : ℝ)) (Ab := (103587897/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (945309067/1000000000 : ℝ) ^ p + (198616137/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (945309067/1000000000 : ℝ)) (y := (198616137/200000000 : ℝ)) (X := (18697976624673/100000000000000 : ℝ)) (Y := (40651020995607/50000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198616137/200000000 : ℝ) ^ p + (945309067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198616137/200000000 : ℝ)) (y := (945309067/1000000000 : ℝ)) (X := (40651020995607/50000000000000 : ℝ)) (Y := (18697976624673/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (242298719/125000000 : ℝ)) (τ := (945309067/1000000000 : ℝ)) (σ := (198616137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (828703241/872967163 : ℝ) ^ p + (866019504/872967163 : ℝ) ^ p := by
    exact cert_lt (x := (828703241/872967163 : ℝ)) (y := (866019504/872967163 : ℝ)) (X := (2649605312023/12500000000000 : ℝ)) (Y := (615649676383/781250000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (945309067/1000000000 : ℝ)) (n' := (872967163/1000000000 : ℝ)) (Ab := (828703241/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (236327267/250000000 : ℝ) ^ p + (198616137/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (236327267/250000000 : ℝ)) (y := (198616137/200000000 : ℝ)) (X := (18697977214357/100000000000000 : ℝ)) (Y := (40651020995607/50000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198616137/200000000 : ℝ) ^ p + (236327267/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198616137/200000000 : ℝ)) (y := (236327267/250000000 : ℝ)) (X := (40651020995607/50000000000000 : ℝ)) (Y := (18697977214357/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1938389753/1000000000 : ℝ)) (τ := (236327267/250000000 : ℝ)) (σ := (198616137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (414351621/436483582 : ℝ) ^ p + (866019505/872967164 : ℝ) ^ p := by
    exact cert_lt (x := (414351621/436483582 : ℝ)) (y := (866019505/872967164 : ℝ)) (X := (21196842534849/100000000000000 : ℝ)) (Y := (39401579299307/50000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (236327267/250000000 : ℝ)) (n' := (218241791/250000000 : ℝ)) (Ab := (414351621/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1938389753/1000000000 : ℝ)) (τ := (236327267/250000000 : ℝ)) (σ := (198616137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (236327267/250000000 : ℝ)) (n' := (218241791/250000000 : ℝ)) (Ab := (414351621/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1938389753/1000000000 : ℝ)) (τ := (236327267/250000000 : ℝ)) (σ := (198616137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (236327267/250000000 : ℝ)) (n' := (218241791/250000000 : ℝ)) (Ab := (414351621/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1938389753/1000000000 : ℝ)) (τ := (236327267/250000000 : ℝ)) (σ := (198616137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (236327267/250000000 : ℝ)) (n' := (218241791/250000000 : ℝ)) (Ab := (414351621/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1938389753/1000000000 : ℝ)) (τ := (236327267/250000000 : ℝ)) (σ := (198616137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (236327267/250000000 : ℝ)) (n' := (218241791/250000000 : ℝ)) (Ab := (414351621/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1938389753/1000000000 : ℝ)) (τ := (236327267/250000000 : ℝ)) (σ := (198616137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1709003957/1842319193 : ℝ) ^ p + (1835371534/1842319193 : ℝ) ^ p := by
    exact cert_lt (x := (1709003957/1842319193 : ℝ)) (y := (1835371534/1842319193 : ℝ)) (X := (426110594797/4000000000000 : ℝ)) (Y := (89347235495621/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1089624060/1157680807 : ℝ) ^ p + (1150733148/1157680807 : ℝ) ^ p := by
    exact cert_lt (x := (1089624060/1157680807 : ℝ)) (y := (1150733148/1157680807 : ℝ)) (X := (3285481726513/20000000000000 : ℝ)) (Y := (83572592253009/100000000000000 : ℝ)) 477 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198616137/200000000 : ℝ)) (U := (1157680807/1000000000 : ℝ)) (Ab := (1709003957/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (236327267/250000000 : ℝ)) (σ := (198616137/200000000 : ℝ)) (Ab := (54481203/50000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab060
