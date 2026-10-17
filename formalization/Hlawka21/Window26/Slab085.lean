import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 85, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab085 (p : ℝ) (hpa : (501/16 : ℝ) ≤ p) (hpb : p ≤ (251/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (711430276139/55485750000000 : ℝ) (3277213/500000000 : ℝ) (3200000665829/22194300000000 : ℝ) (591/500 : ℝ) (978149909/500000000 : ℝ) (122263347/125000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158555979/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2187/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(141/250 : ℝ)
      else (4149/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11509/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (711430276139/55485750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3277213/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (472512669/500000000 : ℝ) ^ p + (497046203/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (472512669/500000000 : ℝ)) (y := (497046203/500000000 : ℝ)) (X := (2120549182519/12500000000000 : ℝ)) (Y := (20758907024549/25000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497046203/500000000 : ℝ) ^ p + (472512669/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (497046203/500000000 : ℝ)) (y := (472512669/500000000 : ℝ)) (X := (20758907024549/25000000000000 : ℝ)) (Y := (2120549182519/12500000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (121194859/62500000 : ℝ)) (τ := (472512669/500000000 : ℝ)) (σ := (497046203/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (25133450/26411733 : ℝ) ^ p + (865032763/871587189 : ℝ) ^ p := by
    exact cert_lt (x := (25133450/26411733 : ℝ)) (y := (865032763/871587189 : ℝ)) (X := (21087843837581/100000000000000 : ℝ)) (Y := (78912157405723/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (472512669/500000000 : ℝ)) (n' := (871587189/1000000000 : ℝ)) (Ab := (16588077/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (474058043/500000000 : ℝ) ^ p + (496693269/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (474058043/500000000 : ℝ)) (y := (496693269/500000000 : ℝ)) (X := (18794467831283/100000000000000 : ℝ)) (Y := (20301388371253/25000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496693269/500000000 : ℝ) ^ p + (474058043/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496693269/500000000 : ℝ)) (y := (474058043/500000000 : ℝ)) (X := (20301388371253/25000000000000 : ℝ)) (Y := (18794467831283/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60671957/31250000 : ℝ)) (τ := (474058043/500000000 : ℝ)) (σ := (496693269/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (277550557/291700005 : ℝ) ^ p + (868545589/875100015 : ℝ) ^ p := by
    exact cert_lt (x := (277550557/291700005 : ℝ)) (y := (868545589/875100015 : ℝ)) (X := (21012503150013/100000000000000 : ℝ)) (Y := (78987498051567/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (474058043/500000000 : ℝ)) (n' := (175020003/200000000 : ℝ)) (Ab := (832651671/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (474097041/500000000 : ℝ) ^ p + (198673519/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (474097041/500000000 : ℝ)) (y := (198673519/200000000 : ℝ)) (X := (18843037739561/100000000000000 : ℝ)) (Y := (10144622850643/12500000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198673519/200000000 : ℝ) ^ p + (474097041/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198673519/200000000 : ℝ)) (y := (474097041/500000000 : ℝ)) (X := (10144622850643/12500000000000 : ℝ)) (Y := (18843037739561/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1941561677/1000000000 : ℝ)) (τ := (474097041/500000000 : ℝ)) (σ := (198673519/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (832733489/875188515 : ℝ) ^ p + (868634089/875188515 : ℝ) ^ p := by
    exact cert_lt (x := (832733489/875188515 : ℝ)) (y := (868634089/875188515 : ℝ)) (X := (10505305887531/50000000000000 : ℝ)) (Y := (19747347305677/25000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (474097041/500000000 : ℝ)) (n' := (175037703/200000000 : ℝ)) (Ab := (832733489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (23704901/25000000 : ℝ) ^ p + (993367119/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23704901/25000000 : ℝ)) (y := (993367119/1000000000 : ℝ)) (X := (18844258593531/100000000000000 : ℝ)) (Y := (81155762682659/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993367119/1000000000 : ℝ) ^ p + (23704901/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (993367119/1000000000 : ℝ)) (y := (23704901/25000000 : ℝ)) (X := (81155762682659/100000000000000 : ℝ)) (Y := (18844258593531/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1941563159/1000000000 : ℝ)) (τ := (23704901/25000000 : ℝ)) (σ := (993367119/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (832735543/875190736 : ℝ) ^ p + (434318155/437595368 : ℝ) ^ p := by
    exact cert_lt (x := (832735543/875190736 : ℝ)) (y := (434318155/437595368 : ℝ)) (X := (2101056486369/10000000000000 : ℝ)) (Y := (19747359169817/25000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (23704901/25000000 : ℝ)) (n' := (54699421/62500000 : ℝ)) (Ab := (832735543/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (948196089/1000000000 : ℝ) ^ p + (993367107/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (948196089/1000000000 : ℝ)) (y := (993367107/1000000000 : ℝ)) (X := (9422144573519/50000000000000 : ℝ)) (Y := (40577865961749/50000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993367107/1000000000 : ℝ) ^ p + (948196089/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993367107/1000000000 : ℝ)) (y := (948196089/1000000000 : ℝ)) (X := (40577865961749/50000000000000 : ℝ)) (Y := (9422144573519/50000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (485390799/250000000 : ℝ)) (τ := (948196089/1000000000 : ℝ)) (σ := (993367107/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (416367797/437595396 : ℝ) ^ p + (434318183/437595396 : ℝ) ^ p := by
    exact cert_lt (x := (416367797/437595396 : ℝ)) (y := (434318183/437595396 : ℝ)) (X := (21010563056067/100000000000000 : ℝ)) (Y := (78989437875829/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (948196089/1000000000 : ℝ)) (n' := (109398849/125000000 : ℝ)) (Ab := (416367797/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (948196091/1000000000 : ℝ) ^ p + (496683553/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (948196091/1000000000 : ℝ)) (y := (496683553/500000000 : ℝ)) (X := (18844290394121/100000000000000 : ℝ)) (Y := (16231145872047/20000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496683553/500000000 : ℝ) ^ p + (948196091/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496683553/500000000 : ℝ)) (y := (948196091/1000000000 : ℝ)) (X := (16231145872047/20000000000000 : ℝ)) (Y := (18844290394121/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1941563197/1000000000 : ℝ)) (τ := (948196091/1000000000 : ℝ)) (σ := (496683553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (416367798/437595397 : ℝ) ^ p + (434318184/437595397 : ℝ) ^ p := by
    exact cert_lt (x := (416367798/437595397 : ℝ)) (y := (434318184/437595397 : ℝ)) (X := (21010563132869/100000000000000 : ℝ)) (Y := (78989437918563/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (948196091/1000000000 : ℝ)) (n' := (437595397/500000000 : ℝ)) (Ab := (208183899/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1941563197/1000000000 : ℝ)) (τ := (948196091/1000000000 : ℝ)) (σ := (496683553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (948196091/1000000000 : ℝ)) (n' := (437595397/500000000 : ℝ)) (Ab := (208183899/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1941563197/1000000000 : ℝ)) (τ := (948196091/1000000000 : ℝ)) (σ := (496683553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (948196091/1000000000 : ℝ)) (n' := (437595397/500000000 : ℝ)) (Ab := (208183899/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1941563197/1000000000 : ℝ)) (τ := (948196091/1000000000 : ℝ)) (σ := (496683553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (948196091/1000000000 : ℝ)) (n' := (437595397/500000000 : ℝ)) (Ab := (208183899/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1941563197/1000000000 : ℝ)) (τ := (948196091/1000000000 : ℝ)) (σ := (496683553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (948196091/1000000000 : ℝ)) (n' := (437595397/500000000 : ℝ)) (Ab := (208183899/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1941563197/1000000000 : ℝ)) (τ := (948196091/1000000000 : ℝ)) (σ := (496683553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1714242314/1841444021 : ℝ) ^ p + (1834889595/1841444021 : ℝ) ^ p := by
    exact cert_lt (x := (1714242314/1841444021 : ℝ)) (y := (1834889595/1841444021 : ℝ)) (X := (2646104727657/25000000000000 : ℝ)) (Y := (89415581474271/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1093484737/1158555979 : ℝ) ^ p + (1152001553/1158555979 : ℝ) ^ p := by
    exact cert_lt (x := (1093484737/1158555979 : ℝ)) (y := (1152001553/1158555979 : ℝ)) (X := (16306196459899/100000000000000 : ℝ)) (Y := (83693804273597/100000000000000 : ℝ)) 251 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496683553/500000000 : ℝ)) (U := (1158555979/1000000000 : ℝ)) (Ab := (857121157/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (948196091/1000000000 : ℝ)) (σ := (496683553/500000000 : ℝ)) (Ab := (1093484737/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab085
