import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 21, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab021 (p : ℝ) (hpa : (437/16 : ℝ) ≤ p) (hpb : p ≤ (219/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1446376288939/96795500000000 : ℝ) (957917/125000000 : ℝ) (3200000580773/19359100000000 : ℝ) (591/500 : ℝ) (974997429/500000000 : ℝ) (974940937/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144525347/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10829/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5513/10000 : ℝ)
      else (1021/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11477/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1446376288939/96795500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (957917/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (468291863/500000000 : ℝ) ^ p + (993374683/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468291863/500000000 : ℝ)) (y := (993374683/1000000000 : ℝ)) (X := (16637511680913/100000000000000 : ℝ)) (Y := (83362507316713/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993374683/1000000000 : ℝ) ^ p + (468291863/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993374683/1000000000 : ℝ)) (y := (468291863/500000000 : ℝ)) (X := (83362507316713/100000000000000 : ℝ)) (Y := (16637511680913/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1929958409/1000000000 : ℝ)) (τ := (468291863/500000000 : ℝ)) (σ := (993374683/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817772489/864822313 : ℝ) ^ p + (857158977/864822313 : ℝ) ^ p := by
    exact cert_lt (x := (817772489/864822313 : ℝ)) (y := (857158977/864822313 : ℝ)) (X := (10812125510807/50000000000000 : ℝ)) (Y := (39187874976861/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (468291863/500000000 : ℝ)) (n' := (864822313/1000000000 : ℝ)) (Ab := (817772489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939994443/1000000000 : ℝ) ^ p + (992609201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939994443/1000000000 : ℝ)) (y := (992609201/1000000000 : ℝ)) (X := (18378273444669/100000000000000 : ℝ)) (Y := (5101358985209/6250000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992609201/1000000000 : ℝ) ^ p + (939994443/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992609201/1000000000 : ℝ)) (y := (939994443/1000000000 : ℝ)) (X := (5101358985209/6250000000000 : ℝ)) (Y := (18378273444669/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (483150911/250000000 : ℝ)) (τ := (939994443/1000000000 : ℝ)) (σ := (992609201/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821364430/868748449 : ℝ) ^ p + (861085113/868748449 : ℝ) ^ p := by
    exact cert_lt (x := (821364430/868748449 : ℝ)) (y := (861085113/868748449 : ℝ)) (X := (21537516340839/100000000000000 : ℝ)) (Y := (78462485086501/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939994443/1000000000 : ℝ)) (n' := (868748449/1000000000 : ℝ)) (Ab := (82136443/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (940096941/1000000000 : ℝ) ^ p + (248146197/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (940096941/1000000000 : ℝ)) (y := (248146197/250000000 : ℝ)) (X := (3686642307409/20000000000000 : ℝ)) (Y := (40783403567797/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248146197/250000000 : ℝ) ^ p + (940096941/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248146197/250000000 : ℝ)) (y := (940096941/1000000000 : ℝ)) (X := (40783403567797/50000000000000 : ℝ)) (Y := (3686642307409/20000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1932681729/1000000000 : ℝ)) (τ := (940096941/1000000000 : ℝ)) (σ := (248146197/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (821472165/868866218 : ℝ) ^ p + (430601441/434433109 : ℝ) ^ p := by
    exact cert_lt (x := (821472165/868866218 : ℝ)) (y := (430601441/434433109 : ℝ)) (X := (21534925132667/100000000000000 : ℝ)) (Y := (39232538059791/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (940096941/1000000000 : ℝ)) (n' := (434433109/500000000 : ℝ)) (Ab := (164294433/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (235025001/250000000 : ℝ) ^ p + (992584057/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (235025001/250000000 : ℝ)) (y := (992584057/1000000000 : ℝ)) (X := (1843485571247/10000000000000 : ℝ)) (Y := (4078258135707/5000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992584057/1000000000 : ℝ) ^ p + (235025001/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992584057/1000000000 : ℝ)) (y := (235025001/250000000 : ℝ)) (X := (4078258135707/5000000000000 : ℝ)) (Y := (1843485571247/10000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1932684061/1000000000 : ℝ)) (τ := (235025001/250000000 : ℝ)) (σ := (992584057/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (821475384/868869737 : ℝ) ^ p + (861206401/868869737 : ℝ) ^ p := by
    exact cert_lt (x := (821475384/868869737 : ℝ)) (y := (861206401/868869737 : ℝ)) (X := (21534847593133/100000000000000 : ℝ)) (Y := (78465153531481/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (235025001/250000000 : ℝ)) (n' := (868869737/1000000000 : ℝ)) (Ab := (102684423/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (188020019/200000000 : ℝ) ^ p + (198516807/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (188020019/200000000 : ℝ)) (y := (198516807/200000000 : ℝ)) (X := (9217452281077/50000000000000 : ℝ)) (Y := (81565113224523/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198516807/200000000 : ℝ) ^ p + (188020019/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198516807/200000000 : ℝ)) (y := (188020019/200000000 : ℝ)) (X := (81565113224523/100000000000000 : ℝ)) (Y := (9217452281077/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (193268413/100000000 : ℝ)) (τ := (188020019/200000000 : ℝ)) (σ := (198516807/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (410737740/434434921 : ℝ) ^ p + (430603253/434434921 : ℝ) ^ p := by
    exact cert_lt (x := (410737740/434434921 : ℝ)) (y := (430603253/434434921 : ℝ)) (X := (2691855655581/12500000000000 : ℝ)) (Y := (78465155841291/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (188020019/200000000 : ℝ)) (n' := (434434921/500000000 : ℝ)) (Ab := (20536887/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (940100099/1000000000 : ℝ) ^ p + (496292017/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (940100099/1000000000 : ℝ)) (y := (496292017/500000000 : ℝ)) (X := (4608726677349/25000000000000 : ℝ)) (Y := (16313022194999/20000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496292017/500000000 : ℝ) ^ p + (940100099/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496292017/500000000 : ℝ)) (y := (940100099/1000000000 : ℝ)) (X := (16313022194999/20000000000000 : ℝ)) (Y := (4608726677349/25000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (410737742/434434923 : ℝ) ^ p + (430603255/434434923 : ℝ) ^ p := by
    exact cert_lt (x := (410737742/434434923 : ℝ)) (y := (430603255/434434923 : ℝ)) (X := (21534845401227/100000000000000 : ℝ)) (Y := (78465155929283/100000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (n' := (434434923/500000000 : ℝ)) (Ab := (205368871/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932684133/1000000000 : ℝ)) (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1699685233/1843797224 : ℝ) ^ p + (229516736/230474653 : ℝ) ^ p := by
    exact cert_lt (x := (1699685233/1843797224 : ℝ)) (y := (229516736/230474653 : ℝ)) (X := (2693891274447/25000000000000 : ℝ)) (Y := (17844887045091/20000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082895425/1156202776 : ℝ) ^ p + (143567430/144525347 : ℝ) ^ p := by
    exact cert_lt (x := (1082895425/1156202776 : ℝ)) (y := (143567430/144525347 : ℝ)) (X := (8321852178107/50000000000000 : ℝ)) (Y := (41678148140203/50000000000000 : ℝ)) 219 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496292017/500000000 : ℝ)) (U := (144525347/125000000 : ℝ)) (Ab := (1699685233/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (940100099/1000000000 : ℝ)) (σ := (496292017/500000000 : ℝ)) (Ab := (43315817/40000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab021
