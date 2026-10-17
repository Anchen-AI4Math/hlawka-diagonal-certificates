import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 108, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab108 (p : ℝ) (hpa : (195/8 : ℝ) ≤ p) (hpb : p ≤ (781/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (104493148579/5323500000000 : ℝ) (10097423/1000000000 : ℝ) (200000031941/1064700000000 : ℝ) (3033/2500 : ℝ) (7593743/3906250 : ℝ) (971963713/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596872931/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5573/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2311/5000 : ℝ)
      else (1943/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11853/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (104493148579/5323500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10097423/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (184366719/200000000 : ℝ) ^ p + (993972547/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184366719/200000000 : ℝ)) (y := (993972547/1000000000 : ℝ)) (X := (1714789661837/12500000000000 : ℝ)) (Y := (21570425111493/25000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993972547/1000000000 : ℝ) ^ p + (184366719/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993972547/1000000000 : ℝ)) (y := (184366719/200000000 : ℝ)) (X := (21570425111493/25000000000000 : ℝ)) (Y := (1714789661837/12500000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (957903071/500000000 : ℝ)) (τ := (184366719/200000000 : ℝ)) (σ := (993972547/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (786190664/831071835 : ℝ) ^ p + (820974412/831071835 : ℝ) ^ p := by
    exact cert_lt (x := (786190664/831071835 : ℝ)) (y := (820974412/831071835 : ℝ)) (X := (6448945024597/25000000000000 : ℝ)) (Y := (14840844170423/20000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184366719/200000000 : ℝ)) (n' := (166214367/200000000 : ℝ)) (Ab := (98273833/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (927367207/1000000000 : ℝ) ^ p + (124117717/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (927367207/1000000000 : ℝ)) (y := (124117717/125000000 : ℝ)) (X := (3175174825229/20000000000000 : ℝ)) (Y := (42062071711061/50000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124117717/125000000 : ℝ) ^ p + (927367207/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124117717/125000000 : ℝ)) (y := (927367207/1000000000 : ℝ)) (X := (42062071711061/50000000000000 : ℝ)) (Y := (3175174825229/20000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1920308943/1000000000 : ℝ)) (τ := (927367207/1000000000 : ℝ)) (σ := (124117717/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (132023797/139599260 : ℝ) ^ p + (827498137/837595560 : ℝ) ^ p := by
    exact cert_lt (x := (132023797/139599260 : ℝ)) (y := (827498137/837595560 : ℝ)) (X := (6405524144011/25000000000000 : ℝ)) (Y := (7437790446131/10000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (927367207/1000000000 : ℝ)) (n' := (20939889/25000000 : ℝ)) (Ab := (396071391/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (18551959/20000000 : ℝ) ^ p + (992894949/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18551959/20000000 : ℝ)) (y := (992894949/1000000000 : ℝ)) (X := (15972563921239/100000000000000 : ℝ)) (Y := (8402745295193/10000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992894949/1000000000 : ℝ) ^ p + (18551959/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (992894949/1000000000 : ℝ)) (y := (18551959/20000000 : ℝ)) (X := (8402745295193/10000000000000 : ℝ)) (Y := (15972563921239/100000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1920492899/1000000000 : ℝ)) (τ := (18551959/20000000 : ℝ)) (σ := (992894949/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (46611187/49286280 : ℝ) ^ p + (827769337/837866760 : ℝ) ^ p := by
    exact cert_lt (x := (46611187/49286280 : ℝ)) (y := (827769337/837866760 : ℝ)) (X := (25614927026971/100000000000000 : ℝ)) (Y := (74385074530023/100000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (18551959/20000000 : ℝ)) (n' := (20946669/25000000 : ℝ)) (Ab := (792390179/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (927607473/1000000000 : ℝ) ^ p + (992893011/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927607473/1000000000 : ℝ)) (y := (992893011/1000000000 : ℝ)) (X := (7988283259163/50000000000000 : ℝ)) (Y := (42011725080967/50000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992893011/1000000000 : ℝ) ^ p + (927607473/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992893011/1000000000 : ℝ)) (y := (927607473/1000000000 : ℝ)) (X := (42011725080967/50000000000000 : ℝ)) (Y := (7988283259163/50000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (480125121/250000000 : ℝ)) (τ := (927607473/1000000000 : ℝ)) (σ := (992893011/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (792400387/837877951 : ℝ) ^ p + (827780528/837877951 : ℝ) ^ p := by
    exact cert_lt (x := (792400387/837877951 : ℝ)) (y := (827780528/837877951 : ℝ)) (X := (5122926141359/20000000000000 : ℝ)) (Y := (74385370315629/100000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (927607473/1000000000 : ℝ)) (n' := (837877951/1000000000 : ℝ)) (Ab := (792400387/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (463803933/500000000 : ℝ) ^ p + (992892931/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (463803933/500000000 : ℝ)) (y := (992892931/1000000000 : ℝ)) (X := (15976731720201/100000000000000 : ℝ)) (Y := (16804656986403/20000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992892931/1000000000 : ℝ) ^ p + (463803933/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992892931/1000000000 : ℝ)) (y := (463803933/500000000 : ℝ)) (X := (16804656986403/20000000000000 : ℝ)) (Y := (15976731720201/100000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1920500797/1000000000 : ℝ)) (τ := (463803933/500000000 : ℝ)) (σ := (992892931/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (792400809/837878413 : ℝ) ^ p + (827780990/837878413 : ℝ) ^ p := by
    exact cert_lt (x := (792400809/837878413 : ℝ)) (y := (827780990/837878413 : ℝ)) (X := (1600913683291/6250000000000 : ℝ)) (Y := (18596345631613/25000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (463803933/500000000 : ℝ)) (n' := (837878413/1000000000 : ℝ)) (Ab := (792400809/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (463803941/500000000 : ℝ) ^ p + (1939244/1953125 : ℝ) ^ p := by
    exact cert_lt (x := (463803941/500000000 : ℝ)) (y := (1939244/1953125 : ℝ)) (X := (3994184611503/25000000000000 : ℝ)) (Y := (84023278735899/100000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (1939244/1953125 : ℝ) ^ p + (463803941/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (1939244/1953125 : ℝ)) (y := (463803941/500000000 : ℝ)) (X := (84023278735899/100000000000000 : ℝ)) (Y := (3994184611503/25000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (192050081/100000000 : ℝ)) (τ := (463803941/500000000 : ℝ)) (σ := (1939244/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (792400825/837878431 : ℝ) ^ p + (827781008/837878431 : ℝ) ^ p := by
    exact cert_lt (x := (792400825/837878431 : ℝ)) (y := (827781008/837878431 : ℝ)) (X := (25614618125561/100000000000000 : ℝ)) (Y := (37192691501099/50000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (463803941/500000000 : ℝ)) (n' := (837878431/1000000000 : ℝ)) (Ab := (31696033/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (192050081/100000000 : ℝ)) (τ := (463803941/500000000 : ℝ)) (σ := (1939244/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (463803941/500000000 : ℝ)) (n' := (837878431/1000000000 : ℝ)) (Ab := (31696033/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (192050081/100000000 : ℝ)) (τ := (463803941/500000000 : ℝ)) (σ := (1939244/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (463803941/500000000 : ℝ)) (n' := (837878431/1000000000 : ℝ)) (Ab := (31696033/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (192050081/100000000 : ℝ)) (τ := (463803941/500000000 : ℝ)) (σ := (1939244/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (463803941/500000000 : ℝ)) (n' := (837878431/1000000000 : ℝ)) (Ab := (31696033/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (192050081/100000000 : ℝ)) (τ := (463803941/500000000 : ℝ)) (σ := (1939244/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (463803941/500000000 : ℝ)) (n' := (837878431/1000000000 : ℝ)) (Ab := (31696033/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (192050081/100000000 : ℝ)) (τ := (463803941/500000000 : ℝ)) (σ := (1939244/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1660277855/1806254138 : ℝ) ^ p + (1796156715/1806254138 : ℝ) ^ p := by
    exact cert_lt (x := (1660277855/1806254138 : ℝ)) (y := (1796156715/1806254138 : ℝ)) (X := (6393639125611/50000000000000 : ℝ)) (Y := (87212721957533/100000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (557275440/596872931 : ℝ) ^ p + (1183648439/1193745862 : ℝ) ^ p := by
    exact cert_lt (x := (557275440/596872931 : ℝ)) (y := (1183648439/1193745862 : ℝ)) (X := (18724117675493/100000000000000 : ℝ)) (Y := (81275882877279/100000000000000 : ℝ)) 781 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (1939244/1953125 : ℝ)) (U := (596872931/500000000 : ℝ)) (Ab := (332055571/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (463803941/500000000 : ℝ)) (σ := (1939244/1953125 : ℝ)) (Ab := (6965943/6250000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab108
