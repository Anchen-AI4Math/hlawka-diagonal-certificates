import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 119, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab119 (p : ℝ) (hpa : (791/32 : ℝ) ≤ p) (hpb : p ≤ (99/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2086338088127/107971500000000 : ℝ) (9936279/1000000000 : ℝ) (4000000647829/21594300000000 : ℝ) (3033/2500 : ℝ) (194476517/100000000 : ℝ) (972348157/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596942823/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11157/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4641/10000 : ℝ)
      else (779/1000 : ℝ) ≤ X j i ∧ X j i ≤ (2371/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2086338088127/107971500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9936279/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (922973543/1000000000 : ℝ) ^ p + (497019663/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922973543/1000000000 : ℝ)) (y := (497019663/500000000 : ℝ)) (X := (6877078718911/50000000000000 : ℝ)) (Y := (1724917226673/2000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497019663/500000000 : ℝ) ^ p + (922973543/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497019663/500000000 : ℝ)) (y := (922973543/1000000000 : ℝ)) (X := (1724917226673/2000000000000 : ℝ)) (Y := (6877078718911/50000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1917012869/1000000000 : ℝ)) (τ := (922973543/1000000000 : ℝ)) (σ := (497019663/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (787695193/832120551 : ℝ) ^ p + (91353808/92457839 : ℝ) ^ p := by
    exact cert_lt (x := (787695193/832120551 : ℝ)) (y := (91353808/92457839 : ℝ)) (X := (401860868481/1562500000000 : ℝ)) (Y := (74280905336877/100000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (922973543/1000000000 : ℝ)) (n' := (832120551/1000000000 : ℝ)) (Ab := (787695193/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (464229951/500000000 : ℝ) ^ p + (993014963/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464229951/500000000 : ℝ)) (y := (993014963/1000000000 : ℝ)) (X := (3981787039641/25000000000000 : ℝ)) (Y := (8407286878681/10000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993014963/1000000000 : ℝ) ^ p + (464229951/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993014963/1000000000 : ℝ)) (y := (464229951/500000000 : ℝ)) (X := (8407286878681/10000000000000 : ℝ)) (Y := (3981787039641/25000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (384294973/200000000 : ℝ)) (τ := (464229951/500000000 : ℝ)) (σ := (993014963/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (396796772/419288963 : ℝ) ^ p + (828641647/838577926 : ℝ) ^ p := by
    exact cert_lt (x := (396796772/419288963 : ℝ)) (y := (828641647/838577926 : ℝ)) (X := (25547818502117/100000000000000 : ℝ)) (Y := (14890436510771/20000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (464229951/500000000 : ℝ)) (n' := (419288963/500000000 : ℝ)) (Ab := (99199193/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (232171087/250000000 : ℝ) ^ p + (992969331/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232171087/250000000 : ℝ)) (y := (992969331/1000000000 : ℝ)) (X := (250354928469/1562500000000 : ℝ)) (Y := (41988650909309/50000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992969331/1000000000 : ℝ) ^ p + (232171087/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992969331/1000000000 : ℝ)) (y := (232171087/250000000 : ℝ)) (X := (41988650909309/50000000000000 : ℝ)) (Y := (250354928469/1562500000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1921653679/1000000000 : ℝ)) (τ := (232171087/250000000 : ℝ)) (σ := (992969331/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (264611359/279613766 : ℝ) ^ p + (276301673/279613766 : ℝ) ^ p := by
    exact cert_lt (x := (264611359/279613766 : ℝ)) (y := (276301673/279613766 : ℝ)) (X := (638522028569/2500000000000 : ℝ)) (Y := (74459120307463/100000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (232171087/250000000 : ℝ)) (n' := (419420649/500000000 : ℝ)) (Ab := (793834077/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (928693437/1000000000 : ℝ) ^ p + (992967477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (928693437/1000000000 : ℝ)) (y := (992967477/1000000000 : ℝ)) (X := (16026597013037/100000000000000 : ℝ)) (Y := (1312084706191/1562500000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992967477/1000000000 : ℝ) ^ p + (928693437/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992967477/1000000000 : ℝ)) (y := (928693437/1000000000 : ℝ)) (X := (1312084706191/1562500000000 : ℝ)) (Y := (16026597013037/100000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (960830457/500000000 : ℝ)) (τ := (928693437/1000000000 : ℝ)) (σ := (992967477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (396921908/419425981 : ℝ) ^ p + (828915683/838851962 : ℝ) ^ p := by
    exact cert_lt (x := (396921908/419425981 : ℝ)) (y := (828915683/838851962 : ℝ)) (X := (5108120036723/20000000000000 : ℝ)) (Y := (14891880228037/20000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (928693437/1000000000 : ℝ)) (n' := (419425981/500000000 : ℝ)) (Ab := (99230477/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464346903/500000000 : ℝ) ^ p + (992967401/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464346903/500000000 : ℝ)) (y := (992967401/1000000000 : ℝ)) (X := (2003344327371/12500000000000 : ℝ)) (Y := (83973262123681/100000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992967401/1000000000 : ℝ) ^ p + (464346903/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992967401/1000000000 : ℝ)) (y := (464346903/500000000 : ℝ)) (X := (83973262123681/100000000000000 : ℝ)) (Y := (2003344327371/12500000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1921661207/1000000000 : ℝ)) (τ := (464346903/500000000 : ℝ)) (σ := (992967401/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (264614737/279617465 : ℝ) ^ p + (276305372/279617465 : ℝ) ^ p := by
    exact cert_lt (x := (264614737/279617465 : ℝ)) (y := (276305372/279617465 : ℝ)) (X := (6385147106079/25000000000000 : ℝ)) (Y := (930742656787/1250000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464346903/500000000 : ℝ)) (n' := (167770479/200000000 : ℝ)) (Ab := (793844211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (928693821/1000000000 : ℝ) ^ p + (496483699/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (928693821/1000000000 : ℝ)) (y := (496483699/500000000 : ℝ)) (X := (3205352205149/20000000000000 : ℝ)) (Y := (83973255844507/100000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496483699/500000000 : ℝ) ^ p + (928693821/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496483699/500000000 : ℝ)) (y := (928693821/1000000000 : ℝ)) (X := (83973255844507/100000000000000 : ℝ)) (Y := (3205352205149/20000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921661219/1000000000 : ℝ)) (τ := (928693821/1000000000 : ℝ)) (σ := (496483699/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (793844227/838852412 : ℝ) ^ p + (828916133/838852412 : ℝ) ^ p := by
    exact cert_lt (x := (793844227/838852412 : ℝ)) (y := (828916133/838852412 : ℝ)) (X := (25540588354343/100000000000000 : ℝ)) (Y := (18614853247661/25000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (928693821/1000000000 : ℝ)) (n' := (209713103/250000000 : ℝ)) (Ab := (793844227/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1921661219/1000000000 : ℝ)) (τ := (928693821/1000000000 : ℝ)) (σ := (496483699/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (928693821/1000000000 : ℝ)) (n' := (209713103/250000000 : ℝ)) (Ab := (793844227/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1921661219/1000000000 : ℝ)) (τ := (928693821/1000000000 : ℝ)) (σ := (496483699/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (928693821/1000000000 : ℝ)) (n' := (209713103/250000000 : ℝ)) (Ab := (793844227/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1921661219/1000000000 : ℝ)) (τ := (928693821/1000000000 : ℝ)) (σ := (496483699/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (928693821/1000000000 : ℝ)) (n' := (209713103/250000000 : ℝ)) (Ab := (793844227/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1921661219/1000000000 : ℝ)) (τ := (928693821/1000000000 : ℝ)) (σ := (496483699/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (928693821/1000000000 : ℝ)) (n' := (209713103/250000000 : ℝ)) (Ab := (793844227/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1921661219/1000000000 : ℝ)) (τ := (928693821/1000000000 : ℝ)) (σ := (496483699/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (151087631/164192214 : ℝ) ^ p + (598726025/602038118 : ℝ) ^ p := by
    exact cert_lt (x := (151087631/164192214 : ℝ)) (y := (598726025/602038118 : ℝ)) (X := (12762616758341/100000000000000 : ℝ)) (Y := (87237383440193/100000000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (557825923/596942823 : ℝ) ^ p + (394649789/397961882 : ℝ) ^ p := by
    exact cert_lt (x := (557825923/596942823 : ℝ)) (y := (394649789/397961882 : ℝ)) (X := (4671404342651/25000000000000 : ℝ)) (Y := (10164297932067/12500000000000 : ℝ)) 99 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496483699/500000000 : ℝ)) (U := (596942823/500000000 : ℝ)) (Ab := (1661963941/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (928693821/1000000000 : ℝ)) (σ := (496483699/500000000 : ℝ)) (Ab := (557825923/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab119
