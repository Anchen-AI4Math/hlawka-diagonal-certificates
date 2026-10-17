import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 40, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab040 (p : ℝ) (hpa : (57/2 : ℝ) ≤ p) (hpb : p ≤ (457/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (179838959519/12625500000000 : ℝ) (456087/62500000 : ℝ) (400000075753/2525100000000 : ℝ) (591/500 : ℝ) (976024359/500000000 : ℝ) (975972417/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289235117/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10863/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1111/2000 : ℝ)
      else (8211/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11487/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (179838959519/12625500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (456087/62500000 : ℝ) := by norm_num
  have pc0 : 1 < (234836959/250000000 : ℝ) ^ p + (124200607/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (234836959/250000000 : ℝ)) (y := (124200607/125000000 : ℝ)) (X := (3348768807141/20000000000000 : ℝ)) (Y := (16651235172949/20000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124200607/125000000 : ℝ) ^ p + (234836959/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124200607/125000000 : ℝ)) (y := (234836959/250000000 : ℝ)) (X := (16651235172949/20000000000000 : ℝ)) (Y := (3348768807141/20000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (483238173/250000000 : ℝ)) (τ := (234836959/250000000 : ℝ)) (σ := (124200607/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (273855669/289021910 : ℝ) ^ p + (143294723/144510955 : ℝ) ^ p := by
    exact cert_lt (x := (273855669/289021910 : ℝ)) (y := (143294723/144510955 : ℝ)) (X := (21447641742049/100000000000000 : ℝ)) (Y := (15710471944767/20000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (234836959/250000000 : ℝ)) (n' := (86706573/100000000 : ℝ)) (Ab := (821567007/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (471329777/500000000 : ℝ) ^ p + (992857337/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471329777/500000000 : ℝ)) (y := (992857337/1000000000 : ℝ)) (X := (1851446108101/10000000000000 : ℝ)) (Y := (40742778521801/50000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992857337/1000000000 : ℝ) ^ p + (471329777/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992857337/1000000000 : ℝ)) (y := (471329777/500000000 : ℝ)) (X := (40742778521801/50000000000000 : ℝ)) (Y := (1851446108101/10000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1935516891/1000000000 : ℝ)) (τ := (471329777/500000000 : ℝ)) (σ := (992857337/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (412526019/435431029 : ℝ) ^ p + (431782333/435431029 : ℝ) ^ p := by
    exact cert_lt (x := (412526019/435431029 : ℝ)) (y := (431782333/435431029 : ℝ)) (X := (4272916870183/20000000000000 : ℝ)) (Y := (78635416965759/100000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (471329777/500000000 : ℝ)) (n' := (435431029/500000000 : ℝ)) (Ab := (412526019/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (942753747/1000000000 : ℝ) ^ p + (496417379/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (942753747/1000000000 : ℝ)) (y := (496417379/500000000 : ℝ)) (X := (4641843728261/25000000000000 : ℝ)) (Y := (1628652890081/2000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496417379/500000000 : ℝ) ^ p + (942753747/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496417379/500000000 : ℝ)) (y := (942753747/1000000000 : ℝ)) (X := (1628652890081/2000000000000 : ℝ)) (Y := (4641843728261/25000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (387117701/200000000 : ℝ)) (τ := (942753747/1000000000 : ℝ)) (σ := (496417379/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (825150975/870969841 : ℝ) ^ p + (863672449/870969841 : ℝ) ^ p := by
    exact cert_lt (x := (825150975/870969841 : ℝ)) (y := (863672449/870969841 : ℝ)) (X := (5340558880029/25000000000000 : ℝ)) (Y := (19659441434131/25000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (942753747/1000000000 : ℝ)) (n' := (870969841/1000000000 : ℝ)) (Ab := (33006039/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (942756411/1000000000 : ℝ) ^ p + (496417059/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (942756411/1000000000 : ℝ)) (y := (496417059/500000000 : ℝ)) (X := (18568873560877/100000000000000 : ℝ)) (Y := (81431145185553/100000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496417059/500000000 : ℝ) ^ p + (942756411/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496417059/500000000 : ℝ)) (y := (942756411/1000000000 : ℝ)) (X := (81431145185553/100000000000000 : ℝ)) (Y := (18568873560877/100000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1935590529/1000000000 : ℝ)) (τ := (942756411/1000000000 : ℝ)) (σ := (496417059/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (825153773/870972889 : ℝ) ^ p + (863675497/870972889 : ℝ) ^ p := by
    exact cert_lt (x := (825153773/870972889 : ℝ)) (y := (863675497/870972889 : ℝ)) (X := (21362169225161/100000000000000 : ℝ)) (Y := (19659458037511/25000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (942756411/1000000000 : ℝ)) (n' := (870972889/1000000000 : ℝ)) (Ab := (825153773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (471378243/500000000 : ℝ) ^ p + (9928341/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (471378243/500000000 : ℝ)) (y := (9928341/10000000 : ℝ)) (X := (18568915754229/100000000000000 : ℝ)) (Y := (16286220603521/20000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (9928341/10000000 : ℝ) ^ p + (471378243/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (9928341/10000000 : ℝ)) (y := (471378243/500000000 : ℝ)) (X := (16286220603521/20000000000000 : ℝ)) (Y := (18568915754229/100000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (967795293/500000000 : ℝ)) (τ := (471378243/500000000 : ℝ)) (σ := (9928341/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (275051284/290324325 : ℝ) ^ p + (287891861/290324325 : ℝ) ^ p := by
    exact cert_lt (x := (275051284/290324325 : ℝ)) (y := (287891861/290324325 : ℝ)) (X := (2136216739443/10000000000000 : ℝ)) (Y := (7863783402391/10000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (471378243/500000000 : ℝ)) (n' := (34838919/40000000 : ℝ)) (Ab := (206288463/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (942756489/1000000000 : ℝ) ^ p + (992834099/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942756489/1000000000 : ℝ)) (y := (992834099/1000000000 : ℝ)) (X := (3713783488393/20000000000000 : ℝ)) (Y := (40715550337471/50000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992834099/1000000000 : ℝ) ^ p + (942756489/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992834099/1000000000 : ℝ)) (y := (942756489/1000000000 : ℝ)) (X := (40715550337471/50000000000000 : ℝ)) (Y := (3713783488393/20000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (483897647/250000000 : ℝ)) (τ := (942756489/1000000000 : ℝ)) (σ := (992834099/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (412576927/435486489 : ℝ) ^ p + (143945931/145162163 : ℝ) ^ p := by
    exact cert_lt (x := (412576927/435486489 : ℝ)) (y := (143945931/145162163 : ℝ)) (X := (21362166771683/100000000000000 : ℝ)) (Y := (39318917044639/50000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (942756489/1000000000 : ℝ)) (n' := (435486489/500000000 : ℝ)) (Ab := (412576927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (483897647/250000000 : ℝ)) (τ := (942756489/1000000000 : ℝ)) (σ := (992834099/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (942756489/1000000000 : ℝ)) (n' := (435486489/500000000 : ℝ)) (Ab := (412576927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (483897647/250000000 : ℝ)) (τ := (942756489/1000000000 : ℝ)) (σ := (992834099/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (942756489/1000000000 : ℝ)) (n' := (435486489/500000000 : ℝ)) (Ab := (412576927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (483897647/250000000 : ℝ)) (τ := (942756489/1000000000 : ℝ)) (σ := (992834099/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (942756489/1000000000 : ℝ)) (n' := (435486489/500000000 : ℝ)) (Ab := (412576927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (483897647/250000000 : ℝ)) (τ := (942756489/1000000000 : ℝ)) (σ := (992834099/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (942756489/1000000000 : ℝ)) (n' := (435486489/500000000 : ℝ)) (Ab := (412576927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (483897647/250000000 : ℝ)) (τ := (942756489/1000000000 : ℝ)) (σ := (992834099/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (426104070/460764883 : ℝ) ^ p + (458940535/460764883 : ℝ) ^ p := by
    exact cert_lt (x := (426104070/460764883 : ℝ)) (y := (458940535/460764883 : ℝ)) (X := (2142604979553/20000000000000 : ℝ)) (Y := (22321743836269/25000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1086289283/1156940468 : ℝ) ^ p + (287410769/289235117 : ℝ) ^ p := by
    exact cert_lt (x := (1086289283/1156940468 : ℝ)) (y := (287410769/289235117 : ℝ)) (X := (16533789747987/100000000000000 : ℝ)) (Y := (83466211061151/100000000000000 : ℝ)) 457 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992834099/1000000000 : ℝ)) (U := (289235117/250000000 : ℝ)) (Ab := (42610407/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (942756489/1000000000 : ℝ)) (σ := (992834099/1000000000 : ℝ)) (Ab := (1086289283/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab040
