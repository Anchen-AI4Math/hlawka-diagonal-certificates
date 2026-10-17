import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 154, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab154 (p : ℝ) (hpa : (413/16 : ℝ) ≤ p) (hpb : p ≤ (827/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (518935200971/28187250000000 : ℝ) (9455677/1000000000 : ℝ) (2000000338247/11274900000000 : ℝ) (3033/2500 : ℝ) (60845987/31250000 : ℝ) (48675209/50000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597163827/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11191/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(939/2000 : ℝ)
      else (1961/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11863/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (518935200971/28187250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9455677/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (185277977/200000000 : ℝ) ^ p + (994242713/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185277977/200000000 : ℝ)) (y := (994242713/1000000000 : ℝ)) (X := (13862047547227/100000000000000 : ℝ)) (Y := (21534492993233/25000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994242713/1000000000 : ℝ) ^ p + (185277977/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (994242713/1000000000 : ℝ)) (y := (185277977/200000000 : ℝ)) (X := (21534492993233/25000000000000 : ℝ)) (Y := (13862047547227/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (960316299/500000000 : ℝ)) (τ := (185277977/200000000 : ℝ)) (σ := (994242713/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (792211999/835239551 : ℝ) ^ p + (825783874/835239551 : ℝ) ^ p := by
    exact cert_lt (x := (792211999/835239551 : ℝ)) (y := (825783874/835239551 : ℝ)) (X := (25490507963767/100000000000000 : ℝ)) (Y := (2328421661837/3125000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (185277977/200000000 : ℝ)) (n' := (835239551/1000000000 : ℝ)) (Ab := (792211999/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931727127/1000000000 : ℝ) ^ p + (198647863/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (931727127/1000000000 : ℝ)) (y := (198647863/200000000 : ℝ)) (X := (1608073427753/10000000000000 : ℝ)) (Y := (10489910573313/12500000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198647863/200000000 : ℝ) ^ p + (931727127/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198647863/200000000 : ℝ)) (y := (931727127/1000000000 : ℝ)) (X := (10489910573313/12500000000000 : ℝ)) (Y := (1608073427753/10000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (962483221/500000000 : ℝ)) (τ := (931727127/1000000000 : ℝ)) (σ := (198647863/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (797941665/841490506 : ℝ) ^ p + (832034829/841490506 : ℝ) ^ p := by
    exact cert_lt (x := (797941665/841490506 : ℝ)) (y := (832034829/841490506 : ℝ)) (X := (25326543663113/100000000000000 : ℝ)) (Y := (74673457541993/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931727127/1000000000 : ℝ)) (n' := (420745253/500000000 : ℝ)) (Ab := (159588333/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (931933071/1000000000 : ℝ) ^ p + (248299277/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (931933071/1000000000 : ℝ)) (y := (248299277/250000000 : ℝ)) (X := (2021605744479/12500000000000 : ℝ)) (Y := (83827172067853/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248299277/250000000 : ℝ) ^ p + (931933071/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248299277/250000000 : ℝ)) (y := (931933071/1000000000 : ℝ)) (X := (83827172067853/100000000000000 : ℝ)) (Y := (2021605744479/12500000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1925130179/1000000000 : ℝ)) (τ := (931933071/1000000000 : ℝ)) (σ := (248299277/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (798162071/841731001 : ℝ) ^ p + (15703308/15881717 : ℝ) ^ p := by
    exact cert_lt (x := (798162071/841731001 : ℝ)) (y := (15703308/15881717 : ℝ)) (X := (25320276911319/100000000000000 : ℝ)) (Y := (74679724014809/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (931933071/1000000000 : ℝ)) (n' := (841731001/1000000000 : ℝ)) (Ab := (798162071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (46597047/50000000 : ℝ) ^ p + (99319549/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (46597047/50000000 : ℝ)) (y := (99319549/100000000 : ℝ)) (X := (16176375530351/100000000000000 : ℝ)) (Y := (10477955360149/12500000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99319549/100000000 : ℝ) ^ p + (46597047/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (99319549/100000000 : ℝ)) (y := (46597047/50000000 : ℝ)) (X := (10477955360149/12500000000000 : ℝ)) (Y := (16176375530351/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (192513643/100000000 : ℝ)) (τ := (46597047/50000000 : ℝ)) (σ := (99319549/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (798170492/841740189 : ℝ) ^ p + (832284512/841740189 : ℝ) ^ p := by
    exact cert_lt (x := (798170492/841740189 : ℝ)) (y := (832284512/841740189 : ℝ)) (X := (25320037996027/100000000000000 : ℝ)) (Y := (37339981680753/50000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (46597047/50000000 : ℝ)) (n' := (841740189/1000000000 : ℝ)) (Ab := (199542623/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (931941241/1000000000 : ℝ) ^ p + (248298857/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (931941241/1000000000 : ℝ)) (y := (248298857/250000000 : ℝ)) (X := (16176510556101/100000000000000 : ℝ)) (Y := (523896922809/625000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248298857/250000000 : ℝ) ^ p + (931941241/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248298857/250000000 : ℝ)) (y := (931941241/1000000000 : ℝ)) (X := (523896922809/625000000000 : ℝ)) (Y := (16176510556101/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1925136669/1000000000 : ℝ)) (τ := (931941241/1000000000 : ℝ)) (σ := (248298857/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (798170814/841740541 : ℝ) ^ p + (15703488/15881897 : ℝ) ^ p := by
    exact cert_lt (x := (798170814/841740541 : ℝ)) (y := (15703488/15881897 : ℝ)) (X := (25320028338453/100000000000000 : ℝ)) (Y := (7467997253099/10000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (931941241/1000000000 : ℝ)) (n' := (841740541/1000000000 : ℝ)) (Ab := (399085407/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232985313/250000000 : ℝ) ^ p + (496597713/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232985313/250000000 : ℝ)) (y := (496597713/500000000 : ℝ)) (X := (8088257745309/50000000000000 : ℝ)) (Y := (83823503287129/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496597713/500000000 : ℝ) ^ p + (232985313/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496597713/500000000 : ℝ)) (y := (232985313/250000000 : ℝ)) (X := (83823503287129/100000000000000 : ℝ)) (Y := (8088257745309/50000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962568339/500000000 : ℝ)) (τ := (232985313/250000000 : ℝ)) (σ := (496597713/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (399085413/420870277 : ℝ) ^ p + (832284877/841740554 : ℝ) ^ p := by
    exact cert_lt (x := (399085413/420870277 : ℝ)) (y := (832284877/841740554 : ℝ)) (X := (12660014035143/50000000000000 : ℝ)) (Y := (14935994573927/20000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232985313/250000000 : ℝ)) (n' := (420870277/500000000 : ℝ)) (Ab := (399085413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962568339/500000000 : ℝ)) (τ := (232985313/250000000 : ℝ)) (σ := (496597713/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (232985313/250000000 : ℝ)) (n' := (420870277/500000000 : ℝ)) (Ab := (399085413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962568339/500000000 : ℝ)) (τ := (232985313/250000000 : ℝ)) (σ := (496597713/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (232985313/250000000 : ℝ)) (n' := (420870277/500000000 : ℝ)) (Ab := (399085413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962568339/500000000 : ℝ)) (τ := (232985313/250000000 : ℝ)) (σ := (496597713/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (232985313/250000000 : ℝ)) (n' := (420870277/500000000 : ℝ)) (Ab := (399085413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962568339/500000000 : ℝ)) (τ := (232985313/250000000 : ℝ)) (σ := (496597713/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (232985313/250000000 : ℝ)) (n' := (420870277/500000000 : ℝ)) (Ab := (399085413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962568339/500000000 : ℝ)) (τ := (232985313/250000000 : ℝ)) (σ := (496597713/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (833520928/902836173 : ℝ) ^ p + (1796216669/1805672346 : ℝ) ^ p := by
    exact cert_lt (x := (833520928/902836173 : ℝ)) (y := (1796216669/1805672346 : ℝ)) (X := (12688701641103/100000000000000 : ℝ)) (Y := (10913912340611/12500000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1119001339/1194327654 : ℝ) ^ p + (1184871977/1194327654 : ℝ) ^ p := by
    exact cert_lt (x := (1119001339/1194327654 : ℝ)) (y := (1184871977/1194327654 : ℝ)) (X := (3713948051871/20000000000000 : ℝ)) (Y := (81430260440317/100000000000000 : ℝ)) 827 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496597713/500000000 : ℝ)) (U := (597163827/500000000 : ℝ)) (Ab := (26047529/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (232985313/250000000 : ℝ)) (σ := (496597713/500000000 : ℝ)) (Ab := (1119001339/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab154
