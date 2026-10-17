import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 68, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab068 (p : ℝ) (hpa : (121/4 : ℝ) ≤ p) (hpb : p ≤ (485/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (17856309161/1340075000000 : ℝ) (1363371/200000000 : ℝ) (800000160809/5360300000000 : ℝ) (591/500 : ℝ) (977392751/500000000 : ℝ) (488673287/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (57898341/50000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10909/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(561/1000 : ℝ)
      else (8267/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11501/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (17856309161/1340075000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1363371/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (188601933/200000000 : ℝ) ^ p + (198783401/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (188601933/200000000 : ℝ)) (y := (198783401/200000000 : ℝ)) (X := (8442879986527/50000000000000 : ℝ)) (Y := (20778565074001/25000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198783401/200000000 : ℝ) ^ p + (188601933/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198783401/200000000 : ℝ)) (y := (188601933/200000000 : ℝ)) (X := (20778565074001/25000000000000 : ℝ)) (Y := (8442879986527/50000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193692667/100000000 : ℝ)) (τ := (188601933/200000000 : ℝ)) (σ := (198783401/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (826614799/869995336 : ℝ) ^ p + (863178481/869995336 : ℝ) ^ p := by
    exact cert_lt (x := (826614799/869995336 : ℝ)) (y := (863178481/869995336 : ℝ)) (X := (21215133030007/100000000000000 : ℝ)) (Y := (78784868479747/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (188601933/200000000 : ℝ)) (n' := (108749417/125000000 : ℝ)) (Ab := (826614799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (946181513/1000000000 : ℝ) ^ p + (124149453/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (946181513/1000000000 : ℝ)) (y := (124149453/125000000 : ℝ)) (X := (18695012839481/100000000000000 : ℝ)) (Y := (81305007835567/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124149453/125000000 : ℝ) ^ p + (946181513/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124149453/125000000 : ℝ)) (y := (946181513/1000000000 : ℝ)) (X := (81305007835567/100000000000000 : ℝ)) (Y := (18695012839481/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1939377137/1000000000 : ℝ)) (τ := (946181513/1000000000 : ℝ)) (σ := (124149453/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (829949481/873611311 : ℝ) ^ p + (866794456/873611311 : ℝ) ^ p := by
    exact cert_lt (x := (829949481/873611311 : ℝ)) (y := (866794456/873611311 : ℝ)) (X := (21137030279577/100000000000000 : ℝ)) (Y := (3943148534023/5000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (946181513/1000000000 : ℝ)) (n' := (873611311/1000000000 : ℝ)) (Ab := (829949481/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (946265119/1000000000 : ℝ) ^ p + (248293853/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (946265119/1000000000 : ℝ)) (y := (248293853/250000000 : ℝ)) (X := (4686287884259/25000000000000 : ℝ)) (Y := (81254867871739/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248293853/250000000 : ℝ) ^ p + (946265119/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248293853/250000000 : ℝ)) (y := (946265119/1000000000 : ℝ)) (X := (81254867871739/100000000000000 : ℝ)) (Y := (4686287884259/25000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1939440531/1000000000 : ℝ)) (τ := (946265119/1000000000 : ℝ)) (σ := (248293853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (830037223/873706461 : ℝ) ^ p + (288963202/291235487 : ℝ) ^ p := by
    exact cert_lt (x := (830037223/873706461 : ℝ)) (y := (288963202/291235487 : ℝ)) (X := (10567491426191/50000000000000 : ℝ)) (Y := (78865018122029/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (946265119/1000000000 : ℝ)) (n' := (873706461/1000000000 : ℝ)) (Ab := (830037223/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (946267311/1000000000 : ℝ) ^ p + (993174881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946267311/1000000000 : ℝ)) (y := (993174881/1000000000 : ℝ)) (X := (18746467831863/100000000000000 : ℝ)) (Y := (40626775510877/50000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993174881/1000000000 : ℝ) ^ p + (946267311/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993174881/1000000000 : ℝ)) (y := (946267311/1000000000 : ℝ)) (X := (40626775510877/50000000000000 : ℝ)) (Y := (18746467831863/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (121215137/62500000 : ℝ)) (τ := (946267311/1000000000 : ℝ)) (σ := (993174881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (830039523/873708955 : ℝ) ^ p + (173378420/174741791 : ℝ) ^ p := by
    exact cert_lt (x := (830039523/873708955 : ℝ)) (y := (173378420/174741791 : ℝ)) (X := (21134929328797/100000000000000 : ℝ)) (Y := (19716267945679/25000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (946267311/1000000000 : ℝ)) (n' := (174741791/200000000 : ℝ)) (Ab := (830039523/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (946267369/1000000000 : ℝ) ^ p + (993174867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946267369/1000000000 : ℝ)) (y := (993174867/1000000000 : ℝ)) (X := (9373251331023/50000000000000 : ℝ)) (Y := (3250140652113/4000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993174867/1000000000 : ℝ) ^ p + (946267369/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993174867/1000000000 : ℝ)) (y := (946267369/1000000000 : ℝ)) (X := (3250140652113/4000000000000 : ℝ)) (Y := (9373251331023/50000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (484860559/250000000 : ℝ)) (τ := (946267369/1000000000 : ℝ)) (σ := (993174867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (830039584/873709021 : ℝ) ^ p + (866892166/873709021 : ℝ) ^ p := by
    exact cert_lt (x := (830039584/873709021 : ℝ)) (y := (866892166/873709021 : ℝ)) (X := (10567464007873/50000000000000 : ℝ)) (Y := (78865073202763/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (946267369/1000000000 : ℝ)) (n' := (873709021/1000000000 : ℝ)) (Ab := (25938737/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (94626737/100000000 : ℝ) ^ p + (993174867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94626737/100000000 : ℝ)) (y := (993174867/1000000000 : ℝ)) (X := (18746503262567/100000000000000 : ℝ)) (Y := (3250140652113/4000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993174867/1000000000 : ℝ) ^ p + (94626737/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993174867/1000000000 : ℝ)) (y := (94626737/100000000 : ℝ)) (X := (3250140652113/4000000000000 : ℝ)) (Y := (18746503262567/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1939442237/1000000000 : ℝ)) (τ := (94626737/100000000 : ℝ)) (σ := (993174867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (830039585/873709022 : ℝ) ^ p + (866892167/873709022 : ℝ) ^ p := by
    exact cert_lt (x := (830039585/873709022 : ℝ)) (y := (866892167/873709022 : ℝ)) (X := (21134928054323/100000000000000 : ℝ)) (Y := (78865073224279/100000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (94626737/100000000 : ℝ)) (n' := (436854511/500000000 : ℝ)) (Ab := (166007917/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1939442237/1000000000 : ℝ)) (τ := (94626737/100000000 : ℝ)) (σ := (993174867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (94626737/100000000 : ℝ)) (n' := (436854511/500000000 : ℝ)) (Ab := (166007917/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1939442237/1000000000 : ℝ)) (τ := (94626737/100000000 : ℝ)) (σ := (993174867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (94626737/100000000 : ℝ)) (n' := (436854511/500000000 : ℝ)) (Ab := (166007917/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1939442237/1000000000 : ℝ)) (τ := (94626737/100000000 : ℝ)) (σ := (993174867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (94626737/100000000 : ℝ)) (n' := (436854511/500000000 : ℝ)) (Ab := (166007917/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1939442237/1000000000 : ℝ)) (τ := (94626737/100000000 : ℝ)) (σ := (993174867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (94626737/100000000 : ℝ)) (n' := (436854511/500000000 : ℝ)) (Ab := (166007917/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1939442237/1000000000 : ℝ)) (τ := (94626737/100000000 : ℝ)) (σ := (993174867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (570245627/614011060 : ℝ) ^ p + (122347755/122802212 : ℝ) ^ p := by
    exact cert_lt (x := (570245627/614011060 : ℝ)) (y := (122347755/122802212 : ℝ)) (X := (10630100920407/100000000000000 : ℝ)) (Y := (17873979867311/20000000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (109089497/115796682 : ℝ) ^ p + (76743331/77197788 : ℝ) ^ p := by
    exact cert_lt (x := (109089497/115796682 : ℝ)) (y := (76743331/77197788 : ℝ)) (X := (16387278987329/100000000000000 : ℝ)) (Y := (10451590196121/12500000000000 : ℝ)) 485 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993174867/1000000000 : ℝ)) (U := (57898341/50000000 : ℝ)) (Ab := (1710736881/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (94626737/100000000 : ℝ)) (σ := (993174867/1000000000 : ℝ)) (Ab := (109089497/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab068
