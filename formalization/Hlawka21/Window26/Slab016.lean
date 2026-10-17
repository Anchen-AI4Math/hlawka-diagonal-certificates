import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 16, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab016 (p : ℝ) (hpa : (27 : ℝ) ≤ p) (hpb : p ≤ (433/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (18106310009/1196100000000 : ℝ) (194143/25000000 : ℝ) (200000035883/1196100000000 : ℝ) (591/500 : ℝ) (487356199/250000000 : ℝ) (974654609/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289000747/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(541/500 : ℝ) ≤ X j i ∧ X j i ≤ -(5501/10000 : ℝ)
      else (2039/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5737/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (18106310009/1196100000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (194143/25000000 : ℝ) := by norm_num
  have pc0 : 1 < (935814081/1000000000 : ℝ) ^ p + (993311417/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (935814081/1000000000 : ℝ)) (y := (993311417/1000000000 : ℝ)) (X := (16608021212527/100000000000000 : ℝ)) (Y := (83391997055237/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993311417/1000000000 : ℝ) ^ p + (935814081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993311417/1000000000 : ℝ)) (y := (935814081/1000000000 : ℝ)) (X := (83391997055237/100000000000000 : ℝ)) (Y := (16608021212527/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (964562749/500000000 : ℝ)) (τ := (935814081/1000000000 : ℝ)) (σ := (993311417/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (816718297/864192769 : ℝ) ^ p + (856427049/864192769 : ℝ) ^ p := by
    exact cert_lt (x := (816718297/864192769 : ℝ)) (y := (856427049/864192769 : ℝ)) (X := (5418400526099/25000000000000 : ℝ)) (Y := (78326399118189/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (935814081/1000000000 : ℝ)) (n' := (864192769/1000000000 : ℝ)) (Ab := (816718297/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939251329/1000000000 : ℝ) ^ p + (992541207/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939251329/1000000000 : ℝ)) (y := (992541207/1000000000 : ℝ)) (X := (3668072845509/20000000000000 : ℝ)) (Y := (81659653609841/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992541207/1000000000 : ℝ) ^ p + (939251329/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992541207/1000000000 : ℝ)) (y := (939251329/1000000000 : ℝ)) (X := (81659653609841/100000000000000 : ℝ)) (Y := (3668072845509/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (241474067/125000000 : ℝ)) (τ := (939251329/1000000000 : ℝ)) (σ := (992541207/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (273446323/289384679 : ℝ) ^ p + (860388317/868154037 : ℝ) ^ p := by
    exact cert_lt (x := (273446323/289384679 : ℝ)) (y := (860388317/868154037 : ℝ)) (X := (10792926822551/50000000000000 : ℝ)) (Y := (3136565899337/4000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939251329/1000000000 : ℝ)) (n' := (868154037/1000000000 : ℝ)) (Ab := (820338969/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469678093/500000000 : ℝ) ^ p + (248129069/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (469678093/500000000 : ℝ)) (y := (248129069/250000000 : ℝ)) (X := (3679171067679/20000000000000 : ℝ)) (Y := (81604162367073/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248129069/250000000 : ℝ) ^ p + (469678093/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248129069/250000000 : ℝ)) (y := (469678093/500000000 : ℝ)) (X := (81604162367073/100000000000000 : ℝ)) (Y := (3679171067679/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (965936231/500000000 : ℝ)) (τ := (469678093/500000000 : ℝ)) (σ := (248129069/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (820449205/868274654 : ℝ) ^ p + (430254467/434137327 : ℝ) ^ p := by
    exact cert_lt (x := (820449205/868274654 : ℝ)) (y := (430254467/434137327 : ℝ)) (X := (5395798114833/25000000000000 : ℝ)) (Y := (15683361651569/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469678093/500000000 : ℝ)) (n' := (434137327/500000000 : ℝ)) (Ab := (164089841/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (187871873/200000000 : ℝ) ^ p + (992515519/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187871873/200000000 : ℝ)) (y := (992515519/1000000000 : ℝ)) (X := (919877010591/5000000000000 : ℝ)) (Y := (40801239005027/50000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992515519/1000000000 : ℝ) ^ p + (187871873/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992515519/1000000000 : ℝ)) (y := (187871873/200000000 : ℝ)) (X := (40801239005027/50000000000000 : ℝ)) (Y := (919877010591/5000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (482968721/250000000 : ℝ)) (τ := (187871873/200000000 : ℝ)) (σ := (992515519/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820452548/868278311 : ℝ) ^ p + (860512591/868278311 : ℝ) ^ p := by
    exact cert_lt (x := (820452548/868278311 : ℝ)) (y := (860512591/868278311 : ℝ)) (X := (21583112319753/100000000000000 : ℝ)) (Y := (78416888919967/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (187871873/200000000 : ℝ)) (n' := (868278311/1000000000 : ℝ)) (Ab := (205113137/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (469679731/500000000 : ℝ) ^ p + (124064437/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (469679731/500000000 : ℝ)) (y := (124064437/125000000 : ℝ)) (X := (18397591624261/100000000000000 : ℝ)) (Y := (16320485366921/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124064437/125000000 : ℝ) ^ p + (469679731/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124064437/125000000 : ℝ)) (y := (469679731/500000000 : ℝ)) (X := (16320485366921/20000000000000 : ℝ)) (Y := (18397591624261/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (965937479/500000000 : ℝ)) (τ := (469679731/500000000 : ℝ)) (σ := (124064437/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (820452649/868278422 : ℝ) ^ p + (430256351/434139211 : ℝ) ^ p := by
    exact cert_lt (x := (820452649/868278422 : ℝ)) (y := (430256351/434139211 : ℝ)) (X := (10791554776627/50000000000000 : ℝ)) (Y := (3136675654731/4000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (469679731/500000000 : ℝ)) (n' := (434139211/500000000 : ℝ)) (Ab := (820452649/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (187871893/200000000 : ℝ) ^ p + (198503099/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (187871893/200000000 : ℝ)) (y := (198503099/200000000 : ℝ)) (X := (18397593214339/100000000000000 : ℝ)) (Y := (81602424609587/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198503099/200000000 : ℝ) ^ p + (187871893/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198503099/200000000 : ℝ)) (y := (187871893/200000000 : ℝ)) (X := (81602424609587/100000000000000 : ℝ)) (Y := (18397593214339/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (820452653/868278426 : ℝ) ^ p + (430256353/434139213 : ℝ) ^ p := by
    exact cert_lt (x := (820452653/868278426 : ℝ)) (y := (430256353/434139213 : ℝ)) (X := (21583109710107/100000000000000 : ℝ)) (Y := (39208445728251/50000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (n' := (434139213/500000000 : ℝ)) (Ab := (820452653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (24148437/12500000 : ℝ)) (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (424593492/460999253 : ℝ) ^ p + (459057823/460999253 : ℝ) ^ p := by
    exact cert_lt (x := (424593492/460999253 : ℝ)) (y := (459057823/460999253 : ℝ)) (X := (10792972752569/100000000000000 : ℝ)) (Y := (17841405510937/20000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (270490719/289000747 : ℝ) ^ p + (287059317/289000747 : ℝ) ^ p := by
    exact cert_lt (x := (270490719/289000747 : ℝ)) (y := (287059317/289000747 : ℝ)) (X := (4168552038377/25000000000000 : ℝ)) (Y := (83325792661771/100000000000000 : ℝ)) 433 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198503099/200000000 : ℝ)) (U := (289000747/250000000 : ℝ)) (Ab := (106148373/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (187871893/200000000 : ℝ)) (σ := (198503099/200000000 : ℝ)) (Ab := (270490719/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab016
