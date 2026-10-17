import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 44, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab044 (p : ℝ) (hpa : (115/4 : ℝ) ≤ p) (hpb : p ≤ (461/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1437178159/101890000000 : ℝ) (3612349/500000000 : ℝ) (160000030567/1018900000000 : ℝ) (591/500 : ℝ) (976229899/500000000 : ℝ) (244044711/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (46283659/40000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1087/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(5563/10000 : ℝ)
      else (8219/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11489/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1437178159/101890000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3612349/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (469949709/500000000 : ℝ) ^ p + (198730269/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (469949709/500000000 : ℝ)) (y := (198730269/200000000 : ℝ)) (X := (838257186083/5000000000000 : ℝ)) (Y := (16646975230409/20000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198730269/200000000 : ℝ) ^ p + (469949709/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198730269/200000000 : ℝ)) (y := (469949709/500000000 : ℝ)) (X := (16646975230409/20000000000000 : ℝ)) (Y := (838257186083/5000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1933550763/1000000000 : ℝ)) (τ := (469949709/500000000 : ℝ)) (σ := (198730269/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (205581454/216877529 : ℝ) ^ p + (430142709/433755058 : ℝ) ^ p := by
    exact cert_lt (x := (205581454/216877529 : ℝ)) (y := (430142709/433755058 : ℝ)) (X := (4282502912833/20000000000000 : ℝ)) (Y := (7858748633063/10000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (469949709/500000000 : ℝ)) (n' := (216877529/250000000 : ℝ)) (Ab := (102790727/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (471595347/500000000 : ℝ) ^ p + (496453797/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (471595347/500000000 : ℝ)) (y := (496453797/500000000 : ℝ)) (X := (1854164660617/10000000000000 : ℝ)) (Y := (10182296604003/12500000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496453797/500000000 : ℝ) ^ p + (471595347/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496453797/500000000 : ℝ)) (y := (471595347/500000000 : ℝ)) (X := (10182296604003/12500000000000 : ℝ)) (Y := (1854164660617/10000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (121006143/62500000 : ℝ)) (τ := (471595347/500000000 : ℝ)) (σ := (496453797/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (91754314/96808875 : ℝ) ^ p + (864055177/871279875 : ℝ) ^ p := by
    exact cert_lt (x := (91754314/96808875 : ℝ)) (y := (864055177/871279875 : ℝ)) (X := (2133019799511/10000000000000 : ℝ)) (Y := (39334901410199/50000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (471595347/500000000 : ℝ)) (n' := (6970239/8000000 : ℝ)) (Ab := (412894413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (943283263/1000000000 : ℝ) ^ p + (7943083/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (943283263/1000000000 : ℝ)) (y := (7943083/8000000 : ℝ)) (X := (18594150094319/100000000000000 : ℝ)) (Y := (40702934124857/50000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (7943083/8000000 : ℝ) ^ p + (943283263/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7943083/8000000 : ℝ)) (y := (943283263/1000000000 : ℝ)) (X := (40702934124857/50000000000000 : ℝ)) (Y := (18594150094319/100000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (968084319/500000000 : ℝ)) (τ := (943283263/1000000000 : ℝ)) (σ := (7943083/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (825886045/871385713 : ℝ) ^ p + (864161015/871385713 : ℝ) ^ p := by
    exact cert_lt (x := (825886045/871385713 : ℝ)) (y := (864161015/871385713 : ℝ)) (X := (21327896483653/100000000000000 : ℝ)) (Y := (9834013102039/12500000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (943283263/1000000000 : ℝ)) (n' := (871385713/1000000000 : ℝ)) (Ab := (165177209/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (943285851/1000000000 : ℝ) ^ p + (992884753/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943285851/1000000000 : ℝ)) (y := (992884753/1000000000 : ℝ)) (X := (18595620022067/100000000000000 : ℝ)) (Y := (20351099725871/25000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992884753/1000000000 : ℝ) ^ p + (943285851/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992884753/1000000000 : ℝ)) (y := (943285851/1000000000 : ℝ)) (X := (20351099725871/25000000000000 : ℝ)) (Y := (18595620022067/100000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (484042651/250000000 : ℝ)) (τ := (943285851/1000000000 : ℝ)) (σ := (992884753/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (3805939/4015616 : ℝ) ^ p + (432081987/435694336 : ℝ) ^ p := by
    exact cert_lt (x := (3805939/4015616 : ℝ)) (y := (432081987/435694336 : ℝ)) (X := (21327832126423/100000000000000 : ℝ)) (Y := (19668042292001/25000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (943285851/1000000000 : ℝ)) (n' := (1701931/1953125 : ℝ)) (Ab := (825888763/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (943285923/1000000000 : ℝ) ^ p + (1939228/1953125 : ℝ) ^ p := by
    exact cert_lt (x := (943285923/1000000000 : ℝ)) (y := (1939228/1953125 : ℝ)) (X := (3719132183621/20000000000000 : ℝ)) (Y := (81404358744863/100000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (1939228/1953125 : ℝ) ^ p + (943285923/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (1939228/1953125 : ℝ)) (y := (943285923/1000000000 : ℝ)) (X := (81404358744863/100000000000000 : ℝ)) (Y := (3719132183621/20000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1936170659/1000000000 : ℝ)) (τ := (943285923/1000000000 : ℝ)) (σ := (1939228/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (412944419/435694377 : ℝ) ^ p + (432082028/435694377 : ℝ) ^ p := by
    exact cert_lt (x := (412944419/435694377 : ℝ)) (y := (432082028/435694377 : ℝ)) (X := (10663915051913/50000000000000 : ℝ)) (Y := (19668042737829/25000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (943285923/1000000000 : ℝ)) (n' := (435694377/500000000 : ℝ)) (Ab := (412944419/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (37731437/40000000 : ℝ) ^ p + (198576947/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (37731437/40000000 : ℝ)) (y := (198576947/200000000 : ℝ)) (X := (4648915513527/25000000000000 : ℝ)) (Y := (635971534239/781250000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198576947/200000000 : ℝ) ^ p + (37731437/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (198576947/200000000 : ℝ)) (y := (37731437/40000000 : ℝ)) (X := (635971534239/781250000000 : ℝ)) (Y := (4648915513527/25000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (96808533/50000000 : ℝ)) (τ := (37731437/40000000 : ℝ)) (σ := (198576947/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (29496030/31121027 : ℝ) ^ p + (432082029/435694378 : ℝ) ^ p := by
    exact cert_lt (x := (29496030/31121027 : ℝ)) (y := (432082029/435694378 : ℝ)) (X := (2665978772691/12500000000000 : ℝ)) (Y := (19668042748703/25000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (37731437/40000000 : ℝ)) (n' := (217847189/250000000 : ℝ)) (Ab := (20647221/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (96808533/50000000 : ℝ)) (τ := (37731437/40000000 : ℝ)) (σ := (198576947/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (37731437/40000000 : ℝ)) (n' := (217847189/250000000 : ℝ)) (Ab := (20647221/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (96808533/50000000 : ℝ)) (τ := (37731437/40000000 : ℝ)) (σ := (198576947/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (37731437/40000000 : ℝ)) (n' := (217847189/250000000 : ℝ)) (Ab := (20647221/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (96808533/50000000 : ℝ)) (τ := (37731437/40000000 : ℝ)) (σ := (198576947/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (37731437/40000000 : ℝ)) (n' := (217847189/250000000 : ℝ)) (Ab := (20647221/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (96808533/50000000 : ℝ)) (τ := (37731437/40000000 : ℝ)) (σ := (198576947/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (37731437/40000000 : ℝ)) (n' := (217847189/250000000 : ℝ)) (Ab := (20647221/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (96808533/50000000 : ℝ)) (τ := (37731437/40000000 : ℝ)) (σ := (198576947/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (341072893/368581705 : ℝ) ^ p + (1835683827/1842908525 : ℝ) ^ p := by
    exact cert_lt (x := (341072893/368581705 : ℝ)) (y := (1835683827/1842908525 : ℝ)) (X := (10700540348393/100000000000000 : ℝ)) (Y := (89299459864911/100000000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (217394997/231418295 : ℝ) ^ p + (1149866777/1157091475 : ℝ) ^ p := by
    exact cert_lt (x := (217394997/231418295 : ℝ)) (y := (1149866777/1157091475 : ℝ)) (X := (16511787581561/100000000000000 : ℝ)) (Y := (5218013323859/6250000000000 : ℝ)) 461 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198576947/200000000 : ℝ)) (U := (46283659/40000000 : ℝ)) (Ab := (341072893/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (37731437/40000000 : ℝ)) (σ := (198576947/200000000 : ℝ)) (Ab := (217394997/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab044
