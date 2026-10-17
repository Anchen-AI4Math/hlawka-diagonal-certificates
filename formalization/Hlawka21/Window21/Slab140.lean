import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 140, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab140 (p : ℝ) (hpa : (203/8 : ℝ) ≤ p) (hpb : p ≤ (813/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (129991930001/6927375000000 : ℝ) (9642307/1000000000 : ℝ) (1000000166257/5541900000000 : ℝ) (3033/2500 : ℝ) (486543131/250000000 : ℝ) (486526783/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194151489/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11177/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2337/5000 : ℝ)
      else (7823/10000 : ℝ) ≤ X j i ∧ X j i ≤ (593/500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (129991930001/6927375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9642307/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (925060261/1000000000 : ℝ) ^ p + (994162971/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925060261/1000000000 : ℝ)) (y := (994162971/1000000000 : ℝ)) (X := (1727496618297/12500000000000 : ℝ)) (Y := (10772505786551/12500000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994162971/1000000000 : ℝ) ^ p + (925060261/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994162971/1000000000 : ℝ)) (y := (925060261/1000000000 : ℝ)) (X := (10772505786551/12500000000000 : ℝ)) (Y := (1727496618297/12500000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (29987863/15625000 : ℝ)) (τ := (925060261/1000000000 : ℝ)) (σ := (994162971/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (197613165/208507481 : ℝ) ^ p + (824387617/834029924 : ℝ) ^ p := by
    exact cert_lt (x := (197613165/208507481 : ℝ)) (y := (824387617/834029924 : ℝ)) (X := (639481301339/2500000000000 : ℝ)) (Y := (1860518727161/2500000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (925060261/1000000000 : ℝ)) (n' := (208507481/250000000 : ℝ)) (Ab := (39522633/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (465228431/500000000 : ℝ) ^ p + (496575561/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465228431/500000000 : ℝ)) (y := (496575561/500000000 : ℝ)) (X := (16020974391261/100000000000000 : ℝ)) (Y := (41989521408159/50000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496575561/500000000 : ℝ) ^ p + (465228431/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496575561/500000000 : ℝ)) (y := (465228431/500000000 : ℝ)) (X := (41989521408159/50000000000000 : ℝ)) (Y := (16020974391261/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (120225499/62500000 : ℝ)) (τ := (465228431/500000000 : ℝ)) (σ := (496575561/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (113749901/120051792 : ℝ) ^ p + (830720237/840362544 : ℝ) ^ p := by
    exact cert_lt (x := (113749901/120051792 : ℝ)) (y := (830720237/840362544 : ℝ)) (X := (12706212152127/50000000000000 : ℝ)) (Y := (74587576732997/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (465228431/500000000 : ℝ)) (n' := (52522659/62500000 : ℝ)) (Ab := (796249307/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (930669939/1000000000 : ℝ) ^ p + (993107589/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (930669939/1000000000 : ℝ)) (y := (993107589/1000000000 : ℝ)) (X := (16114446911557/100000000000000 : ℝ)) (Y := (83885570617491/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993107589/1000000000 : ℝ) ^ p + (930669939/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993107589/1000000000 : ℝ)) (y := (930669939/1000000000 : ℝ)) (X := (83885570617491/100000000000000 : ℝ)) (Y := (16114446911557/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (240472191/125000000 : ℝ)) (τ := (930669939/1000000000 : ℝ)) (σ := (993107589/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (796477466/840611837 : ℝ) ^ p + (830969530/840611837 : ℝ) ^ p := by
    exact cert_lt (x := (796477466/840611837 : ℝ)) (y := (830969530/840611837 : ℝ)) (X := (25405901499047/100000000000000 : ℝ)) (Y := (74594100013523/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (930669939/1000000000 : ℝ)) (n' := (840611837/1000000000 : ℝ)) (Ab := (398238733/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (232669567/250000000 : ℝ) ^ p + (496552941/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232669567/250000000 : ℝ)) (y := (496552941/500000000 : ℝ)) (X := (8059055646089/50000000000000 : ℝ)) (Y := (41940953728521/50000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496552941/500000000 : ℝ) ^ p + (232669567/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496552941/500000000 : ℝ)) (y := (232669567/250000000 : ℝ)) (X := (41940953728521/50000000000000 : ℝ)) (Y := (8059055646089/50000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (38475683/20000000 : ℝ)) (τ := (232669567/250000000 : ℝ)) (σ := (496552941/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (796486384/840621581 : ℝ) ^ p + (830979274/840621581 : ℝ) ^ p := by
    exact cert_lt (x := (796486384/840621581 : ℝ)) (y := (830979274/840621581 : ℝ)) (X := (25405646700863/100000000000000 : ℝ)) (Y := (74594354918523/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (232669567/250000000 : ℝ)) (n' := (840621581/1000000000 : ℝ)) (Ab := (49780399/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465339297/500000000 : ℝ) ^ p + (198621163/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (465339297/500000000 : ℝ)) (y := (198621163/200000000 : ℝ)) (X := (16118254733607/100000000000000 : ℝ)) (Y := (5242610230037/6250000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198621163/200000000 : ℝ) ^ p + (465339297/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198621163/200000000 : ℝ)) (y := (465339297/500000000 : ℝ)) (X := (5242610230037/6250000000000 : ℝ)) (Y := (16118254733607/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1923784409/1000000000 : ℝ)) (τ := (465339297/500000000 : ℝ)) (σ := (198621163/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (398243366/420310981 : ℝ) ^ p + (830979655/840621962 : ℝ) ^ p := by
    exact cert_lt (x := (398243366/420310981 : ℝ)) (y := (830979655/840621962 : ℝ)) (X := (12702818084403/50000000000000 : ℝ)) (Y := (4662147805341/6250000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465339297/500000000 : ℝ)) (n' := (420310981/500000000 : ℝ)) (Ab := (199121683/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (930678607/1000000000 : ℝ) ^ p + (248276453/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (930678607/1000000000 : ℝ)) (y := (248276453/250000000 : ℝ)) (X := (16118260453689/100000000000000 : ℝ)) (Y := (83881757242847/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248276453/250000000 : ℝ) ^ p + (930678607/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248276453/250000000 : ℝ)) (y := (930678607/1000000000 : ℝ)) (X := (83881757242847/100000000000000 : ℝ)) (Y := (16118260453689/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1923784419/1000000000 : ℝ)) (τ := (930678607/1000000000 : ℝ)) (σ := (248276453/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (796486746/840621977 : ℝ) ^ p + (830979670/840621977 : ℝ) ^ p := by
    exact cert_lt (x := (796486746/840621977 : ℝ)) (y := (830979670/840621977 : ℝ)) (X := (25405635996637/100000000000000 : ℝ)) (Y := (14918873055571/20000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (930678607/1000000000 : ℝ)) (n' := (840621977/1000000000 : ℝ)) (Ab := (398243373/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (58167413/62500000 : ℝ) ^ p + (248276453/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (58167413/62500000 : ℝ)) (y := (248276453/250000000 : ℝ)) (X := (3223652178739/20000000000000 : ℝ)) (Y := (83881757242847/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248276453/250000000 : ℝ) ^ p + (58167413/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248276453/250000000 : ℝ)) (y := (58167413/62500000 : ℝ)) (X := (83881757242847/100000000000000 : ℝ)) (Y := (3223652178739/20000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (96189221/50000000 : ℝ)) (τ := (58167413/62500000 : ℝ)) (σ := (248276453/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (113783821/120088854 : ℝ) ^ p + (830979671/840621978 : ℝ) ^ p := by
    exact cert_lt (x := (113783821/120088854 : ℝ)) (y := (830979671/840621978 : ℝ)) (X := (1587852252449/6250000000000 : ℝ)) (Y := (14918873060803/20000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (58167413/62500000 : ℝ)) (n' := (420310989/500000000 : ℝ)) (Ab := (796486747/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (96189221/50000000 : ℝ)) (τ := (58167413/62500000 : ℝ)) (σ := (248276453/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (58167413/62500000 : ℝ)) (n' := (420310989/500000000 : ℝ)) (Ab := (796486747/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (96189221/50000000 : ℝ)) (τ := (58167413/62500000 : ℝ)) (σ := (248276453/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (58167413/62500000 : ℝ)) (n' := (420310989/500000000 : ℝ)) (Ab := (796486747/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (96189221/50000000 : ℝ)) (τ := (58167413/62500000 : ℝ)) (σ := (248276453/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (58167413/62500000 : ℝ)) (n' := (420310989/500000000 : ℝ)) (Ab := (796486747/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (96189221/50000000 : ℝ)) (τ := (58167413/62500000 : ℝ)) (σ := (248276453/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1665061094/1805848511 : ℝ) ^ p + (1796206204/1805848511 : ℝ) ^ p := by
    exact cert_lt (x := (1665061094/1805848511 : ℝ)) (y := (1796206204/1805848511 : ℝ)) (X := (6358734197831/50000000000000 : ℝ)) (Y := (87282531819553/100000000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1117688743/1194151489 : ℝ) ^ p + (1184509182/1194151489 : ℝ) ^ p := by
    exact cert_lt (x := (1117688743/1194151489 : ℝ)) (y := (1184509182/1194151489 : ℝ)) (X := (930746215077/5000000000000 : ℝ)) (Y := (651080609349/800000000000 : ℝ)) 813 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248276453/250000000 : ℝ)) (U := (1194151489/1000000000 : ℝ)) (Ab := (832530547/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (58167413/62500000 : ℝ)) (σ := (248276453/250000000 : ℝ)) (Ab := (1117688743/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab140
