import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 81, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab081 (p : ℝ) (hpa : (497/16 : ℝ) ≤ p) (hpb : p ≤ (249/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1424153811481/110085500000000 : ℝ) (6614361/1000000000 : ℝ) (3200000660513/22017100000000 : ℝ) (591/500 : ℝ) (977976353/500000000 : ℝ) (977932531/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158419587/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10929/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5633/10000 : ℝ)
      else (8291/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11507/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1424153811481/110085500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6614361/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (944563967/1000000000 : ℝ) ^ p + (994052031/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944563967/1000000000 : ℝ)) (y := (994052031/1000000000 : ℝ)) (X := (16946363656571/100000000000000 : ℝ)) (Y := (83053658140119/100000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994052031/1000000000 : ℝ) ^ p + (944563967/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994052031/1000000000 : ℝ)) (y := (944563967/1000000000 : ℝ)) (X := (83053658140119/100000000000000 : ℝ)) (Y := (16946363656571/100000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (969307999/500000000 : ℝ)) (τ := (944563967/1000000000 : ℝ)) (σ := (994052031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (276254929/290408046 : ℝ) ^ p + (96067753/96802682 : ℝ) ^ p := by
    exact cert_lt (x := (276254929/290408046 : ℝ)) (y := (96067753/96802682 : ℝ)) (X := (2639616309909/12500000000000 : ℝ)) (Y := (78883070599057/100000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (944563967/1000000000 : ℝ)) (n' := (435612069/500000000 : ℝ)) (Ab := (828764787/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (236918383/250000000 : ℝ) ^ p + (993342541/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236918383/250000000 : ℝ)) (y := (993342541/1000000000 : ℝ)) (X := (1173231319759/6250000000000 : ℝ)) (Y := (20307079708817/25000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993342541/1000000000 : ℝ) ^ p + (236918383/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993342541/1000000000 : ℝ)) (y := (236918383/250000000 : ℝ)) (X := (20307079708817/25000000000000 : ℝ)) (Y := (1173231319759/6250000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1941016073/1000000000 : ℝ)) (τ := (236918383/250000000 : ℝ)) (σ := (993342541/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (832032743/874760810 : ℝ) ^ p + (868146449/874760810 : ℝ) ^ p := by
    exact cert_lt (x := (832032743/874760810 : ℝ)) (y := (868146449/874760810 : ℝ)) (X := (21040955989553/100000000000000 : ℝ)) (Y := (3158361810093/4000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (236918383/250000000 : ℝ)) (n' := (87476081/100000000 : ℝ)) (Ab := (832032743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (236938199/250000000 : ℝ) ^ p + (993323311/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236938199/250000000 : ℝ)) (y := (993323311/1000000000 : ℝ)) (X := (4705157842371/25000000000000 : ℝ)) (Y := (2029484734327/2500000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993323311/1000000000 : ℝ) ^ p + (236938199/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993323311/1000000000 : ℝ)) (y := (236938199/250000000 : ℝ)) (X := (2029484734327/2500000000000 : ℝ)) (Y := (4705157842371/25000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1941076107/1000000000 : ℝ)) (τ := (236938199/250000000 : ℝ)) (σ := (993323311/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (832115900/874850811 : ℝ) ^ p + (289412150/291616937 : ℝ) ^ p := by
    exact cert_lt (x := (832115900/874850811 : ℝ)) (y := (289412150/291616937 : ℝ)) (X := (21039029540561/100000000000000 : ℝ)) (Y := (39480485777689/50000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (236938199/250000000 : ℝ)) (n' := (874850811/1000000000 : ℝ)) (Ab := (8321159/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (947754807/1000000000 : ℝ) ^ p + (496661411/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (947754807/1000000000 : ℝ)) (y := (496661411/500000000 : ℝ)) (X := (18821874378919/100000000000000 : ℝ)) (Y := (20294536379237/25000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496661411/500000000 : ℝ) ^ p + (947754807/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496661411/500000000 : ℝ)) (y := (947754807/1000000000 : ℝ)) (X := (20294536379237/25000000000000 : ℝ)) (Y := (18821874378919/100000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1941077629/1000000000 : ℝ)) (τ := (947754807/1000000000 : ℝ)) (σ := (496661411/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (138686335/145808849 : ℝ) ^ p + (289412911/291617698 : ℝ) ^ p := by
    exact cert_lt (x := (138686335/145808849 : ℝ)) (y := (289412911/291617698 : ℝ)) (X := (21038981158993/100000000000000 : ℝ)) (Y := (987012755177/1250000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (947754807/1000000000 : ℝ)) (n' := (437426547/500000000 : ℝ)) (Ab := (83211801/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (947754857/1000000000 : ℝ) ^ p + (99332281/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (947754857/1000000000 : ℝ)) (y := (99332281/100000000 : ℝ)) (X := (4705476321297/25000000000000 : ℝ)) (Y := (81178114993103/100000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99332281/100000000 : ℝ) ^ p + (947754857/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99332281/100000000 : ℝ)) (y := (947754857/1000000000 : ℝ)) (X := (81178114993103/100000000000000 : ℝ)) (Y := (4705476321297/25000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1941077667/1000000000 : ℝ)) (τ := (947754857/1000000000 : ℝ)) (σ := (99332281/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (832118062/874853151 : ℝ) ^ p + (289412930/291617717 : ℝ) ^ p := by
    exact cert_lt (x := (832118062/874853151 : ℝ)) (y := (289412930/291617717 : ℝ)) (X := (10519489707691/50000000000000 : ℝ)) (Y := (78961021634021/100000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (947754857/1000000000 : ℝ)) (n' := (874853151/1000000000 : ℝ)) (Ab := (416059031/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (473877429/500000000 : ℝ) ^ p + (99332281/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (473877429/500000000 : ℝ)) (y := (99332281/100000000 : ℝ)) (X := (9410952951657/50000000000000 : ℝ)) (Y := (81178114993103/100000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99332281/100000000 : ℝ) ^ p + (473877429/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99332281/100000000 : ℝ)) (y := (473877429/500000000 : ℝ)) (X := (81178114993103/100000000000000 : ℝ)) (Y := (9410952951657/50000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (485269417/250000000 : ℝ)) (τ := (473877429/500000000 : ℝ)) (σ := (99332281/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (832118063/874853152 : ℝ) ^ p + (868238791/874853152 : ℝ) ^ p := by
    exact cert_lt (x := (832118063/874853152 : ℝ)) (y := (868238791/874853152 : ℝ)) (X := (21038979453823/100000000000000 : ℝ)) (Y := (39480510827711/50000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (473877429/500000000 : ℝ)) (n' := (27339161/31250000 : ℝ)) (Ab := (832118063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (485269417/250000000 : ℝ)) (τ := (473877429/500000000 : ℝ)) (σ := (99332281/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (473877429/500000000 : ℝ)) (n' := (27339161/31250000 : ℝ)) (Ab := (832118063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (485269417/250000000 : ℝ)) (τ := (473877429/500000000 : ℝ)) (σ := (99332281/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (473877429/500000000 : ℝ)) (n' := (27339161/31250000 : ℝ)) (Ab := (832118063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (485269417/250000000 : ℝ)) (τ := (473877429/500000000 : ℝ)) (σ := (99332281/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (473877429/500000000 : ℝ)) (n' := (27339161/31250000 : ℝ)) (Ab := (832118063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (485269417/250000000 : ℝ)) (τ := (473877429/500000000 : ℝ)) (σ := (99332281/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (473877429/500000000 : ℝ)) (n' := (27339161/31250000 : ℝ)) (Ab := (832118063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (485269417/250000000 : ℝ)) (τ := (473877429/500000000 : ℝ)) (σ := (99332281/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1713438277/1841580413 : ℝ) ^ p + (1834966052/1841580413 : ℝ) ^ p := by
    exact cert_lt (x := (1713438277/1841580413 : ℝ)) (y := (1834966052/1841580413 : ℝ)) (X := (10594874572559/100000000000000 : ℝ)) (Y := (22351281448857/25000000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1092888474/1158419587 : ℝ) ^ p + (88600402/89109199 : ℝ) ^ p := by
    exact cert_lt (x := (1092888474/1158419587 : ℝ)) (y := (88600402/89109199 : ℝ)) (X := (4081194712171/25000000000000 : ℝ)) (Y := (5229701376437/6250000000000 : ℝ)) 249 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99332281/100000000 : ℝ)) (U := (1158419587/1000000000 : ℝ)) (Ab := (1713438277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (473877429/500000000 : ℝ)) (σ := (99332281/100000000 : ℝ)) (Ab := (546444237/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab081
