import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 1, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab001 (p : ℝ) (hpa : (673/32 : ℝ) ≤ p) (hpb : p ≤ (337/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2130096904319/91864500000000 : ℝ) (149777/12500000 : ℝ) (4000000551187/18372900000000 : ℝ) (3033/2500 : ℝ) (967626547/500000000 : ℝ) (967579231/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298101893/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(441/400 : ℝ) ≤ X j i ∧ X j i ≤ -(4407/10000 : ℝ)
      else (189/250 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2130096904319/91864500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (149777/12500000 : ℝ) := by norm_num
  have pc0 : 1 < (908697599/1000000000 : ℝ) ^ p + (993241123/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (908697599/1000000000 : ℝ)) (y := (993241123/1000000000 : ℝ)) (X := (6655461982797/50000000000000 : ℝ)) (Y := (86689092404953/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993241123/1000000000 : ℝ) ^ p + (908697599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993241123/1000000000 : ℝ)) (y := (908697599/1000000000 : ℝ)) (X := (86689092404953/100000000000000 : ℝ)) (Y := (6655461982797/50000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (950969361/500000000 : ℝ)) (τ := (908697599/1000000000 : ℝ)) (σ := (993241123/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (768941351/818700596 : ℝ) ^ p + (201679609/204675149 : ℝ) ^ p := by
    exact cert_lt (x := (768941351/818700596 : ℝ)) (y := (201679609/204675149 : ℝ)) (X := (26694900927027/100000000000000 : ℝ)) (Y := (73305099853913/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (908697599/1000000000 : ℝ)) (n' := (204675149/250000000 : ℝ)) (Ab := (768941351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (914680237/1000000000 : ℝ) ^ p + (496078027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (914680237/1000000000 : ℝ)) (y := (496078027/500000000 : ℝ)) (X := (3820978092607/25000000000000 : ℝ)) (Y := (1694322063223/2000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496078027/500000000 : ℝ) ^ p + (914680237/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496078027/500000000 : ℝ)) (y := (914680237/1000000000 : ℝ)) (X := (1694322063223/2000000000000 : ℝ)) (Y := (3820978092607/25000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1906836291/1000000000 : ℝ)) (τ := (914680237/1000000000 : ℝ)) (σ := (496078027/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (775416162/825889025 : ℝ) ^ p + (162781373/165177805 : ℝ) ^ p := by
    exact cert_lt (x := (775416162/825889025 : ℝ)) (y := (162781373/165177805 : ℝ)) (X := (3311879794049/12500000000000 : ℝ)) (Y := (73504963052363/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (914680237/1000000000 : ℝ)) (n' := (33035561/40000000 : ℝ)) (Ab := (387708081/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (36599481/40000000 : ℝ) ^ p + (496047889/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (36599481/40000000 : ℝ)) (y := (496047889/500000000 : ℝ)) (X := (481007781727/3125000000000 : ℝ)) (Y := (84607766442261/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496047889/500000000 : ℝ) ^ p + (36599481/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496047889/500000000 : ℝ)) (y := (36599481/40000000 : ℝ)) (X := (84607766442261/100000000000000 : ℝ)) (Y := (481007781727/3125000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1907082803/1000000000 : ℝ)) (τ := (36599481/40000000 : ℝ)) (σ := (496047889/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (775747001/826256408 : ℝ) ^ p + (101784281/103282051 : ℝ) ^ p := by
    exact cert_lt (x := (775747001/826256408 : ℝ)) (y := (101784281/103282051 : ℝ)) (X := (1324245149189/5000000000000 : ℝ)) (Y := (73515097958189/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (36599481/40000000 : ℝ)) (n' := (103282051/125000000 : ℝ)) (Ab := (775747001/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (57187661/62500000 : ℝ) ^ p + (99209271/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (57187661/62500000 : ℝ)) (y := (99209271/100000000 : ℝ)) (X := (3079552000561/20000000000000 : ℝ)) (Y := (84602255721181/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99209271/100000000 : ℝ) ^ p + (57187661/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (99209271/100000000 : ℝ)) (y := (57187661/62500000 : ℝ)) (X := (84602255721181/100000000000000 : ℝ)) (Y := (3079552000561/20000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (953547643/500000000 : ℝ)) (τ := (57187661/62500000 : ℝ)) (σ := (99209271/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (775763768/826275027 : ℝ) ^ p + (814292867/826275027 : ℝ) ^ p := by
    exact cert_lt (x := (775763768/826275027 : ℝ)) (y := (814292867/826275027 : ℝ)) (X := (13242194849373/50000000000000 : ℝ)) (Y := (73515611391501/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (57187661/62500000 : ℝ)) (n' := (826275027/1000000000 : ℝ)) (Ab := (96970471/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (183000673/200000000 : ℝ) ^ p + (496046277/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (183000673/200000000 : ℝ)) (y := (496046277/500000000 : ℝ)) (X := (7699019829971/50000000000000 : ℝ)) (Y := (84601975524159/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496046277/500000000 : ℝ) ^ p + (183000673/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496046277/500000000 : ℝ)) (y := (183000673/200000000 : ℝ)) (X := (84601975524159/100000000000000 : ℝ)) (Y := (7699019829971/50000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1907095919/1000000000 : ℝ)) (τ := (183000673/200000000 : ℝ)) (σ := (496046277/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (775764619/826275972 : ℝ) ^ p + (203573453/206568993 : ℝ) ^ p := by
    exact cert_lt (x := (775764619/826275972 : ℝ)) (y := (203573453/206568993 : ℝ)) (X := (26484363646259/100000000000000 : ℝ)) (Y := (459472734063/625000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (183000673/200000000 : ℝ)) (n' := (206568993/250000000 : ℝ)) (Ab := (775764619/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (183000681/200000000 : ℝ) ^ p + (496046273/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (183000681/200000000 : ℝ)) (y := (496046273/500000000 : ℝ)) (X := (15398053837873/100000000000000 : ℝ)) (Y := (16920392231021/20000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496046273/500000000 : ℝ) ^ p + (183000681/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496046273/500000000 : ℝ)) (y := (183000681/200000000 : ℝ)) (X := (16920392231021/20000000000000 : ℝ)) (Y := (15398053837873/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1907095951/1000000000 : ℝ)) (τ := (183000681/200000000 : ℝ)) (σ := (496046273/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (387882331/413138010 : ℝ) ^ p + (40714693/41313801 : ℝ) ^ p := by
    exact cert_lt (x := (387882331/413138010 : ℝ)) (y := (40714693/41313801 : ℝ)) (X := (5296872432177/20000000000000 : ℝ)) (Y := (73515638773689/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (183000681/200000000 : ℝ)) (n' := (41313801/50000000 : ℝ)) (Ab := (387882331/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (915003407/1000000000 : ℝ) ^ p + (496046273/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915003407/1000000000 : ℝ)) (y := (496046273/500000000 : ℝ)) (X := (15398054546769/100000000000000 : ℝ)) (Y := (16920392231021/20000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496046273/500000000 : ℝ) ^ p + (915003407/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496046273/500000000 : ℝ)) (y := (915003407/1000000000 : ℝ)) (X := (16920392231021/20000000000000 : ℝ)) (Y := (15398054546769/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1907095953/1000000000 : ℝ)) (τ := (915003407/1000000000 : ℝ)) (σ := (496046273/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (387882332/413138011 : ℝ) ^ p + (407146931/413138011 : ℝ) ^ p := by
    exact cert_lt (x := (387882332/413138011 : ℝ)) (y := (407146931/413138011 : ℝ)) (X := (33105452811/125000000000 : ℝ)) (Y := (73515638828839/100000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (915003407/1000000000 : ℝ)) (n' := (413138011/500000000 : ℝ)) (Ab := (96970583/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1907095953/1000000000 : ℝ)) (τ := (915003407/1000000000 : ℝ)) (σ := (496046273/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (915003407/1000000000 : ℝ)) (n' := (413138011/500000000 : ℝ)) (Ab := (96970583/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1907095953/1000000000 : ℝ)) (τ := (915003407/1000000000 : ℝ)) (σ := (496046273/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (915003407/1000000000 : ℝ)) (n' := (413138011/500000000 : ℝ)) (Ab := (96970583/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1907095953/1000000000 : ℝ)) (τ := (915003407/1000000000 : ℝ)) (σ := (496046273/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (915003407/1000000000 : ℝ)) (n' := (413138011/500000000 : ℝ)) (Ab := (96970583/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1907095953/1000000000 : ℝ)) (τ := (915003407/1000000000 : ℝ)) (σ := (496046273/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (410284950/451898107 : ℝ) ^ p + (448902567/451898107 : ℝ) ^ p := by
    exact cert_lt (x := (410284950/451898107 : ℝ)) (y := (448902567/451898107 : ℝ)) (X := (1633932771353/12500000000000 : ℝ)) (Y := (8692853802579/10000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (275610981/298101893 : ℝ) ^ p + (295106353/298101893 : ℝ) ^ p := by
    exact cert_lt (x := (275610981/298101893 : ℝ)) (y := (295106353/298101893 : ℝ)) (X := (3832376562943/20000000000000 : ℝ)) (Y := (20209529393277/25000000000000 : ℝ)) 337 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496046273/500000000 : ℝ)) (U := (298101893/250000000 : ℝ)) (Ab := (8205699/5000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (915003407/1000000000 : ℝ)) (σ := (496046273/500000000 : ℝ)) (Ab := (275610981/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab001
