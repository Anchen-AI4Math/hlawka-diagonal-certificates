import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 152, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab152 (p : ℝ) (hpa : (103/4 : ℝ) ≤ p) (hpb : p ≤ (825/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (129770167733/7029750000000 : ℝ) (9481903/1000000000 : ℝ) (500000084357/2811900000000 : ℝ) (3033/2500 : ℝ) (194694499/100000000 : ℝ) (243360183/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597151279/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11189/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1173/2500 : ℝ)
      else (7841/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5931/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (129770167733/7029750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9481903/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (463101411/500000000 : ℝ) ^ p + (19884629/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (463101411/500000000 : ℝ)) (y := (19884629/20000000 : ℝ)) (X := (1385612006091/10000000000000 : ℝ)) (Y := (17228779916669/20000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (19884629/20000000 : ℝ) ^ p + (463101411/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (19884629/20000000 : ℝ)) (y := (463101411/500000000 : ℝ)) (X := (17228779916669/20000000000000 : ℝ)) (Y := (1385612006091/10000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (60013571/31250000 : ℝ)) (τ := (463101411/500000000 : ℝ)) (σ := (19884629/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (395982187/417534848 : ℝ) ^ p + (825587793/835069696 : ℝ) ^ p := by
    exact cert_lt (x := (395982187/417534848 : ℝ)) (y := (825587793/835069696 : ℝ)) (X := (25502981309377/100000000000000 : ℝ)) (Y := (7449701988471/10000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (463101411/500000000 : ℝ)) (n' := (3261991/3906250 : ℝ)) (Ab := (395982187/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931548517/1000000000 : ℝ) ^ p + (24830671/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (931548517/1000000000 : ℝ)) (y := (24830671/25000000 : ℝ)) (X := (8036163319321/50000000000000 : ℝ)) (Y := (41963845404577/50000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (24830671/25000000 : ℝ) ^ p + (931548517/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24830671/25000000 : ℝ)) (y := (931548517/1000000000 : ℝ)) (X := (41963845404577/50000000000000 : ℝ)) (Y := (8036163319321/50000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1924775357/1000000000 : ℝ)) (τ := (931548517/1000000000 : ℝ)) (σ := (24830671/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (797703565/841332241 : ℝ) ^ p + (831850338/841332241 : ℝ) ^ p := by
    exact cert_lt (x := (797703565/841332241 : ℝ)) (y := (831850338/841332241 : ℝ)) (X := (12669306462567/50000000000000 : ℝ)) (Y := (74661388368267/100000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931548517/1000000000 : ℝ)) (n' := (841332241/1000000000 : ℝ)) (Ab := (159540713/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (465877729/500000000 : ℝ) ^ p + (15518507/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (465877729/500000000 : ℝ)) (y := (15518507/15625000 : ℝ)) (X := (4041157613843/25000000000000 : ℝ)) (Y := (41917693986441/50000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (15518507/15625000 : ℝ) ^ p + (465877729/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (15518507/15625000 : ℝ)) (y := (465877729/500000000 : ℝ)) (X := (41917693986441/50000000000000 : ℝ)) (Y := (4041157613843/25000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (962469953/500000000 : ℝ)) (τ := (465877729/500000000 : ℝ)) (σ := (15518507/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (159585011/168314793 : ℝ) ^ p + (832092062/841573965 : ℝ) ^ p := by
    exact cert_lt (x := (159585011/168314793 : ℝ)) (y := (832092062/841573965 : ℝ)) (X := (5066462113573/20000000000000 : ℝ)) (Y := (18666922653893/25000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (465877729/500000000 : ℝ)) (n' := (168314793/200000000 : ℝ)) (Ab := (159585011/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (931763391/1000000000 : ℝ) ^ p + (993182817/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931763391/1000000000 : ℝ)) (y := (993182817/1000000000 : ℝ)) (X := (16168179006573/100000000000000 : ℝ)) (Y := (8383183864139/10000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993182817/1000000000 : ℝ) ^ p + (931763391/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993182817/1000000000 : ℝ)) (y := (931763391/1000000000 : ℝ)) (X := (8383183864139/10000000000000 : ℝ)) (Y := (16168179006573/100000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (60154569/31250000 : ℝ)) (τ := (931763391/1000000000 : ℝ)) (σ := (993182817/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (398966772/420791615 : ℝ) ^ p + (832101327/841583230 : ℝ) ^ p := by
    exact cert_lt (x := (398966772/420791615 : ℝ)) (y := (832101327/841583230 : ℝ)) (X := (12666034368011/50000000000000 : ℝ)) (Y := (37333966055759/50000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (931763391/1000000000 : ℝ)) (n' := (84158323/100000000 : ℝ)) (Ab := (99741693/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (186352739/200000000 : ℝ) ^ p + (198636551/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (186352739/200000000 : ℝ)) (y := (198636551/200000000 : ℝ)) (X := (8084157502639/50000000000000 : ℝ)) (Y := (10478962965221/12500000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198636551/200000000 : ℝ) ^ p + (186352739/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198636551/200000000 : ℝ)) (y := (186352739/200000000 : ℝ)) (X := (10478962965221/12500000000000 : ℝ)) (Y := (8084157502639/50000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (38498929/20000000 : ℝ)) (τ := (186352739/200000000 : ℝ)) (σ := (198636551/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (159586774/168316717 : ℝ) ^ p + (832101682/841583585 : ℝ) ^ p := by
    exact cert_lt (x := (159586774/168316717 : ℝ)) (y := (832101682/841583585 : ℝ)) (X := (25332060070361/100000000000000 : ℝ)) (Y := (14933588272929/20000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (186352739/200000000 : ℝ)) (n' := (168316717/200000000 : ℝ)) (Ab := (79793387/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (931763707/1000000000 : ℝ) ^ p + (31036961/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (931763707/1000000000 : ℝ)) (y := (31036961/31250000 : ℝ)) (X := (16168320373671/100000000000000 : ℝ)) (Y := (20957924298351/25000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (31036961/31250000 : ℝ) ^ p + (931763707/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31036961/31250000 : ℝ)) (y := (931763707/1000000000 : ℝ)) (X := (20957924298351/25000000000000 : ℝ)) (Y := (16168320373671/100000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1924946459/1000000000 : ℝ)) (τ := (931763707/1000000000 : ℝ)) (σ := (31036961/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797933883/841583599 : ℝ) ^ p + (832101696/841583599 : ℝ) ^ p := by
    exact cert_lt (x := (797933883/841583599 : ℝ)) (y := (832101696/841583599 : ℝ)) (X := (25332059846201/100000000000000 : ℝ)) (Y := (74667941729557/100000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (931763707/1000000000 : ℝ)) (n' := (841583599/1000000000 : ℝ)) (Ab := (797933883/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1924946459/1000000000 : ℝ)) (τ := (931763707/1000000000 : ℝ)) (σ := (31036961/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (931763707/1000000000 : ℝ)) (n' := (841583599/1000000000 : ℝ)) (Ab := (797933883/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1924946459/1000000000 : ℝ)) (τ := (931763707/1000000000 : ℝ)) (σ := (31036961/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (931763707/1000000000 : ℝ)) (n' := (841583599/1000000000 : ℝ)) (Ab := (797933883/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1924946459/1000000000 : ℝ)) (τ := (931763707/1000000000 : ℝ)) (σ := (31036961/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (931763707/1000000000 : ℝ)) (n' := (841583599/1000000000 : ℝ)) (Ab := (797933883/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1924946459/1000000000 : ℝ)) (τ := (931763707/1000000000 : ℝ)) (σ := (31036961/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (931763707/1000000000 : ℝ)) (n' := (841583599/1000000000 : ℝ)) (Ab := (797933883/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1924946459/1000000000 : ℝ)) (τ := (931763707/1000000000 : ℝ)) (σ := (31036961/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1666762853/1805697442 : ℝ) ^ p + (1796215539/1805697442 : ℝ) ^ p := by
    exact cert_lt (x := (1666762853/1805697442 : ℝ)) (y := (1796215539/1805697442 : ℝ)) (X := (12692751380493/100000000000000 : ℝ)) (Y := (87307248922337/100000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1118815995/1194302558 : ℝ) ^ p + (1184820655/1194302558 : ℝ) ^ p := by
    exact cert_lt (x := (1118815995/1194302558 : ℝ)) (y := (1184820655/1194302558 : ℝ)) (X := (18576107456523/100000000000000 : ℝ)) (Y := (8142389337479/10000000000000 : ℝ)) 825 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (31036961/31250000 : ℝ)) (U := (597151279/500000000 : ℝ)) (Ab := (1666762853/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (931763707/1000000000 : ℝ)) (σ := (31036961/31250000 : ℝ)) (Ab := (223763199/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab152
