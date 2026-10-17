import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 134, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab134 (p : ℝ) (hpa : (403/16 : ℝ) ≤ p) (hpb : p ≤ (807/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (520421178191/27504750000000 : ℝ) (1944907/200000000 : ℝ) (2000000330057/11001900000000 : ℝ) (3033/2500 : ℝ) (972888897/500000000 : ℝ) (24321393/25000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194075709/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2793/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(933/2000 : ℝ)
      else (3907/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5929/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (520421178191/27504750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1944907/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (184895129/200000000 : ℝ) ^ p + (994128147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184895129/200000000 : ℝ)) (y := (994128147/1000000000 : ℝ)) (X := (13801506446123/100000000000000 : ℝ)) (Y := (17239702642647/20000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994128147/1000000000 : ℝ) ^ p + (184895129/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (994128147/1000000000 : ℝ)) (y := (184895129/200000000 : ℝ)) (X := (17239702642647/20000000000000 : ℝ)) (Y := (13801506446123/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (119912737/62500000 : ℝ)) (τ := (184895129/200000000 : ℝ)) (σ := (994128147/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (263226561/277832114 : ℝ) ^ p + (823771807/833496342 : ℝ) ^ p := by
    exact cert_lt (x := (263226561/277832114 : ℝ)) (y := (823771807/833496342 : ℝ)) (X := (12809181482727/50000000000000 : ℝ)) (Y := (14876327605493/20000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184895129/200000000 : ℝ)) (n' := (416748171/500000000 : ℝ)) (Ab := (789679683/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (464948907/500000000 : ℝ) ^ p + (9931127/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (464948907/500000000 : ℝ)) (y := (9931127/10000000 : ℝ)) (X := (15994691767227/100000000000000 : ℝ)) (Y := (84005326208873/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (9931127/10000000 : ℝ) ^ p + (464948907/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (9931127/10000000 : ℝ)) (y := (464948907/500000000 : ℝ)) (X := (84005326208873/100000000000000 : ℝ)) (Y := (15994691767227/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (961505257/500000000 : ℝ)) (τ := (464948907/500000000 : ℝ)) (σ := (9931127/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (795505247/839864337 : ℝ) ^ p + (830139802/839864337 : ℝ) ^ p := by
    exact cert_lt (x := (795505247/839864337 : ℝ)) (y := (830139802/839864337 : ℝ)) (X := (795321356907/3125000000000 : ℝ)) (Y := (18637429462131/25000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (464948907/500000000 : ℝ)) (n' := (839864337/1000000000 : ℝ)) (Ab := (795505247/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (186022811/200000000 : ℝ) ^ p + (993068581/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186022811/200000000 : ℝ)) (y := (993068581/1000000000 : ℝ)) (X := (8044378125391/50000000000000 : ℝ)) (Y := (83911262112347/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993068581/1000000000 : ℝ) ^ p + (186022811/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993068581/1000000000 : ℝ)) (y := (186022811/200000000 : ℝ)) (X := (83911262112347/100000000000000 : ℝ)) (Y := (8044378125391/50000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (480795659/250000000 : ℝ)) (τ := (186022811/200000000 : ℝ)) (σ := (993068581/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795736847/840117542 : ℝ) ^ p + (830393007/840117542 : ℝ) ^ p := by
    exact cert_lt (x := (795736847/840117542 : ℝ)) (y := (830393007/840117542 : ℝ)) (X := (5088728997257/20000000000000 : ℝ)) (Y := (74556355859393/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (186022811/200000000 : ℝ)) (n' := (420058771/500000000 : ℝ)) (Ab := (795736847/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (930122593/1000000000 : ℝ) ^ p + (993066833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (930122593/1000000000 : ℝ)) (y := (993066833/1000000000 : ℝ)) (X := (2011560143451/12500000000000 : ℝ)) (Y := (83907537365687/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993066833/1000000000 : ℝ) ^ p + (930122593/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993066833/1000000000 : ℝ)) (y := (930122593/1000000000 : ℝ)) (X := (83907537365687/100000000000000 : ℝ)) (Y := (2011560143451/12500000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (961594713/500000000 : ℝ)) (τ := (930122593/1000000000 : ℝ)) (σ := (993066833/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (397872995/420063769 : ℝ) ^ p + (17668149/17875054 : ℝ) ^ p := by
    exact cert_lt (x := (397872995/420063769 : ℝ)) (y := (17668149/17875054 : ℝ)) (X := (12721691483241/50000000000000 : ℝ)) (Y := (74556617843623/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (930122593/1000000000 : ℝ)) (n' := (420063769/500000000 : ℝ)) (Ab := (79574599/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (93012293/100000000 : ℝ) ^ p + (248266691/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (93012293/100000000 : ℝ)) (y := (248266691/250000000 : ℝ)) (X := (16092628188517/100000000000000 : ℝ)) (Y := (83907390339471/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248266691/250000000 : ℝ) ^ p + (93012293/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248266691/250000000 : ℝ)) (y := (93012293/100000000 : ℝ)) (X := (83907390339471/100000000000000 : ℝ)) (Y := (16092628188517/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961594847/500000000 : ℝ)) (τ := (93012293/100000000 : ℝ)) (σ := (248266691/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (795746352/840127933 : ℝ) ^ p + (830403398/840127933 : ℝ) ^ p := by
    exact cert_lt (x := (795746352/840127933 : ℝ)) (y := (830403398/840127933 : ℝ)) (X := (5088674636563/20000000000000 : ℝ)) (Y := (74556628196031/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (93012293/100000000 : ℝ)) (n' := (840127933/1000000000 : ℝ)) (Ab := (49734147/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (14533171/15625000 : ℝ) ^ p + (993066761/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14533171/15625000 : ℝ)) (y := (993066761/1000000000 : ℝ)) (X := (16092634297069/100000000000000 : ℝ)) (Y := (83907383947033/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993066761/1000000000 : ℝ) ^ p + (14533171/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (993066761/1000000000 : ℝ)) (y := (14533171/15625000 : ℝ)) (X := (83907383947033/100000000000000 : ℝ)) (Y := (16092634297069/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795746366/840127949 : ℝ) ^ p + (830403414/840127949 : ℝ) ^ p := by
    exact cert_lt (x := (795746366/840127949 : ℝ)) (y := (830403414/840127949 : ℝ)) (X := (2544337225167/10000000000000 : ℝ)) (Y := (74556628615369/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1664191994/1805924291 : ℝ) ^ p + (1796199756/1805924291 : ℝ) ^ p := by
    exact cert_lt (x := (1664191994/1805924291 : ℝ)) (y := (1796199756/1805924291 : ℝ)) (X := (3182529617131/25000000000000 : ℝ)) (Y := (8726988179951/10000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1117115264/1194075709 : ℝ) ^ p + (1184351174/1194075709 : ℝ) ^ p := by
    exact cert_lt (x := (1117115264/1194075709 : ℝ)) (y := (1184351174/1194075709 : ℝ)) (X := (18634758670113/100000000000000 : ℝ)) (Y := (16273048380961/20000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993066761/1000000000 : ℝ)) (U := (1194075709/1000000000 : ℝ)) (Ab := (832095997/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ)) (Ab := (8727463/7812500 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab134
