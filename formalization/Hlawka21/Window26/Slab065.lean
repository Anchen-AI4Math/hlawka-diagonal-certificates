import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 65, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab065 (p : ℝ) (hpa : (481/16 : ℝ) ≤ p) (hpb : p ≤ (241/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1429541928337/106541500000000 : ℝ) (6865333/1000000000 : ℝ) (3200000639249/21308300000000 : ℝ) (591/500 : ℝ) (195450731/100000000 : ℝ) (977206907/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144732529/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2181/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(1121/2000 : ℝ)
      else (8261/10000 : ℝ) ≤ X j i ∧ X j i ≤ (23/20 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1429541928337/106541500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6865333/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (188527711/200000000 : ℝ) ^ p + (993884991/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188527711/200000000 : ℝ)) (y := (993884991/1000000000 : ℝ)) (X := (16871322135253/100000000000000 : ℝ)) (Y := (83128698900557/100000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993884991/1000000000 : ℝ) ^ p + (188527711/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993884991/1000000000 : ℝ)) (y := (188527711/200000000 : ℝ)) (X := (83128698900557/100000000000000 : ℝ)) (Y := (16871322135253/100000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (968261773/500000000 : ℝ)) (τ := (188527711/200000000 : ℝ)) (σ := (993884991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (165220424/173940129 : ℝ) ^ p + (862835312/869700645 : ℝ) ^ p := by
    exact cert_lt (x := (165220424/173940129 : ℝ)) (y := (862835312/869700645 : ℝ)) (X := (10619310830707/50000000000000 : ℝ)) (Y := (15752275959687/20000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (188527711/200000000 : ℝ)) (n' := (173940129/200000000 : ℝ)) (Ab := (20652553/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (945825021/1000000000 : ℝ) ^ p + (24829021/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (945825021/1000000000 : ℝ)) (y := (24829021/25000000 : ℝ)) (X := (747068290207/4000000000000 : ℝ)) (Y := (81323312910157/100000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (24829021/25000000 : ℝ) ^ p + (945825021/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24829021/25000000 : ℝ)) (y := (945825021/1000000000 : ℝ)) (X := (81323312910157/100000000000000 : ℝ)) (Y := (747068290207/4000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1938985861/1000000000 : ℝ)) (τ := (945825021/1000000000 : ℝ)) (σ := (24829021/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (414726241/436667659 : ℝ) ^ p + (866469985/873335318 : ℝ) ^ p := by
    exact cert_lt (x := (414726241/436667659 : ℝ)) (y := (866469985/873335318 : ℝ)) (X := (5290003319583/25000000000000 : ℝ)) (Y := (78839987995177/100000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (945825021/1000000000 : ℝ)) (n' := (436667659/500000000 : ℝ)) (Ab := (414726241/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (945909677/1000000000 : ℝ) ^ p + (124142549/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (945909677/1000000000 : ℝ)) (y := (124142549/125000000 : ℝ)) (X := (9363565812819/50000000000000 : ℝ)) (Y := (40636444114499/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124142549/125000000 : ℝ) ^ p + (945909677/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124142549/125000000 : ℝ)) (y := (945909677/1000000000 : ℝ)) (X := (40636444114499/50000000000000 : ℝ)) (Y := (9363565812819/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1939050069/1000000000 : ℝ)) (τ := (945909677/1000000000 : ℝ)) (σ := (124142549/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (829541333/873431716 : ℝ) ^ p + (866566383/873431716 : ℝ) ^ p := by
    exact cert_lt (x := (829541333/873431716 : ℝ)) (y := (866566383/873431716 : ℝ)) (X := (10578968060943/50000000000000 : ℝ)) (Y := (78842064946343/100000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (945909677/1000000000 : ℝ)) (n' := (218357929/250000000 : ℝ)) (Ab := (829541333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (472955957/500000000 : ℝ) ^ p + (993139851/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (472955957/500000000 : ℝ)) (y := (993139851/1000000000 : ℝ)) (X := (9364232926113/50000000000000 : ℝ)) (Y := (40635777267919/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993139851/1000000000 : ℝ) ^ p + (472955957/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993139851/1000000000 : ℝ)) (y := (472955957/500000000 : ℝ)) (X := (40635777267919/50000000000000 : ℝ)) (Y := (9364232926113/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (387810353/200000000 : ℝ)) (τ := (472955957/500000000 : ℝ)) (σ := (993139851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (829543681/873434263 : ℝ) ^ p + (866568930/873434263 : ℝ) ^ p := by
    exact cert_lt (x := (829543681/873434263 : ℝ)) (y := (866568930/873434263 : ℝ)) (X := (21157881559661/100000000000000 : ℝ)) (Y := (15768423963489/20000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (472955957/500000000 : ℝ)) (n' := (873434263/1000000000 : ℝ)) (Ab := (829543681/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (472955987/500000000 : ℝ) ^ p + (248284959/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (472955987/500000000 : ℝ)) (y := (248284959/250000000 : ℝ)) (X := (1170531352477/6250000000000 : ℝ)) (Y := (40635758778793/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248284959/250000000 : ℝ) ^ p + (472955987/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248284959/250000000 : ℝ)) (y := (472955987/500000000 : ℝ)) (X := (40635758778793/50000000000000 : ℝ)) (Y := (1170531352477/6250000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (193905181/100000000 : ℝ)) (τ := (472955987/500000000 : ℝ)) (σ := (248284959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (13167361/13864037 : ℝ) ^ p + (866568998/873434331 : ℝ) ^ p := by
    exact cert_lt (x := (13167361/13864037 : ℝ)) (y := (866568998/873434331 : ℝ)) (X := (8264796709/39062500000 : ℝ)) (Y := (39421060641197/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (472955987/500000000 : ℝ)) (n' := (873434331/1000000000 : ℝ)) (Ab := (829543743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (37836479/40000000 : ℝ) ^ p + (248284959/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (37836479/40000000 : ℝ)) (y := (248284959/250000000 : ℝ)) (X := (18728502236089/100000000000000 : ℝ)) (Y := (40635758778793/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248284959/250000000 : ℝ) ^ p + (37836479/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (248284959/250000000 : ℝ)) (y := (37836479/40000000 : ℝ)) (X := (40635758778793/50000000000000 : ℝ)) (Y := (18728502236089/100000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1939051811/1000000000 : ℝ)) (τ := (37836479/40000000 : ℝ)) (σ := (248284959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (207385936/218358583 : ℝ) ^ p + (866568999/873434332 : ℝ) ^ p := by
    exact cert_lt (x := (207385936/218358583 : ℝ)) (y := (866568999/873434332 : ℝ)) (X := (423157592273/2000000000000 : ℝ)) (Y := (39421060651969/50000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (37836479/40000000 : ℝ)) (n' := (218358583/250000000 : ℝ)) (Ab := (12961621/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1939051811/1000000000 : ℝ)) (τ := (37836479/40000000 : ℝ)) (σ := (248284959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (37836479/40000000 : ℝ)) (n' := (218358583/250000000 : ℝ)) (Ab := (12961621/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1939051811/1000000000 : ℝ)) (τ := (37836479/40000000 : ℝ)) (σ := (248284959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (37836479/40000000 : ℝ)) (n' := (218358583/250000000 : ℝ)) (Ab := (12961621/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1939051811/1000000000 : ℝ)) (τ := (37836479/40000000 : ℝ)) (σ := (248284959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (37836479/40000000 : ℝ)) (n' := (218358583/250000000 : ℝ)) (Ab := (12961621/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1939051811/1000000000 : ℝ)) (τ := (37836479/40000000 : ℝ)) (σ := (248284959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (37836479/40000000 : ℝ)) (n' := (218358583/250000000 : ℝ)) (Ab := (12961621/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1939051811/1000000000 : ℝ)) (τ := (37836479/40000000 : ℝ)) (σ := (248284959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (61074769/65790706 : ℝ) ^ p + (1835274435/1842139768 : ℝ) ^ p := by
    exact cert_lt (x := (61074769/65790706 : ℝ)) (y := (1835274435/1842139768 : ℝ)) (X := (10638508547679/100000000000000 : ℝ)) (Y := (11170186461021/12500000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1090422423/1157860232 : ℝ) ^ p + (1150994899/1157860232 : ℝ) ^ p := by
    exact cert_lt (x := (1090422423/1157860232 : ℝ)) (y := (1150994899/1157860232 : ℝ)) (X := (4100543369061/25000000000000 : ℝ)) (Y := (8359782713673/10000000000000 : ℝ)) 241 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248284959/250000000 : ℝ)) (U := (144732529/125000000 : ℝ)) (Ab := (427523383/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (37836479/40000000 : ℝ)) (σ := (248284959/250000000 : ℝ)) (Ab := (1090422423/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab065
