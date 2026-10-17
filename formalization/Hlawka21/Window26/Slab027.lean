import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 27, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab027 (p : ℝ) (hpa : (443/16 : ℝ) ≤ p) (hpb : p ≤ (111/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1443885700411/98124500000000 : ℝ) (7543933/1000000000 : ℝ) (3200000588747/19624900000000 : ℝ) (591/500 : ℝ) (9753311/5000000 : ℝ) (975276107/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (115643941/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(271/250 : ℝ) ≤ X j i ∧ X j i ≤ -(5527/10000 : ℝ)
      else (4091/5000 : ℝ) ≤ X j i ∧ X j i ≤ (287/250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1443885700411/98124500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7543933/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (937483347/1000000000 : ℝ) ^ p + (7761321/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (937483347/1000000000 : ℝ)) (y := (7761321/7812500 : ℝ)) (X := (4168010943813/25000000000000 : ℝ)) (Y := (10415996870937/12500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (7761321/7812500 : ℝ) ^ p + (937483347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7761321/7812500 : ℝ)) (y := (937483347/1000000000 : ℝ)) (X := (10415996870937/12500000000000 : ℝ)) (Y := (4168010943813/25000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (386186487/200000000 : ℝ)) (τ := (937483347/1000000000 : ℝ)) (σ := (7761321/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819006013/865555475 : ℝ) ^ p + (858011542/865555475 : ℝ) ^ p := by
    exact cert_lt (x := (819006013/865555475 : ℝ)) (y := (858011542/865555475 : ℝ)) (X := (21566668537009/100000000000000 : ℝ)) (Y := (78433332264619/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (937483347/1000000000 : ℝ)) (n' := (34622219/40000000 : ℝ)) (Ab := (819006013/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940862477/1000000000 : ℝ) ^ p + (198537857/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (940862477/1000000000 : ℝ)) (y := (198537857/200000000 : ℝ)) (X := (4605646819539/25000000000000 : ℝ)) (Y := (10197178841983/12500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198537857/200000000 : ℝ) ^ p + (940862477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198537857/200000000 : ℝ)) (y := (940862477/1000000000 : ℝ)) (X := (10197178841983/12500000000000 : ℝ)) (Y := (4605646819539/25000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (966775881/500000000 : ℝ)) (τ := (940862477/1000000000 : ℝ)) (σ := (198537857/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822563793/869439980 : ℝ) ^ p + (861896047/869439980 : ℝ) ^ p := by
    exact cert_lt (x := (822563793/869439980 : ℝ)) (y := (861896047/869439980 : ℝ)) (X := (21481124464409/100000000000000 : ℝ)) (Y := (78518876869033/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940862477/1000000000 : ℝ)) (n' := (43471999/50000000 : ℝ)) (Ab := (822563793/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (188192449/200000000 : ℝ) ^ p + (7755199/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (188192449/200000000 : ℝ)) (y := (7755199/7812500 : ℝ)) (X := (18476874147661/100000000000000 : ℝ)) (Y := (254759824717/312500000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (7755199/7812500 : ℝ) ^ p + (188192449/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (7755199/7812500 : ℝ)) (y := (188192449/200000000 : ℝ)) (X := (254759824717/312500000000 : ℝ)) (Y := (18476874147661/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1933627717/1000000000 : ℝ)) (τ := (188192449/200000000 : ℝ)) (σ := (7755199/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822668634/869554459 : ℝ) ^ p + (862010526/869554459 : ℝ) ^ p := by
    exact cert_lt (x := (822668634/869554459 : ℝ)) (y := (862010526/869554459 : ℝ)) (X := (5369653325339/25000000000000 : ℝ)) (Y := (9815173461241/12500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (188192449/200000000 : ℝ)) (n' := (869554459/1000000000 : ℝ)) (Ab := (411334317/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (940965173/1000000000 : ℝ) ^ p + (248166193/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (940965173/1000000000 : ℝ)) (y := (248166193/250000000 : ℝ)) (X := (18478469690383/100000000000000 : ℝ)) (Y := (81521548636733/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248166193/250000000 : ℝ) ^ p + (940965173/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248166193/250000000 : ℝ)) (y := (940965173/1000000000 : ℝ)) (X := (81521548636733/100000000000000 : ℝ)) (Y := (18478469690383/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (386725989/200000000 : ℝ)) (τ := (940965173/1000000000 : ℝ)) (σ := (248166193/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (411335855/434778909 : ℝ) ^ p + (862013885/869557818 : ℝ) ^ p := by
    exact cert_lt (x := (411335855/434778909 : ℝ)) (y := (862013885/869557818 : ℝ)) (X := (21478539485187/100000000000000 : ℝ)) (Y := (1963036533817/2500000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (940965173/1000000000 : ℝ)) (n' := (434778909/500000000 : ℝ)) (Ab := (82267171/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (47048263/50000000 : ℝ) ^ p + (992664751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (47048263/50000000 : ℝ)) (y := (992664751/1000000000 : ℝ)) (X := (18478517100959/100000000000000 : ℝ)) (Y := (81521500779017/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992664751/1000000000 : ℝ) ^ p + (47048263/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992664751/1000000000 : ℝ)) (y := (47048263/50000000 : ℝ)) (X := (81521500779017/100000000000000 : ℝ)) (Y := (18478517100959/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1933630011/1000000000 : ℝ)) (τ := (47048263/50000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (411335901/434778959 : ℝ) ^ p + (862013985/869557918 : ℝ) ^ p := by
    exact cert_lt (x := (411335901/434778959 : ℝ)) (y := (862013985/869557918 : ℝ)) (X := (21478537595641/100000000000000 : ℝ)) (Y := (78521463545669/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (47048263/50000000 : ℝ)) (n' := (434778959/500000000 : ℝ)) (Ab := (411335901/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470482631/500000000 : ℝ) ^ p + (992664751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470482631/500000000 : ℝ)) (y := (992664751/1000000000 : ℝ)) (X := (18478518190859/100000000000000 : ℝ)) (Y := (81521500779017/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992664751/1000000000 : ℝ) ^ p + (470482631/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992664751/1000000000 : ℝ)) (y := (470482631/500000000 : ℝ)) (X := (81521500779017/100000000000000 : ℝ)) (Y := (18478518190859/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (822671805/869557921 : ℝ) ^ p + (862013988/869557921 : ℝ) ^ p := by
    exact cert_lt (x := (822671805/869557921 : ℝ)) (y := (862013988/869557921 : ℝ)) (X := (5369634428209/25000000000000 : ℝ)) (Y := (78521463611459/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (n' := (869557921/1000000000 : ℝ)) (Ab := (164534361/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933630013/1000000000 : ℝ)) (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1701221293/1843560590 : ℝ) ^ p + (1836016657/1843560590 : ℝ) ^ p := by
    exact cert_lt (x := (1701221293/1843560590 : ℝ)) (y := (1836016657/1843560590 : ℝ)) (X := (10755217324443/100000000000000 : ℝ)) (Y := (89244783014169/100000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (541996164/578219705 : ℝ) ^ p + (1148895477/1156439410 : ℝ) ^ p := by
    exact cert_lt (x := (541996164/578219705 : ℝ)) (y := (1148895477/1156439410 : ℝ)) (X := (16607997438809/100000000000000 : ℝ)) (Y := (20848000766583/25000000000000 : ℝ)) 111 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992664751/1000000000 : ℝ)) (U := (115643941/100000000 : ℝ)) (Ab := (1701221293/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470482631/500000000 : ℝ)) (σ := (992664751/1000000000 : ℝ)) (Ab := (135499041/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab027
