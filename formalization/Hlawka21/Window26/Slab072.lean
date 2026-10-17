import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 72, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab072 (p : ℝ) (hpa : (61/2 : ℝ) ≤ p) (hpb : p ≤ (489/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (89196351589/6755750000000 : ℝ) (6753259/1000000000 : ℝ) (400000081069/2702300000000 : ℝ) (591/500 : ℝ) (244393897/125000000 : ℝ) (244382539/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144763463/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2729/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(5617/10000 : ℝ)
      else (331/400 : ℝ) ≤ X j i ∧ X j i ≤ (11503/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (89196351589/6755750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6753259/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (943497089/1000000000 : ℝ) ^ p + (496979593/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (943497089/1000000000 : ℝ)) (y := (496979593/500000000 : ℝ)) (X := (1690474034361/10000000000000 : ℝ)) (Y := (415476406749/500000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496979593/500000000 : ℝ) ^ p + (943497089/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496979593/500000000 : ℝ)) (y := (943497089/1000000000 : ℝ)) (X := (415476406749/500000000000 : ℝ)) (Y := (1690474034361/10000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (77498251/40000000 : ℝ)) (τ := (943497089/1000000000 : ℝ)) (σ := (496979593/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (206822137/217595407 : ℝ) ^ p + (863628369/870381628 : ℝ) ^ p := by
    exact cert_lt (x := (206822137/217595407 : ℝ)) (y := (863628369/870381628 : ℝ)) (X := (331004802473/1562500000000 : ℝ)) (Y := (39407846751731/50000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (943497089/1000000000 : ℝ)) (n' := (217595407/250000000 : ℝ)) (Ab := (206822137/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (94664959/100000000 : ℝ) ^ p + (496620741/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (94664959/100000000 : ℝ)) (y := (496620741/500000000 : ℝ)) (X := (9359528954213/50000000000000 : ℝ)) (Y := (81280961096633/100000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496620741/500000000 : ℝ) ^ p + (94664959/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496620741/500000000 : ℝ)) (y := (94664959/100000000 : ℝ)) (X := (81280961096633/100000000000000 : ℝ)) (Y := (9359528954213/50000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (15155399/7812500 : ℝ)) (τ := (94664959/100000000 : ℝ)) (σ := (496620741/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (415301245/436986453 : ℝ) ^ p + (867219647/873972906 : ℝ) ^ p := by
    exact cert_lt (x := (415301245/436986453 : ℝ)) (y := (867219647/873972906 : ℝ)) (X := (10553435745327/50000000000000 : ℝ)) (Y := (3944656497561/5000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (94664959/100000000 : ℝ)) (n' := (436986453/500000000 : ℝ)) (Ab := (83060249/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37869273/40000000 : ℝ) ^ p + (49661079/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (37869273/40000000 : ℝ)) (y := (49661079/50000000 : ℝ)) (X := (9384409967833/50000000000000 : ℝ)) (Y := (81231199883869/100000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (49661079/50000000 : ℝ) ^ p + (37869273/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (49661079/50000000 : ℝ)) (y := (37869273/40000000 : ℝ)) (X := (81231199883869/100000000000000 : ℝ)) (Y := (9384409967833/50000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (387990681/200000000 : ℝ)) (τ := (37869273/40000000 : ℝ)) (σ := (49661079/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (276896261/291355476 : ℝ) ^ p + (867313169/874066428 : ℝ) ^ p := by
    exact cert_lt (x := (276896261/291355476 : ℝ)) (y := (867313169/874066428 : ℝ)) (X := (4220972367419/20000000000000 : ℝ)) (Y := (1577902779683/2000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37869273/40000000 : ℝ)) (n' := (218516607/250000000 : ℝ)) (Ab := (830688783/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (473366979/500000000 : ℝ) ^ p + (993221063/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (473366979/500000000 : ℝ)) (y := (993221063/1000000000 : ℝ)) (X := (18770112357203/100000000000000 : ℝ)) (Y := (40614953807623/50000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993221063/1000000000 : ℝ) ^ p + (473366979/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993221063/1000000000 : ℝ)) (y := (473366979/500000000 : ℝ)) (X := (40614953807623/50000000000000 : ℝ)) (Y := (18770112357203/100000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1939955021/1000000000 : ℝ)) (τ := (473366979/500000000 : ℝ)) (σ := (993221063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (415345511/437034427 : ℝ) ^ p + (867315595/874068854 : ℝ) ^ p := by
    exact cert_lt (x := (415345511/437034427 : ℝ)) (y := (867315595/874068854 : ℝ)) (X := (10552405060177/50000000000000 : ℝ)) (Y := (39447595547123/50000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (473366979/500000000 : ℝ)) (n' := (437034427/500000000 : ℝ)) (Ab := (415345511/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (946734013/1000000000 : ℝ) ^ p + (19864421/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (946734013/1000000000 : ℝ)) (y := (19864421/20000000 : ℝ)) (X := (18770145683791/100000000000000 : ℝ)) (Y := (2030746878033/2500000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (19864421/20000000 : ℝ) ^ p + (946734013/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19864421/20000000 : ℝ)) (y := (946734013/1000000000 : ℝ)) (X := (2030746878033/2500000000000 : ℝ)) (Y := (18770145683791/100000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1939955063/1000000000 : ℝ)) (τ := (946734013/1000000000 : ℝ)) (σ := (19864421/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (830691080/874068917 : ℝ) ^ p + (867315658/874068917 : ℝ) ^ p := by
    exact cert_lt (x := (830691080/874068917 : ℝ)) (y := (867315658/874068917 : ℝ)) (X := (10552404332821/50000000000000 : ℝ)) (Y := (78895192447473/100000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (946734013/1000000000 : ℝ)) (n' := (874068917/1000000000 : ℝ)) (Ab := (20767277/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (189346803/200000000 : ℝ) ^ p + (993221049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (189346803/200000000 : ℝ)) (y := (993221049/1000000000 : ℝ)) (X := (4692536723917/25000000000000 : ℝ)) (Y := (20307468155447/25000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993221049/1000000000 : ℝ) ^ p + (189346803/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993221049/1000000000 : ℝ)) (y := (189346803/200000000 : ℝ)) (X := (20307468155447/25000000000000 : ℝ)) (Y := (4692536723917/25000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (242494383/125000000 : ℝ)) (τ := (189346803/200000000 : ℝ)) (σ := (993221049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (830691082/874068919 : ℝ) ^ p + (867315660/874068919 : ℝ) ^ p := by
    exact cert_lt (x := (830691082/874068919 : ℝ)) (y := (867315660/874068919 : ℝ)) (X := (21104808742711/100000000000000 : ℝ)) (Y := (1232737382663/1562500000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (189346803/200000000 : ℝ)) (n' := (874068919/1000000000 : ℝ)) (Ab := (415345541/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (242494383/125000000 : ℝ)) (τ := (189346803/200000000 : ℝ)) (σ := (993221049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (189346803/200000000 : ℝ)) (n' := (874068919/1000000000 : ℝ)) (Ab := (415345541/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (242494383/125000000 : ℝ)) (τ := (189346803/200000000 : ℝ)) (σ := (993221049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (189346803/200000000 : ℝ)) (n' := (874068919/1000000000 : ℝ)) (Ab := (415345541/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (242494383/125000000 : ℝ)) (τ := (189346803/200000000 : ℝ)) (σ := (993221049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (189346803/200000000 : ℝ)) (n' := (874068919/1000000000 : ℝ)) (Ab := (415345541/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (242494383/125000000 : ℝ)) (τ := (189346803/200000000 : ℝ)) (σ := (993221049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (189346803/200000000 : ℝ)) (n' := (874068919/1000000000 : ℝ)) (Ab := (415345541/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (242494383/125000000 : ℝ)) (τ := (189346803/200000000 : ℝ)) (σ := (993221049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1711582837/1841892296 : ℝ) ^ p + (1835139037/1841892296 : ℝ) ^ p := by
    exact cert_lt (x := (1711582837/1841892296 : ℝ)) (y := (1835139037/1841892296 : ℝ)) (X := (530952844483/5000000000000 : ℝ)) (Y := (11172617922991/12500000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1091517633/1158107704 : ℝ) ^ p + (1151354445/1158107704 : ℝ) ^ p := by
    exact cert_lt (x := (1091517633/1158107704 : ℝ)) (y := (1151354445/1158107704 : ℝ)) (X := (8183850337561/50000000000000 : ℝ)) (Y := (41816150035423/50000000000000 : ℝ)) 489 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993221049/1000000000 : ℝ)) (U := (144763463/125000000 : ℝ)) (Ab := (1711582837/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (189346803/200000000 : ℝ)) (σ := (993221049/1000000000 : ℝ)) (Ab := (1091517633/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab072
