import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 7, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab007 (p : ℝ) (hpa : (423/16 : ℝ) ≤ p) (hpb : p ≤ (53/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1452461056963/93694500000000 : ℝ) (1591391/200000000 : ℝ) (3200000562167/18738900000000 : ℝ) (591/500 : ℝ) (974182621/500000000 : ℝ) (974122383/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (577818683/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10803/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5479/10000 : ℝ)
      else (8133/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11469/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1452461056963/93694500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1591391/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (467190383/500000000 : ℝ) ^ p + (993194539/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (467190383/500000000 : ℝ)) (y := (993194539/1000000000 : ℝ)) (X := (8276621402463/50000000000000 : ℝ)) (Y := (83446775257613/100000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993194539/1000000000 : ℝ) ^ p + (467190383/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993194539/1000000000 : ℝ)) (y := (467190383/500000000 : ℝ)) (X := (83446775257613/100000000000000 : ℝ)) (Y := (8276621402463/50000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (385515061/200000000 : ℝ)) (τ := (467190383/500000000 : ℝ)) (σ := (993194539/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (814757750/863014729 : ℝ) ^ p + (855057774/863014729 : ℝ) ^ p := by
    exact cert_lt (x := (814757750/863014729 : ℝ)) (y := (855057774/863014729 : ℝ)) (X := (5441426351827/25000000000000 : ℝ)) (Y := (78234295876779/100000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (467190383/500000000 : ℝ)) (n' := (863014729/1000000000 : ℝ)) (Ab := (3259031/4000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (937866201/1000000000 : ℝ) ^ p + (992415841/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937866201/1000000000 : ℝ)) (y := (992415841/1000000000 : ℝ)) (X := (570930800601/3125000000000 : ℝ)) (Y := (20432557875853/25000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992415841/1000000000 : ℝ) ^ p + (937866201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992415841/1000000000 : ℝ)) (y := (937866201/1000000000 : ℝ)) (X := (20432557875853/25000000000000 : ℝ)) (Y := (570930800601/3125000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (965141021/500000000 : ℝ)) (τ := (937866201/1000000000 : ℝ)) (σ := (992415841/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (818430705/867040216 : ℝ) ^ p + (859083261/867040216 : ℝ) ^ p := by
    exact cert_lt (x := (818430705/867040216 : ℝ)) (y := (859083261/867040216 : ℝ)) (X := (1083804192457/5000000000000 : ℝ)) (Y := (3916195876331/5000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (937866201/1000000000 : ℝ)) (n' := (108380027/125000000 : ℝ)) (Ab := (163686141/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (468987749/500000000 : ℝ) ^ p + (992389941/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468987749/500000000 : ℝ)) (y := (992389941/1000000000 : ℝ)) (X := (9163145650341/50000000000000 : ℝ)) (Y := (81673726074601/100000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992389941/1000000000 : ℝ) ^ p + (468987749/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992389941/1000000000 : ℝ)) (y := (468987749/500000000 : ℝ)) (X := (81673726074601/100000000000000 : ℝ)) (Y := (9163145650341/50000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1930365439/1000000000 : ℝ)) (τ := (468987749/500000000 : ℝ)) (σ := (992389941/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (90949517/96351801 : ℝ) ^ p + (859209254/867166209 : ℝ) ^ p := by
    exact cert_lt (x := (90949517/96351801 : ℝ)) (y := (859209254/867166209 : ℝ)) (X := (270916126329/1250000000000 : ℝ)) (Y := (19581677683921/25000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (468987749/500000000 : ℝ)) (n' := (867166209/1000000000 : ℝ)) (Ab := (818545653/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (187595781/200000000 : ℝ) ^ p + (248097283/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (187595781/200000000 : ℝ)) (y := (248097283/250000000 : ℝ)) (X := (572751731019/3125000000000 : ℝ)) (Y := (10208995212957/12500000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248097283/250000000 : ℝ) ^ p + (187595781/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248097283/250000000 : ℝ)) (y := (187595781/200000000 : ℝ)) (X := (10208995212957/12500000000000 : ℝ)) (Y := (572751731019/3125000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1930368037/1000000000 : ℝ)) (τ := (187595781/200000000 : ℝ)) (σ := (248097283/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (204637309/216792534 : ℝ) ^ p + (859213181/867170136 : ℝ) ^ p := by
    exact cert_lt (x := (204637309/216792534 : ℝ)) (y := (859213181/867170136 : ℝ)) (X := (10836601613669/50000000000000 : ℝ)) (Y := (78326797784033/100000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (187595781/200000000 : ℝ)) (n' := (108396267/125000000 : ℝ)) (Ab := (204637309/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (937979011/1000000000 : ℝ) ^ p + (992389107/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937979011/1000000000 : ℝ)) (y := (992389107/1000000000 : ℝ)) (X := (1832811028039/10000000000000 : ℝ)) (Y := (40835953590517/50000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992389107/1000000000 : ℝ) ^ p + (937979011/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992389107/1000000000 : ℝ)) (y := (937979011/1000000000 : ℝ)) (X := (40835953590517/50000000000000 : ℝ)) (Y := (1832811028039/10000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (965184059/500000000 : ℝ)) (τ := (937979011/1000000000 : ℝ)) (σ := (992389107/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (818549347/867170258 : ℝ) ^ p + (859213303/867170258 : ℝ) ^ p := by
    exact cert_lt (x := (818549347/867170258 : ℝ)) (y := (859213303/867170258 : ℝ)) (X := (10836600154349/50000000000000 : ℝ)) (Y := (1566536009767/2000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (937979011/1000000000 : ℝ)) (n' := (433585129/500000000 : ℝ)) (Ab := (818549347/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (468989507/500000000 : ℝ) ^ p + (496194553/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (468989507/500000000 : ℝ)) (y := (496194553/500000000 : ℝ)) (X := (916405591691/5000000000000 : ℝ)) (Y := (8167190500013/10000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496194553/500000000 : ℝ) ^ p + (468989507/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496194553/500000000 : ℝ)) (y := (468989507/500000000 : ℝ)) (X := (8167190500013/10000000000000 : ℝ)) (Y := (916405591691/5000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (48259203/25000000 : ℝ)) (τ := (468989507/500000000 : ℝ)) (σ := (496194553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (818549351/867170262 : ℝ) ^ p + (859213307/867170262 : ℝ) ^ p := by
    exact cert_lt (x := (818549351/867170262 : ℝ)) (y := (859213307/867170262 : ℝ)) (X := (21673200466061/100000000000000 : ℝ)) (Y := (9790850072127/12500000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (468989507/500000000 : ℝ)) (n' := (433585131/500000000 : ℝ)) (Ab := (818549351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (48259203/25000000 : ℝ)) (τ := (468989507/500000000 : ℝ)) (σ := (496194553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (468989507/500000000 : ℝ)) (n' := (433585131/500000000 : ℝ)) (Ab := (818549351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (48259203/25000000 : ℝ)) (τ := (468989507/500000000 : ℝ)) (σ := (496194553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (468989507/500000000 : ℝ)) (n' := (433585131/500000000 : ℝ)) (Ab := (818549351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (48259203/25000000 : ℝ)) (τ := (468989507/500000000 : ℝ)) (σ := (496194553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (468989507/500000000 : ℝ)) (n' := (433585131/500000000 : ℝ)) (Ab := (818549351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (48259203/25000000 : ℝ)) (τ := (468989507/500000000 : ℝ)) (σ := (496194553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (468989507/500000000 : ℝ)) (n' := (433585131/500000000 : ℝ)) (Ab := (818549351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (48259203/25000000 : ℝ)) (τ := (468989507/500000000 : ℝ)) (σ := (496194553/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1695938919/1844362634 : ℝ) ^ p + (1836405679/1844362634 : ℝ) ^ p := by
    exact cert_lt (x := (1695938919/1844362634 : ℝ)) (y := (1836405679/1844362634 : ℝ)) (X := (10825379445133/100000000000000 : ℝ)) (Y := (89174620764561/100000000000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (41547707/44447591 : ℝ) ^ p + (1147680411/1155637366 : ℝ) ^ p := by
    exact cert_lt (x := (41547707/44447591 : ℝ)) (y := (1147680411/1155637366 : ℝ)) (X := (3346178132367/20000000000000 : ℝ)) (Y := (325269960317/390625000000 : ℝ)) 53 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496194553/500000000 : ℝ)) (U := (577818683/500000000 : ℝ)) (Ab := (1695938919/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (468989507/500000000 : ℝ)) (σ := (496194553/500000000 : ℝ)) (Ab := (540120191/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab007
