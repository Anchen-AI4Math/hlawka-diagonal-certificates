import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 92, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab092 (p : ℝ) (hpa : (127/4 : ℝ) ≤ p) (hpb : p ≤ (509/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (355161327157/28130500000000 : ℝ) (6452077/1000000000 : ℝ) (800000168783/5626100000000 : ℝ) (591/500 : ℝ) (978447139/500000000 : ℝ) (978405173/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158791389/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5473/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1413/2500 : ℝ)
      else (831/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1439/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (355161327157/28130500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6452077/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (37832583/40000000 : ℝ) ^ p + (198832357/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (37832583/40000000 : ℝ)) (y := (198832357/200000000 : ℝ)) (X := (4248821185573/25000000000000 : ℝ)) (Y := (5187796128743/6250000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198832357/200000000 : ℝ) ^ p + (37832583/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (198832357/200000000 : ℝ)) (y := (37832583/40000000 : ℝ)) (X := (5187796128743/6250000000000 : ℝ)) (Y := (4248821185573/25000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (48499409/25000000 : ℝ)) (τ := (37832583/40000000 : ℝ)) (σ := (198832357/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (166099594/174441289 : ℝ) ^ p + (865754368/872206445 : ℝ) ^ p := by
    exact cert_lt (x := (166099594/174441289 : ℝ)) (y := (865754368/872206445 : ℝ)) (X := (21038133872807/100000000000000 : ℝ)) (Y := (19740466783597/25000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (37832583/40000000 : ℝ)) (n' := (174441289/200000000 : ℝ)) (Ab := (83049797/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (474436397/500000000 : ℝ) ^ p + (496731103/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (474436397/500000000 : ℝ)) (y := (496731103/500000000 : ℝ)) (X := (18833426143473/100000000000000 : ℝ)) (Y := (40583297042337/50000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496731103/500000000 : ℝ) ^ p + (474436397/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496731103/500000000 : ℝ)) (y := (474436397/500000000 : ℝ)) (X := (40583297042337/50000000000000 : ℝ)) (Y := (18833426143473/100000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (388467/200000 : ℝ)) (τ := (474436397/500000000 : ℝ)) (σ := (496731103/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (833711008/875678165 : ℝ) ^ p + (869226088/875678165 : ℝ) ^ p := by
    exact cert_lt (x := (833711008/875678165 : ℝ)) (y := (869226088/875678165 : ℝ)) (X := (5240970020343/25000000000000 : ℝ)) (Y := (79036120806079/100000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (474436397/500000000 : ℝ)) (n' := (175135633/200000000 : ℝ)) (Ab := (26053469/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (237237159/250000000 : ℝ) ^ p + (993443753/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (237237159/250000000 : ℝ)) (y := (993443753/1000000000 : ℝ)) (X := (9440686702097/50000000000000 : ℝ)) (Y := (81118646528097/100000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993443753/1000000000 : ℝ) ^ p + (237237159/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993443753/1000000000 : ℝ)) (y := (237237159/250000000 : ℝ)) (X := (81118646528097/100000000000000 : ℝ)) (Y := (9440686702097/50000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1942392389/1000000000 : ℝ)) (τ := (237237159/250000000 : ℝ)) (σ := (993443753/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (416895277/437882060 : ℝ) ^ p + (869312043/875764120 : ℝ) ^ p := by
    exact cert_lt (x := (416895277/437882060 : ℝ)) (y := (869312043/875764120 : ℝ)) (X := (2096204882743/10000000000000 : ℝ)) (Y := (79037952610389/100000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (237237159/250000000 : ℝ)) (n' := (21894103/25000000 : ℝ)) (Ab := (416895277/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (237237627/250000000 : ℝ) ^ p + (993443297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (237237627/250000000 : ℝ)) (y := (993443297/1000000000 : ℝ)) (X := (1180159898449/6250000000000 : ℝ)) (Y := (5069841376429/6250000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993443297/1000000000 : ℝ) ^ p + (237237627/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993443297/1000000000 : ℝ)) (y := (237237627/250000000 : ℝ)) (X := (5069841376429/6250000000000 : ℝ)) (Y := (1180159898449/6250000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (388478761/200000000 : ℝ)) (τ := (237237627/250000000 : ℝ)) (σ := (993443297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (833792517/875766242 : ℝ) ^ p + (869314165/875766242 : ℝ) ^ p := by
    exact cert_lt (x := (833792517/875766242 : ℝ)) (y := (869314165/875766242 : ℝ)) (X := (10481001501117/50000000000000 : ℝ)) (Y := (7903799782873/10000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (237237627/250000000 : ℝ)) (n' := (437883121/500000000 : ℝ)) (Ab := (833792517/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (948950553/1000000000 : ℝ) ^ p + (496721643/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (948950553/1000000000 : ℝ)) (y := (496721643/500000000 : ℝ)) (X := (377651737219/2000000000000 : ℝ)) (Y := (2027935836237/2500000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496721643/500000000 : ℝ) ^ p + (948950553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496721643/500000000 : ℝ)) (y := (948950553/1000000000 : ℝ)) (X := (2027935836237/2500000000000 : ℝ)) (Y := (377651737219/2000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1942393839/1000000000 : ℝ)) (τ := (948950553/1000000000 : ℝ)) (σ := (496721643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (833792565/875766293 : ℝ) ^ p + (869314216/875766293 : ℝ) ^ p := by
    exact cert_lt (x := (833792565/875766293 : ℝ)) (y := (869314216/875766293 : ℝ)) (X := (2620250319727/12500000000000 : ℝ)) (Y := (39518999457751/50000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (948950553/1000000000 : ℝ)) (n' := (875766293/1000000000 : ℝ)) (Ab := (166758513/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (474475277/500000000 : ℝ) ^ p + (496721643/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (474475277/500000000 : ℝ)) (y := (496721643/500000000 : ℝ)) (X := (1180161718373/6250000000000 : ℝ)) (Y := (2027935836237/2500000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496721643/500000000 : ℝ) ^ p + (474475277/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496721643/500000000 : ℝ)) (y := (474475277/500000000 : ℝ)) (X := (2027935836237/2500000000000 : ℝ)) (Y := (1180161718373/6250000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (24279923/12500000 : ℝ)) (τ := (474475277/500000000 : ℝ)) (σ := (496721643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (416896283/437883147 : ℝ) ^ p + (869314217/875766294 : ℝ) ^ p := by
    exact cert_lt (x := (416896283/437883147 : ℝ)) (y := (869314217/875766294 : ℝ)) (X := (5240500649037/25000000000000 : ℝ)) (Y := (79037998936811/100000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (474475277/500000000 : ℝ)) (n' := (437883147/500000000 : ℝ)) (Ab := (416896283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (24279923/12500000 : ℝ)) (τ := (474475277/500000000 : ℝ)) (σ := (496721643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (474475277/500000000 : ℝ)) (n' := (437883147/500000000 : ℝ)) (Ab := (416896283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (24279923/12500000 : ℝ)) (τ := (474475277/500000000 : ℝ)) (σ := (496721643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (474475277/500000000 : ℝ)) (n' := (437883147/500000000 : ℝ)) (Ab := (416896283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (24279923/12500000 : ℝ)) (τ := (474475277/500000000 : ℝ)) (σ := (496721643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (474475277/500000000 : ℝ)) (n' := (437883147/500000000 : ℝ)) (Ab := (416896283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (24279923/12500000 : ℝ)) (τ := (474475277/500000000 : ℝ)) (σ := (496721643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (474475277/500000000 : ℝ)) (n' := (437883147/500000000 : ℝ)) (Ab := (416896283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (24279923/12500000 : ℝ)) (τ := (474475277/500000000 : ℝ)) (σ := (496721643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1715619996/1841208611 : ℝ) ^ p + (1834756534/1841208611 : ℝ) ^ p := by
    exact cert_lt (x := (1715619996/1841208611 : ℝ)) (y := (1834756534/1841208611 : ℝ)) (X := (10566523471243/100000000000000 : ℝ)) (Y := (44716738429833/50000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (156358498/165541627 : ℝ) ^ p + (1152339312/1158791389 : ℝ) ^ p := by
    exact cert_lt (x := (156358498/165541627 : ℝ)) (y := (1152339312/1158791389 : ℝ)) (X := (1017147652667/6250000000000 : ℝ)) (Y := (1674512762179/2000000000000 : ℝ)) 509 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496721643/500000000 : ℝ)) (U := (1158791389/1000000000 : ℝ)) (Ab := (428904999/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (474475277/500000000 : ℝ)) (σ := (496721643/500000000 : ℝ)) (Ab := (547254743/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab092
