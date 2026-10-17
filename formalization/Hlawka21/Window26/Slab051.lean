import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 51, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab051 (p : ℝ) (hpa : (467/16 : ℝ) ≤ p) (hpb : p ≤ (117/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1434557056027/103440500000000 : ℝ) (7100859/1000000000 : ℝ) (3200000620643/20688100000000 : ℝ) (591/500 : ℝ) (488290619/250000000 : ℝ) (976531683/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578676089/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5441/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2789/5000 : ℝ)
      else (4117/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11493/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1434557056027/103440500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7100859/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (940840993/1000000000 : ℝ) ^ p + (15527049/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (940840993/1000000000 : ℝ)) (y := (15527049/15625000 : ℝ)) (X := (16801566478727/100000000000000 : ℝ)) (Y := (41599226662317/50000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (15527049/15625000 : ℝ) ^ p + (940840993/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (15527049/15625000 : ℝ)) (y := (940840993/1000000000 : ℝ)) (X := (41599226662317/50000000000000 : ℝ)) (Y := (16801566478727/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1934572129/1000000000 : ℝ)) (τ := (940840993/1000000000 : ℝ)) (σ := (15527049/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (823622389/868266170 : ℝ) ^ p + (861165311/868266170 : ℝ) ^ p := by
    exact cert_lt (x := (823622389/868266170 : ℝ)) (y := (861165311/868266170 : ℝ)) (X := (21352634382429/100000000000000 : ℝ)) (Y := (7864736689947/10000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (940840993/1000000000 : ℝ)) (n' := (86826617/100000000 : ℝ)) (Ab := (823622389/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (472048429/500000000 : ℝ) ^ p + (198598791/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (472048429/500000000 : ℝ)) (y := (198598791/200000000 : ℝ)) (X := (9294031895999/50000000000000 : ℝ)) (Y := (40705977756637/50000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198598791/200000000 : ℝ) ^ p + (472048429/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198598791/200000000 : ℝ)) (y := (472048429/500000000 : ℝ)) (X := (40705977756637/50000000000000 : ℝ)) (Y := (9294031895999/50000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1937090813/1000000000 : ℝ)) (τ := (472048429/500000000 : ℝ)) (σ := (198598791/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (827047293/871990081 : ℝ) ^ p + (864889222/871990081 : ℝ) ^ p := by
    exact cert_lt (x := (827047293/871990081 : ℝ)) (y := (864889222/871990081 : ℝ)) (X := (21271586939313/100000000000000 : ℝ)) (Y := (78728414133539/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (472048429/500000000 : ℝ)) (n' := (871990081/1000000000 : ℝ)) (Ab := (827047293/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37767467/40000000 : ℝ) ^ p + (19859447/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (37767467/40000000 : ℝ)) (y := (19859447/20000000 : ℝ)) (X := (18639858540529/100000000000000 : ℝ)) (Y := (8136016046289/10000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (19859447/20000000 : ℝ) ^ p + (37767467/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (19859447/20000000 : ℝ)) (y := (37767467/40000000 : ℝ)) (X := (8136016046289/10000000000000 : ℝ)) (Y := (18639858540529/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (77486361/40000000 : ℝ)) (τ := (37767467/40000000 : ℝ)) (σ := (19859447/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (827141600/872092629 : ℝ) ^ p + (288330590/290697543 : ℝ) ^ p := by
    exact cert_lt (x := (827141600/872092629 : ℝ)) (y := (288330590/290697543 : ℝ)) (X := (2658670471583/12500000000000 : ℝ)) (Y := (39365318666117/50000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37767467/40000000 : ℝ)) (n' := (872092629/1000000000 : ℝ)) (Ab := (1033927/1250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (944189139/1000000000 : ℝ) ^ p + (248242939/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (944189139/1000000000 : ℝ)) (y := (248242939/250000000 : ℝ)) (X := (9320640708713/50000000000000 : ℝ)) (Y := (1271230263723/1562500000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248242939/250000000 : ℝ) ^ p + (944189139/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248242939/250000000 : ℝ)) (y := (944189139/1000000000 : ℝ)) (X := (1271230263723/1562500000000 : ℝ)) (Y := (9320640708713/50000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (387432179/200000000 : ℝ)) (τ := (944189139/1000000000 : ℝ)) (σ := (248242939/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (827144187/872095442 : ℝ) ^ p + (864994583/872095442 : ℝ) ^ p := by
    exact cert_lt (x := (827144187/872095442 : ℝ)) (y := (864994583/872095442 : ℝ)) (X := (10634651422007/50000000000000 : ℝ)) (Y := (7873069831041/10000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (944189139/1000000000 : ℝ)) (n' := (436047721/500000000 : ℝ)) (Ab := (827144187/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (472094603/500000000 : ℝ) ^ p + (49648587/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (472094603/500000000 : ℝ)) (y := (49648587/50000000 : ℝ)) (X := (18641320109131/100000000000000 : ℝ)) (Y := (81358698532891/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (49648587/50000000 : ℝ) ^ p + (472094603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (49648587/50000000 : ℝ)) (y := (472094603/500000000 : ℝ)) (X := (81358698532891/100000000000000 : ℝ)) (Y := (18641320109131/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (968580473/500000000 : ℝ)) (τ := (472094603/500000000 : ℝ)) (σ := (49648587/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (827144257/872095518 : ℝ) ^ p + (288331553/290698506 : ℝ) ^ p := by
    exact cert_lt (x := (827144257/872095518 : ℝ)) (y := (288331553/290698506 : ℝ)) (X := (10634650638783/50000000000000 : ℝ)) (Y := (39365349978939/50000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (472094603/500000000 : ℝ)) (n' := (436047759/500000000 : ℝ)) (Ab := (827144257/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (118023651/125000000 : ℝ) ^ p + (49648587/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (118023651/125000000 : ℝ)) (y := (49648587/50000000 : ℝ)) (X := (18641321264109/100000000000000 : ℝ)) (Y := (81358698532891/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (49648587/50000000 : ℝ) ^ p + (118023651/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (49648587/50000000 : ℝ)) (y := (118023651/125000000 : ℝ)) (X := (81358698532891/100000000000000 : ℝ)) (Y := (18641321264109/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (484290237/250000000 : ℝ)) (τ := (118023651/125000000 : ℝ)) (σ := (49648587/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (827144260/872095521 : ℝ) ^ p + (288331554/290698507 : ℝ) ^ p := by
    exact cert_lt (x := (827144260/872095521 : ℝ)) (y := (288331554/290698507 : ℝ)) (X := (2126930139387/10000000000000 : ℝ)) (Y := (7873070002291/10000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (118023651/125000000 : ℝ)) (n' := (872095521/1000000000 : ℝ)) (Ab := (41357213/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (484290237/250000000 : ℝ)) (τ := (118023651/125000000 : ℝ)) (σ := (49648587/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (118023651/125000000 : ℝ)) (n' := (872095521/1000000000 : ℝ)) (Ab := (41357213/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (484290237/250000000 : ℝ)) (τ := (118023651/125000000 : ℝ)) (σ := (49648587/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (118023651/125000000 : ℝ)) (n' := (872095521/1000000000 : ℝ)) (Ab := (41357213/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (484290237/250000000 : ℝ)) (τ := (118023651/125000000 : ℝ)) (σ := (49648587/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (118023651/125000000 : ℝ)) (n' := (872095521/1000000000 : ℝ)) (Ab := (41357213/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (484290237/250000000 : ℝ)) (τ := (118023651/125000000 : ℝ)) (σ := (49648587/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (118023651/125000000 : ℝ)) (n' := (872095521/1000000000 : ℝ)) (Ab := (41357213/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (484290237/250000000 : ℝ)) (τ := (118023651/125000000 : ℝ)) (σ := (49648587/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1706986227/1842647822 : ℝ) ^ p + (1835546963/1842647822 : ℝ) ^ p := by
    exact cert_lt (x := (1706986227/1842647822 : ℝ)) (y := (1835546963/1842647822 : ℝ)) (X := (10679221769933/100000000000000 : ℝ)) (Y := (22330194610321/25000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1088152057/1157352178 : ℝ) ^ p + (1150251319/1157352178 : ℝ) ^ p := by
    exact cert_lt (x := (1088152057/1157352178 : ℝ)) (y := (1150251319/1157352178 : ℝ)) (X := (16474171481349/100000000000000 : ℝ)) (Y := (83525829086093/100000000000000 : ℝ)) 117 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (49648587/50000000 : ℝ)) (U := (578676089/500000000 : ℝ)) (Ab := (1706986227/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (118023651/125000000 : ℝ)) (σ := (49648587/50000000 : ℝ)) (Ab := (1088152057/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab051
