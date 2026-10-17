import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 47, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab047 (p : ℝ) (hpa : (463/16 : ℝ) ≤ p) (hpb : p ≤ (29 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1436044908739/102554500000000 : ℝ) (1434221/200000000 : ℝ) (3200000615327/20510900000000 : ℝ) (591/500 : ℝ) (195276351/100000000 : ℝ) (976331351/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289300937/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(87/80 : ℝ) ≤ X j i ∧ X j i ≤ -(557/1000 : ℝ)
      else (329/400 : ℝ) ≤ X j i ∧ X j i ≤ (11491/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1436044908739/102554500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1434221/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (940306589/1000000000 : ℝ) ^ p + (993685781/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940306589/1000000000 : ℝ)) (y := (993685781/1000000000 : ℝ)) (X := (671235461619/4000000000000 : ℝ)) (Y := (41609566450331/50000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993685781/1000000000 : ℝ) ^ p + (940306589/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993685781/1000000000 : ℝ)) (y := (940306589/1000000000 : ℝ)) (X := (41609566450331/50000000000000 : ℝ)) (Y := (671235461619/4000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193399237/100000000 : ℝ)) (τ := (940306589/1000000000 : ℝ)) (σ := (993685781/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (411443151/433918729 : ℝ) ^ p + (860666353/867837458 : ℝ) ^ p := by
    exact cert_lt (x := (411443151/433918729 : ℝ)) (y := (860666353/867837458 : ℝ)) (X := (10693301452853/50000000000000 : ℝ)) (Y := (78613398598023/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (940306589/1000000000 : ℝ)) (n' := (433918729/500000000 : ℝ)) (Ab := (411443151/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (943582631/1000000000 : ℝ) ^ p + (19858897/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (943582631/1000000000 : ℝ)) (y := (19858897/20000000 : ℝ)) (X := (18561719365739/100000000000000 : ℝ)) (Y := (81438300439501/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (19858897/20000000 : ℝ) ^ p + (943582631/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19858897/20000000 : ℝ)) (y := (943582631/1000000000 : ℝ)) (X := (81438300439501/100000000000000 : ℝ)) (Y := (18561719365739/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1936527481/1000000000 : ℝ)) (τ := (943582631/1000000000 : ℝ)) (σ := (19858897/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (826332913/871587467 : ℝ) ^ p + (864416362/871587467 : ℝ) ^ p := by
    exact cert_lt (x := (826332913/871587467 : ℝ)) (y := (864416362/871587467 : ℝ)) (X := (10652417112051/50000000000000 : ℝ)) (Y := (78695166930201/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (943582631/1000000000 : ℝ)) (n' := (871587467/1000000000 : ℝ)) (Ab := (826332913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (471837003/500000000 : ℝ) ^ p + (992922897/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471837003/500000000 : ℝ)) (y := (992922897/1000000000 : ℝ)) (X := (18613917208563/100000000000000 : ℝ)) (Y := (81386101578103/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992922897/1000000000 : ℝ) ^ p + (471837003/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992922897/1000000000 : ℝ)) (y := (471837003/500000000 : ℝ)) (X := (81386101578103/100000000000000 : ℝ)) (Y := (18613917208563/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1936596903/1000000000 : ℝ)) (τ := (471837003/500000000 : ℝ)) (σ := (992922897/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (75129897/79244716 : ℝ) ^ p + (864520771/871691876 : ℝ) ^ p := by
    exact cert_lt (x := (75129897/79244716 : ℝ)) (y := (864520771/871691876 : ℝ)) (X := (4260513243039/20000000000000 : ℝ)) (Y := (9837179331739/12500000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (471837003/500000000 : ℝ)) (n' := (217922969/250000000 : ℝ)) (Ab := (826428867/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (47183827/50000000 : ℝ) ^ p + (992922287/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (47183827/50000000 : ℝ)) (y := (992922287/1000000000 : ℝ)) (X := (9307683385157/50000000000000 : ℝ)) (Y := (81384651608767/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992922287/1000000000 : ℝ) ^ p + (47183827/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992922287/1000000000 : ℝ)) (y := (47183827/50000000 : ℝ)) (X := (81384651608767/100000000000000 : ℝ)) (Y := (9307683385157/50000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1936598827/1000000000 : ℝ)) (τ := (47183827/50000000 : ℝ)) (σ := (992922287/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (826431529/871694772 : ℝ) ^ p + (864523667/871694772 : ℝ) ^ p := by
    exact cert_lt (x := (826431529/871694772 : ℝ)) (y := (864523667/871694772 : ℝ)) (X := (10651251852381/50000000000000 : ℝ)) (Y := (15739499509417/20000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (47183827/50000000 : ℝ)) (n' := (217923693/250000000 : ℝ)) (Ab := (826431529/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (943676609/1000000000 : ℝ) ^ p + (992922271/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943676609/1000000000 : ℝ)) (y := (992922271/1000000000 : ℝ)) (X := (3723081248587/20000000000000 : ℝ)) (Y := (508653834857/625000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992922271/1000000000 : ℝ) ^ p + (943676609/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992922271/1000000000 : ℝ)) (y := (943676609/1000000000 : ℝ)) (X := (508653834857/625000000000 : ℝ)) (Y := (3723081248587/20000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (12103743/6250000 : ℝ)) (τ := (943676609/1000000000 : ℝ)) (σ := (992922271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (826431601/871694850 : ℝ) ^ p + (4217189/4252170 : ℝ) ^ p := by
    exact cert_lt (x := (826431601/871694850 : ℝ)) (y := (4217189/4252170 : ℝ)) (X := (21302502247247/100000000000000 : ℝ)) (Y := (39348749620513/50000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (943676609/1000000000 : ℝ)) (n' := (17433897/20000000 : ℝ)) (Ab := (826431601/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (235919153/250000000 : ℝ) ^ p + (99292227/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (235919153/250000000 : ℝ)) (y := (99292227/100000000 : ℝ)) (X := (9307703979569/50000000000000 : ℝ)) (Y := (40692305600071/50000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99292227/100000000 : ℝ) ^ p + (235919153/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (99292227/100000000 : ℝ)) (y := (235919153/250000000 : ℝ)) (X := (40692305600071/50000000000000 : ℝ)) (Y := (9307703979569/50000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (968299441/500000000 : ℝ)) (τ := (235919153/250000000 : ℝ)) (σ := (99292227/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (413215802/435847427 : ℝ) ^ p + (864523749/871694854 : ℝ) ^ p := by
    exact cert_lt (x := (413215802/435847427 : ℝ)) (y := (864523749/871694854 : ℝ)) (X := (2130250165499/10000000000000 : ℝ)) (Y := (39348749663947/50000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (235919153/250000000 : ℝ)) (n' := (435847427/500000000 : ℝ)) (Ab := (206607901/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (968299441/500000000 : ℝ)) (τ := (235919153/250000000 : ℝ)) (σ := (99292227/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (235919153/250000000 : ℝ)) (n' := (435847427/500000000 : ℝ)) (Ab := (206607901/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (968299441/500000000 : ℝ)) (τ := (235919153/250000000 : ℝ)) (σ := (99292227/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (235919153/250000000 : ℝ)) (n' := (435847427/500000000 : ℝ)) (Ab := (206607901/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (968299441/500000000 : ℝ)) (τ := (235919153/250000000 : ℝ)) (σ := (99292227/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (235919153/250000000 : ℝ)) (n' := (435847427/500000000 : ℝ)) (Ab := (206607901/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (968299441/500000000 : ℝ)) (τ := (235919153/250000000 : ℝ)) (σ := (99292227/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (235919153/250000000 : ℝ)) (n' := (435847427/500000000 : ℝ)) (Ab := (206607901/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (968299441/500000000 : ℝ)) (τ := (235919153/250000000 : ℝ)) (σ := (99292227/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (426516317/460699063 : ℝ) ^ p + (1835625147/1842796252 : ℝ) ^ p := by
    exact cert_lt (x := (426516317/460699063 : ℝ)) (y := (1835625147/1842796252 : ℝ)) (X := (2672829956427/25000000000000 : ℝ)) (Y := (8930868041417/10000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (543741477/578601874 : ℝ) ^ p + (1150032643/1157203748 : ℝ) ^ p := by
    exact cert_lt (x := (543741477/578601874 : ℝ)) (y := (1150032643/1157203748 : ℝ)) (X := (8247763075877/50000000000000 : ℝ)) (Y := (83504474600111/100000000000000 : ℝ)) 29 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99292227/100000000 : ℝ)) (U := (289300937/250000000 : ℝ)) (Ab := (426516317/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (235919153/250000000 : ℝ)) (σ := (99292227/100000000 : ℝ)) (Ab := (543741477/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab047
