import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 41, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab041 (p : ℝ) (hpa : (457/16 : ℝ) ≤ p) (hpb : p ≤ (229/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (359581387123/25306375000000 : ℝ) (7279083/1000000000 : ℝ) (3200000607353/20245100000000 : ℝ) (591/500 : ℝ) (976076077/500000000 : ℝ) (488012179/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289244589/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2173/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(5557/10000 : ℝ)
      else (8213/10000 : ℝ) ≤ X j i ∧ X j i ≤ (718/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (359581387123/25306375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7279083/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (23487167/25000000 : ℝ) ^ p + (993616539/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23487167/25000000 : ℝ)) (y := (993616539/1000000000 : ℝ)) (X := (16749205071343/100000000000000 : ℝ)) (Y := (41625407017053/50000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993616539/1000000000 : ℝ) ^ p + (23487167/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (993616539/1000000000 : ℝ)) (y := (23487167/25000000 : ℝ)) (X := (41625407017053/50000000000000 : ℝ)) (Y := (16749205071343/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1933103219/1000000000 : ℝ)) (τ := (23487167/25000000 : ℝ)) (σ := (993616539/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (34239915/36132404 : ℝ) ^ p + (40947553/41294176 : ℝ) ^ p := by
    exact cert_lt (x := (34239915/36132404 : ℝ)) (y := (40947553/41294176 : ℝ)) (X := (10719397189993/50000000000000 : ℝ)) (Y := (78561207015559/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (23487167/25000000 : ℝ)) (n' := (27099303/31250000 : ℝ)) (Ab := (20543949/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (942793273/1000000000 : ℝ) ^ p + (992869963/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942793273/1000000000 : ℝ)) (y := (992869963/1000000000 : ℝ)) (X := (1852130568283/10000000000000 : ℝ)) (Y := (81478712432783/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992869963/1000000000 : ℝ) ^ p + (942793273/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992869963/1000000000 : ℝ)) (y := (942793273/1000000000 : ℝ)) (X := (81478712432783/100000000000000 : ℝ)) (Y := (1852130568283/10000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (483915809/250000000 : ℝ)) (τ := (942793273/1000000000 : ℝ)) (σ := (992869963/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (68769789/72580613 : ℝ) ^ p + (41128013/41474636 : ℝ) ^ p := by
    exact cert_lt (x := (68769789/72580613 : ℝ)) (y := (41128013/41474636 : ℝ)) (X := (4271184563051/20000000000000 : ℝ)) (Y := (15728815596137/20000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (942793273/1000000000 : ℝ)) (n' := (217741839/250000000 : ℝ)) (Ab := (206309367/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (188577411/200000000 : ℝ) ^ p + (39713899/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (188577411/200000000 : ℝ)) (y := (39713899/40000000 : ℝ)) (X := (18574115775779/100000000000000 : ℝ)) (Y := (81425902908927/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39713899/40000000 : ℝ) ^ p + (188577411/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (39713899/40000000 : ℝ)) (y := (188577411/200000000 : ℝ)) (X := (81425902908927/100000000000000 : ℝ)) (Y := (18574115775779/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (193573453/100000000 : ℝ)) (τ := (188577411/200000000 : ℝ)) (σ := (39713899/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (825335971/871074647 : ℝ) ^ p + (863795564/871074647 : ℝ) ^ p := by
    exact cert_lt (x := (825335971/871074647 : ℝ)) (y := (863795564/871074647 : ℝ)) (X := (10676793149219/50000000000000 : ℝ)) (Y := (78646414908597/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (188577411/200000000 : ℝ)) (n' := (871074647/1000000000 : ℝ)) (Ab := (825335971/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (9428897/10000000 : ℝ) ^ p + (24821171/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (9428897/10000000 : ℝ)) (y := (24821171/25000000 : ℝ)) (X := (18575607321169/100000000000000 : ℝ)) (Y := (81424412191147/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (24821171/25000000 : ℝ) ^ p + (9428897/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (24821171/25000000 : ℝ)) (y := (9428897/10000000 : ℝ)) (X := (81424412191147/100000000000000 : ℝ)) (Y := (18575607321169/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (96786827/50000000 : ℝ)) (τ := (9428897/10000000 : ℝ)) (σ := (24821171/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (825338749/871077673 : ℝ) ^ p + (863798590/871077673 : ℝ) ^ p := by
    exact cert_lt (x := (825338749/871077673 : ℝ)) (y := (863798590/871077673 : ℝ)) (X := (667297509493/3125000000000 : ℝ)) (Y := (39323240405583/50000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (9428897/10000000 : ℝ)) (n' := (871077673/1000000000 : ℝ)) (Ab := (825338749/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (471444887/500000000 : ℝ) ^ p + (496423411/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (471444887/500000000 : ℝ)) (y := (496423411/500000000 : ℝ)) (X := (4643912263067/25000000000000 : ℝ)) (Y := (20356092483741/25000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496423411/500000000 : ℝ) ^ p + (471444887/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496423411/500000000 : ℝ)) (y := (471444887/500000000 : ℝ)) (X := (20356092483741/25000000000000 : ℝ)) (Y := (4643912263067/25000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (483934149/250000000 : ℝ)) (τ := (471444887/500000000 : ℝ)) (σ := (496423411/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (825338826/871077757 : ℝ) ^ p + (863798674/871077757 : ℝ) ^ p := by
    exact cert_lt (x := (825338826/871077757 : ℝ)) (y := (863798674/871077757 : ℝ)) (X := (21353518386151/100000000000000 : ℝ)) (Y := (78646482640577/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (471444887/500000000 : ℝ)) (n' := (871077757/1000000000 : ℝ)) (Ab := (412669413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (942889777/1000000000 : ℝ) ^ p + (992846821/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942889777/1000000000 : ℝ)) (y := (992846821/1000000000 : ℝ)) (X := (18575650744071/100000000000000 : ℝ)) (Y := (81424367587399/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992846821/1000000000 : ℝ) ^ p + (942889777/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992846821/1000000000 : ℝ)) (y := (942889777/1000000000 : ℝ)) (X := (81424367587399/100000000000000 : ℝ)) (Y := (18575650744071/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (967868299/500000000 : ℝ)) (τ := (942889777/1000000000 : ℝ)) (σ := (992846821/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (825338830/871077761 : ℝ) ^ p + (863798678/871077761 : ℝ) ^ p := by
    exact cert_lt (x := (825338830/871077761 : ℝ)) (y := (863798678/871077761 : ℝ)) (X := (10676759270851/50000000000000 : ℝ)) (Y := (19661620681923/25000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (942889777/1000000000 : ℝ)) (n' := (871077761/1000000000 : ℝ)) (Ab := (82533883/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (967868299/500000000 : ℝ)) (τ := (942889777/1000000000 : ℝ)) (σ := (992846821/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (942889777/1000000000 : ℝ)) (n' := (871077761/1000000000 : ℝ)) (Ab := (82533883/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (967868299/500000000 : ℝ)) (τ := (942889777/1000000000 : ℝ)) (σ := (992846821/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (942889777/1000000000 : ℝ)) (n' := (871077761/1000000000 : ℝ)) (Ab := (82533883/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (967868299/500000000 : ℝ)) (τ := (942889777/1000000000 : ℝ)) (σ := (992846821/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (942889777/1000000000 : ℝ)) (n' := (871077761/1000000000 : ℝ)) (Ab := (82533883/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (967868299/500000000 : ℝ)) (τ := (942889777/1000000000 : ℝ)) (σ := (992846821/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (942889777/1000000000 : ℝ)) (n' := (871077761/1000000000 : ℝ)) (Ab := (82533883/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (967868299/500000000 : ℝ)) (τ := (942889777/1000000000 : ℝ)) (σ := (992846821/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1704654817/1843021644 : ℝ) ^ p + (611914187/614340548 : ℝ) ^ p := by
    exact cert_lt (x := (1704654817/1843021644 : ℝ)) (y := (611914187/614340548 : ℝ)) (X := (2141976303947/20000000000000 : ℝ)) (Y := (89290118661213/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1086461609/1156978356 : ℝ) ^ p + (383233091/385659452 : ℝ) ^ p := by
    exact cert_lt (x := (1086461609/1156978356 : ℝ)) (y := (383233091/385659452 : ℝ)) (X := (8264126004213/50000000000000 : ℝ)) (Y := (83471748487799/100000000000000 : ℝ)) 229 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992846821/1000000000 : ℝ)) (U := (289244589/250000000 : ℝ)) (Ab := (1704654817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (942889777/1000000000 : ℝ)) (σ := (992846821/1000000000 : ℝ)) (Ab := (1086461609/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab041
