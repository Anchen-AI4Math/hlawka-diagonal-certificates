import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 59, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab059 (p : ℝ) (hpa : (731/32 : ℝ) ≤ p) (hpb : p ≤ (183/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (526710141599/24945375000000 : ℝ) (10882519/1000000000 : ℝ) (4000000598689/19956300000000 : ℝ) (3033/2500 : ℝ) (970152973/500000000 : ℝ) (485056379/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193123373/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5547/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4533/10000 : ℝ)
      else (7683/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (526710141599/24945375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10882519/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (916318439/1000000000 : ℝ) ^ p + (496828509/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (916318439/1000000000 : ℝ)) (y := (496828509/500000000 : ℝ)) (X := (6773014375233/50000000000000 : ℝ)) (Y := (5403374282471/6250000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496828509/500000000 : ℝ) ^ p + (916318439/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496828509/500000000 : ℝ)) (y := (916318439/1000000000 : ℝ)) (X := (5403374282471/6250000000000 : ℝ)) (Y := (6773014375233/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1909975457/1000000000 : ℝ)) (τ := (916318439/1000000000 : ℝ)) (σ := (496828509/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778929390/825941849 : ℝ) ^ p + (815059330/825941849 : ℝ) ^ p := by
    exact cert_lt (x := (778929390/825941849 : ℝ)) (y := (815059330/825941849 : ℝ)) (X := (26169755219857/100000000000000 : ℝ)) (Y := (73830246265591/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916318439/1000000000 : ℝ)) (n' := (825941849/1000000000 : ℝ)) (Ab := (77892939/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (922062413/1000000000 : ℝ) ^ p + (198519781/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (922062413/1000000000 : ℝ)) (y := (198519781/200000000 : ℝ)) (X := (15627600197779/100000000000000 : ℝ)) (Y := (42186208126091/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198519781/200000000 : ℝ) ^ p + (922062413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198519781/200000000 : ℝ)) (y := (922062413/1000000000 : ℝ)) (X := (42186208126091/50000000000000 : ℝ)) (Y := (15627600197779/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957330659/500000000 : ℝ)) (τ := (922062413/1000000000 : ℝ)) (σ := (198519781/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785123188/832767779 : ℝ) ^ p + (821885260/832767779 : ℝ) ^ p := by
    exact cert_lt (x := (785123188/832767779 : ℝ)) (y := (821885260/832767779 : ℝ)) (X := (12992351313613/50000000000000 : ℝ)) (Y := (74015298138651/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (922062413/1000000000 : ℝ)) (n' := (832767779/1000000000 : ℝ)) (Ab := (196280797/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922324381/1000000000 : ℝ) ^ p + (496273239/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922324381/1000000000 : ℝ)) (y := (496273239/500000000 : ℝ)) (X := (3145896157287/20000000000000 : ℝ)) (Y := (84270535548907/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496273239/500000000 : ℝ) ^ p + (922324381/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496273239/500000000 : ℝ)) (y := (922324381/1000000000 : ℝ)) (X := (84270535548907/100000000000000 : ℝ)) (Y := (3145896157287/20000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914870859/1000000000 : ℝ)) (τ := (922324381/1000000000 : ℝ)) (σ := (496273239/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (112200674/119011157 : ℝ) ^ p + (822195580/833078099 : ℝ) ^ p := by
    exact cert_lt (x := (112200674/119011157 : ℝ)) (y := (822195580/833078099 : ℝ)) (X := (1298817600111/5000000000000 : ℝ)) (Y := (14804729865543/20000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922324381/1000000000 : ℝ)) (n' := (833078099/1000000000 : ℝ)) (Ab := (392702359/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922336201/1000000000 : ℝ) ^ p + (992544103/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922336201/1000000000 : ℝ)) (y := (992544103/1000000000 : ℝ)) (X := (25174548133/160000000000 : ℝ)) (Y := (42132961514509/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992544103/1000000000 : ℝ) ^ p + (922336201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992544103/1000000000 : ℝ)) (y := (922336201/1000000000 : ℝ)) (X := (42132961514509/50000000000000 : ℝ)) (Y := (25174548133/160000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (119680019/62500000 : ℝ)) (τ := (922336201/1000000000 : ℝ)) (σ := (992544103/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (785417419/833092099 : ℝ) ^ p + (822209580/833092099 : ℝ) ^ p := by
    exact cert_lt (x := (785417419/833092099 : ℝ)) (y := (822209580/833092099 : ℝ)) (X := (811749230059/3125000000000 : ℝ)) (Y := (14804805192767/20000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922336201/1000000000 : ℝ)) (n' := (833092099/1000000000 : ℝ)) (Ab := (785417419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (461168367/500000000 : ℝ) ^ p + (248135999/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (461168367/500000000 : ℝ)) (y := (248135999/250000000 : ℝ)) (X := (15734300573627/100000000000000 : ℝ)) (Y := (42132857614271/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248135999/250000000 : ℝ) ^ p + (461168367/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248135999/250000000 : ℝ)) (y := (461168367/500000000 : ℝ)) (X := (42132857614271/50000000000000 : ℝ)) (Y := (15734300573627/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (191488073/100000000 : ℝ)) (τ := (461168367/500000000 : ℝ)) (σ := (248135999/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785417991/833092730 : ℝ) ^ p + (822210211/833092730 : ℝ) ^ p := by
    exact cert_lt (x := (785417991/833092730 : ℝ)) (y := (822210211/833092730 : ℝ)) (X := (25975958044473/100000000000000 : ℝ)) (Y := (18506010734777/25000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (461168367/500000000 : ℝ)) (n' := (83309273/100000000 : ℝ)) (Ab := (785417991/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (922336757/1000000000 : ℝ) ^ p + (124067999/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (922336757/1000000000 : ℝ)) (y := (124067999/125000000 : ℝ)) (X := (7867154774443/50000000000000 : ℝ)) (Y := (8426570746031/10000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124067999/125000000 : ℝ) ^ p + (922336757/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124067999/125000000 : ℝ)) (y := (922336757/1000000000 : ℝ)) (X := (8426570746031/10000000000000 : ℝ)) (Y := (7867154774443/50000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1914880749/1000000000 : ℝ)) (τ := (922336757/1000000000 : ℝ)) (σ := (124067999/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (785418017/833092758 : ℝ) ^ p + (822210239/833092758 : ℝ) ^ p := by
    exact cert_lt (x := (785418017/833092758 : ℝ)) (y := (822210239/833092758 : ℝ)) (X := (25975957743623/100000000000000 : ℝ)) (Y := (74024043692369/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (922336757/1000000000 : ℝ)) (n' := (416546379/500000000 : ℝ)) (Ab := (785418017/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (922336759/1000000000 : ℝ) ^ p + (992543991/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922336759/1000000000 : ℝ)) (y := (992543991/1000000000 : ℝ)) (X := (15365537431/97656250000 : ℝ)) (Y := (21066426379563/25000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992543991/1000000000 : ℝ) ^ p + (922336759/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992543991/1000000000 : ℝ)) (y := (922336759/1000000000 : ℝ)) (X := (21066426379563/25000000000000 : ℝ)) (Y := (15365537431/97656250000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (392709009/416546380 : ℝ) ^ p + (26522911/26873960 : ℝ) ^ p := by
    exact cert_lt (x := (392709009/416546380 : ℝ)) (y := (26522911/26873960 : ℝ)) (X := (25975957073671/100000000000000 : ℝ)) (Y := (74024043746173/100000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (n' := (20827319/25000000 : ℝ)) (Ab := (392709009/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (7659523/4000000 : ℝ)) (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (550726038/602292209 : ℝ) ^ p + (1795994108/1806876627 : ℝ) ^ p := by
    exact cert_lt (x := (550726038/602292209 : ℝ)) (y := (1795994108/1806876627 : ℝ)) (X := (12906584964481/100000000000000 : ℝ)) (Y := (21773353829949/25000000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (369779883/397707791 : ℝ) ^ p + (1182240854/1193123373 : ℝ) ^ p := by
    exact cert_lt (x := (369779883/397707791 : ℝ)) (y := (1182240854/1193123373 : ℝ)) (X := (18909227465057/100000000000000 : ℝ)) (Y := (5068173313111/6250000000000 : ℝ)) 183 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992543991/1000000000 : ℝ)) (U := (1193123373/1000000000 : ℝ)) (Ab := (826089057/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (922336759/1000000000 : ℝ)) (σ := (992543991/1000000000 : ℝ)) (Ab := (1109339649/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab059
