import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 32, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab032 (p : ℝ) (hpa : (22 : ℝ) ≤ p) (hpb : p ≤ (705/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (33081171311/1501500000000 : ℝ) (5684323/500000000 : ℝ) (62500009009/300300000000 : ℝ) (3033/2500 : ℝ) (48451389/25000000 : ℝ) (968984473/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (11927851/10000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11063/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4477/10000 : ℝ)
      else (7629/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11837/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (33081171311/1501500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5684323/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (912934831/1000000000 : ℝ) ^ p + (993469527/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (912934831/1000000000 : ℝ)) (y := (993469527/1000000000 : ℝ)) (X := (6720612260927/50000000000000 : ℝ)) (Y := (4327939616377/5000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993469527/1000000000 : ℝ) ^ p + (912934831/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993469527/1000000000 : ℝ)) (y := (912934831/1000000000 : ℝ)) (X := (4327939616377/5000000000000 : ℝ)) (Y := (6720612260927/50000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (953202179/500000000 : ℝ)) (τ := (912934831/1000000000 : ℝ)) (σ := (993469527/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (774488481/822748574 : ℝ) ^ p + (405689964/411374287 : ℝ) ^ p := by
    exact cert_lt (x := (774488481/822748574 : ℝ)) (y := (405689964/411374287 : ℝ)) (X := (26401692053993/100000000000000 : ℝ)) (Y := (18399577250913/25000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (912934831/1000000000 : ℝ)) (n' := (411374287/500000000 : ℝ)) (Ab := (774488481/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (918792421/1000000000 : ℝ) ^ p + (992397891/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918792421/1000000000 : ℝ)) (y := (992397891/1000000000 : ℝ)) (X := (3095019785773/20000000000000 : ℝ)) (Y := (42262458282303/50000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992397891/1000000000 : ℝ) ^ p + (918792421/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992397891/1000000000 : ℝ)) (y := (918792421/1000000000 : ℝ)) (X := (42262458282303/50000000000000 : ℝ)) (Y := (3095019785773/20000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (238898789/125000000 : ℝ)) (τ := (918792421/1000000000 : ℝ)) (σ := (992397891/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (780814869/829743688 : ℝ) ^ p + (409187521/414871844 : ℝ) ^ p := by
    exact cert_lt (x := (780814869/829743688 : ℝ)) (y := (409187521/414871844 : ℝ)) (X := (6552480320571/25000000000000 : ℝ)) (Y := (73790079522157/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (918792421/1000000000 : ℝ)) (n' := (103717961/125000000 : ℝ)) (Ab := (780814869/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (91907409/100000000 : ℝ) ^ p + (496170989/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (91907409/100000000 : ℝ)) (y := (496170989/500000000 : ℝ)) (X := (15579955311553/100000000000000 : ℝ)) (Y := (1688401209931/2000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496170989/500000000 : ℝ) ^ p + (91907409/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496170989/500000000 : ℝ)) (y := (91907409/100000000 : ℝ)) (X := (1688401209931/2000000000000 : ℝ)) (Y := (15579955311553/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (477854017/250000000 : ℝ)) (τ := (91907409/100000000 : ℝ)) (σ := (496170989/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (781118026/830078957 : ℝ) ^ p + (818710311/830078957 : ℝ) ^ p := by
    exact cert_lt (x := (781118026/830078957 : ℝ)) (y := (818710311/830078957 : ℝ)) (X := (13100399718539/50000000000000 : ℝ)) (Y := (18449800396479/25000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (91907409/100000000 : ℝ)) (n' := (830078957/1000000000 : ℝ)) (Ab := (390559013/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (183817497/200000000 : ℝ) ^ p + (248084827/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (183817497/200000000 : ℝ)) (y := (248084827/250000000 : ℝ)) (X := (15584958698629/100000000000000 : ℝ)) (Y := (10551882054713/12500000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248084827/250000000 : ℝ) ^ p + (183817497/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248084827/250000000 : ℝ)) (y := (183817497/200000000 : ℝ)) (X := (10551882054713/12500000000000 : ℝ)) (Y := (15584958698629/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1911426793/1000000000 : ℝ)) (τ := (183817497/200000000 : ℝ)) (σ := (248084827/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (781132441/830094899 : ℝ) ^ p + (818726253/830094899 : ℝ) ^ p := by
    exact cert_lt (x := (781132441/830094899 : ℝ)) (y := (818726253/830094899 : ℝ)) (X := (3275045736943/12500000000000 : ℝ)) (Y := (73799635182211/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (183817497/200000000 : ℝ)) (n' := (830094899/1000000000 : ℝ)) (Ab := (781132441/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (459544061/500000000 : ℝ) ^ p + (992339181/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459544061/500000000 : ℝ)) (y := (992339181/1000000000 : ℝ)) (X := (15585196673193/100000000000000 : ℝ)) (Y := (42207409211991/50000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992339181/1000000000 : ℝ) ^ p + (459544061/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992339181/1000000000 : ℝ)) (y := (459544061/500000000 : ℝ)) (X := (42207409211991/50000000000000 : ℝ)) (Y := (15585196673193/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1911427303/1000000000 : ℝ)) (τ := (459544061/500000000 : ℝ)) (σ := (992339181/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (781133126/830095657 : ℝ) ^ p + (818727011/830095657 : ℝ) ^ p := by
    exact cert_lt (x := (781133126/830095657 : ℝ)) (y := (818727011/830095657 : ℝ)) (X := (524006899807/2000000000000 : ℝ)) (Y := (9224956974777/12500000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (459544061/500000000 : ℝ)) (n' := (830095657/1000000000 : ℝ)) (Ab := (390566563/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (114886019/125000000 : ℝ) ^ p + (39693567/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (114886019/125000000 : ℝ)) (y := (39693567/40000000 : ℝ)) (X := (1948150985109/12500000000000 : ℝ)) (Y := (16882961435851/20000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (39693567/40000000 : ℝ) ^ p + (114886019/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (39693567/40000000 : ℝ)) (y := (114886019/125000000 : ℝ)) (X := (16882961435851/20000000000000 : ℝ)) (Y := (1948150985109/12500000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1911427327/1000000000 : ℝ)) (τ := (114886019/125000000 : ℝ)) (σ := (39693567/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (390566579/415047846 : ℝ) ^ p + (409363523/415047846 : ℝ) ^ p := by
    exact cert_lt (x := (390566579/415047846 : ℝ)) (y := (409363523/415047846 : ℝ)) (X := (26200344299013/100000000000000 : ℝ)) (Y := (73799656750141/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (114886019/125000000 : ℝ)) (n' := (207523923/250000000 : ℝ)) (Ab := (390566579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (919088153/1000000000 : ℝ) ^ p + (39693567/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (919088153/1000000000 : ℝ)) (y := (39693567/40000000 : ℝ)) (X := (15585208254461/100000000000000 : ℝ)) (Y := (16882961435851/20000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (39693567/40000000 : ℝ) ^ p + (919088153/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39693567/40000000 : ℝ)) (y := (919088153/1000000000 : ℝ)) (X := (16882961435851/20000000000000 : ℝ)) (Y := (15585208254461/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (7466513/3906250 : ℝ)) (τ := (919088153/1000000000 : ℝ)) (σ := (39693567/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (390566580/415047847 : ℝ) ^ p + (409363524/415047847 : ℝ) ^ p := by
    exact cert_lt (x := (390566580/415047847 : ℝ)) (y := (409363524/415047847 : ℝ)) (X := (26200344386187/100000000000000 : ℝ)) (Y := (73799656804537/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (919088153/1000000000 : ℝ)) (n' := (415047847/500000000 : ℝ)) (Ab := (19528329/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (7466513/3906250 : ℝ)) (τ := (919088153/1000000000 : ℝ)) (σ := (39693567/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (919088153/1000000000 : ℝ)) (n' := (415047847/500000000 : ℝ)) (Ab := (19528329/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (7466513/3906250 : ℝ)) (τ := (919088153/1000000000 : ℝ)) (σ := (39693567/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (919088153/1000000000 : ℝ)) (n' := (415047847/500000000 : ℝ)) (Ab := (19528329/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (7466513/3906250 : ℝ)) (τ := (919088153/1000000000 : ℝ)) (σ := (39693567/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (919088153/1000000000 : ℝ)) (n' := (415047847/500000000 : ℝ)) (Ab := (19528329/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (7466513/3906250 : ℝ)) (τ := (919088153/1000000000 : ℝ)) (σ := (39693567/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1647255427/1807214900 : ℝ) ^ p + (897923127/903607450 : ℝ) ^ p := by
    exact cert_lt (x := (1647255427/1807214900 : ℝ)) (y := (897923127/903607450 : ℝ)) (X := (12979784728259/100000000000000 : ℝ)) (Y := (87020215518769/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1106235113/1192785100 : ℝ) ^ p + (590708227/596392550 : ℝ) ^ p := by
    exact cert_lt (x := (1106235113/1192785100 : ℝ)) (y := (590708227/596392550 : ℝ)) (X := (19021852501849/100000000000000 : ℝ)) (Y := (80978148007631/100000000000000 : ℝ)) 705 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (39693567/40000000 : ℝ)) (U := (11927851/10000000 : ℝ)) (Ab := (1647255427/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (919088153/1000000000 : ℝ)) (σ := (39693567/40000000 : ℝ)) (Ab := (1106235113/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab032
