import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 74, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab074 (p : ℝ) (hpa : (245/8 : ℝ) ≤ p) (hpb : p ≤ (491/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (71323425941/5426750000000 : ℝ) (6721899/1000000000 : ℝ) (320000065121/2170700000000 : ℝ) (591/500 : ℝ) (488832951/250000000 : ℝ) (244405209/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144772203/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10919/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5621/10000 : ℝ)
      else (4139/5000 : ℝ) ≤ X j i ∧ X j i ≤ (719/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (71323425941/5426750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6721899/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (471868847/500000000 : ℝ) ^ p + (993980063/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471868847/500000000 : ℝ)) (y := (993980063/1000000000 : ℝ)) (X := (16914116547119/100000000000000 : ℝ)) (Y := (1661718105027/2000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993980063/1000000000 : ℝ) ^ p + (471868847/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993980063/1000000000 : ℝ)) (y := (471868847/500000000 : ℝ)) (X := (1661718105027/2000000000000 : ℝ)) (Y := (16914116547119/100000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1937717757/1000000000 : ℝ)) (τ := (471868847/500000000 : ℝ)) (σ := (993980063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (827621293/870571991 : ℝ) ^ p + (863850092/870571991 : ℝ) ^ p := by
    exact cert_lt (x := (827621293/870571991 : ℝ)) (y := (863850092/870571991 : ℝ)) (X := (5292276219249/25000000000000 : ℝ)) (Y := (78830896568541/100000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (471868847/500000000 : ℝ)) (n' := (870571991/1000000000 : ℝ)) (Ab := (827621293/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (946880583/1000000000 : ℝ) ^ p + (15519753/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (946880583/1000000000 : ℝ)) (y := (15519753/15625000 : ℝ)) (X := (18730927540771/100000000000000 : ℝ)) (Y := (40634546037979/50000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (15519753/15625000 : ℝ) ^ p + (946880583/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (15519753/15625000 : ℝ)) (y := (946880583/1000000000 : ℝ)) (X := (40634546037979/50000000000000 : ℝ)) (Y := (18730927540771/100000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (77605791/40000000 : ℝ)) (τ := (946880583/1000000000 : ℝ)) (σ := (15519753/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (830924935/874151021 : ℝ) ^ p + (867429122/874151021 : ℝ) ^ p := by
    exact cert_lt (x := (830924935/874151021 : ℝ)) (y := (867429122/874151021 : ℝ)) (X := (21091997601057/100000000000000 : ℝ)) (Y := (19727000982353/25000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (946880583/1000000000 : ℝ)) (n' := (874151021/1000000000 : ℝ)) (Ab := (166184987/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (29592567/31250000 : ℝ) ^ p + (496622221/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (29592567/31250000 : ℝ)) (y := (496622221/500000000 : ℝ)) (X := (58689070721/312500000000 : ℝ)) (Y := (81219517265687/100000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496622221/500000000 : ℝ) ^ p + (29592567/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (496622221/500000000 : ℝ)) (y := (29592567/31250000 : ℝ)) (X := (81219517265687/100000000000000 : ℝ)) (Y := (58689070721/312500000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (970103293/500000000 : ℝ)) (τ := (29592567/31250000 : ℝ)) (σ := (496622221/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (831010516/874243743 : ℝ) ^ p + (289173948/291414581 : ℝ) ^ p := by
    exact cert_lt (x := (831010516/874243743 : ℝ)) (y := (289173948/291414581 : ℝ)) (X := (5272501723683/25000000000000 : ℝ)) (Y := (19727498531649/25000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (29592567/31250000 : ℝ)) (n' := (874243743/1000000000 : ℝ)) (Ab := (207752629/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (118370531/125000000 : ℝ) ^ p + (248310983/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (118370531/125000000 : ℝ)) (y := (248310983/250000000 : ℝ)) (X := (18781783179603/100000000000000 : ℝ)) (Y := (40609118746797/50000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248310983/250000000 : ℝ) ^ p + (118370531/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248310983/250000000 : ℝ)) (y := (118370531/125000000 : ℝ)) (X := (40609118746797/50000000000000 : ℝ)) (Y := (18781783179603/100000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (97010409/50000000 : ℝ)) (τ := (118370531/125000000 : ℝ)) (σ := (248310983/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (831012724/874246135 : ℝ) ^ p + (867524236/874246135 : ℝ) ^ p := by
    exact cert_lt (x := (831012724/874246135 : ℝ)) (y := (867524236/874246135 : ℝ)) (X := (2636244464867/12500000000000 : ℝ)) (Y := (15782009092771/20000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (118370531/125000000 : ℝ)) (n' := (174849227/200000000 : ℝ)) (Ab := (207753181/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (946964303/1000000000 : ℝ) ^ p + (496621959/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (946964303/1000000000 : ℝ)) (y := (496621959/500000000 : ℝ)) (X := (469545416379/2500000000000 : ℝ)) (Y := (8121820236287/10000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496621959/500000000 : ℝ) ^ p + (946964303/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496621959/500000000 : ℝ)) (y := (946964303/1000000000 : ℝ)) (X := (8121820236287/10000000000000 : ℝ)) (Y := (469545416379/2500000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1940208221/1000000000 : ℝ)) (τ := (946964303/1000000000 : ℝ)) (σ := (496621959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (831012781/874246197 : ℝ) ^ p + (289174766/291415399 : ℝ) ^ p := by
    exact cert_lt (x := (831012781/874246197 : ℝ)) (y := (289174766/291415399 : ℝ)) (X := (10544977106377/50000000000000 : ℝ)) (Y := (157820093589/200000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (946964303/1000000000 : ℝ)) (n' := (874246197/1000000000 : ℝ)) (Ab := (831012781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (59185269/62500000 : ℝ) ^ p + (496621959/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (59185269/62500000 : ℝ)) (y := (496621959/500000000 : ℝ)) (X := (18781817263807/100000000000000 : ℝ)) (Y := (8121820236287/10000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496621959/500000000 : ℝ) ^ p + (59185269/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (496621959/500000000 : ℝ)) (y := (59185269/62500000 : ℝ)) (X := (8121820236287/10000000000000 : ℝ)) (Y := (18781817263807/100000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (970104111/500000000 : ℝ)) (τ := (59185269/62500000 : ℝ)) (σ := (496621959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (831012783/874246199 : ℝ) ^ p + (867524300/874246199 : ℝ) ^ p := by
    exact cert_lt (x := (831012783/874246199 : ℝ)) (y := (867524300/874246199 : ℝ)) (X := (21089954289781/100000000000000 : ℝ)) (Y := (4931877927339/6250000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (59185269/62500000 : ℝ)) (n' := (874246199/1000000000 : ℝ)) (Ab := (831012783/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (189392861/200000000 : ℝ) ^ p + (496621959/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (189392861/200000000 : ℝ)) (y := (496621959/500000000 : ℝ)) (X := (9390908936227/50000000000000 : ℝ)) (Y := (8121820236287/10000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496621959/500000000 : ℝ) ^ p + (189392861/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496621959/500000000 : ℝ)) (y := (189392861/200000000 : ℝ)) (X := (8121820236287/10000000000000 : ℝ)) (Y := (9390908936227/50000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1940208223/1000000000 : ℝ)) (τ := (189392861/200000000 : ℝ)) (σ := (496621959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (103876598/109280775 : ℝ) ^ p + (289174767/291415400 : ℝ) ^ p := by
    exact cert_lt (x := (103876598/109280775 : ℝ)) (y := (289174767/291415400 : ℝ)) (X := (4217990865659/20000000000000 : ℝ)) (Y := (39455023429443/50000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (189392861/200000000 : ℝ)) (n' := (4371231/5000000 : ℝ)) (Ab := (51938299/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1940208223/1000000000 : ℝ)) (τ := (189392861/200000000 : ℝ)) (σ := (496621959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (189392861/200000000 : ℝ)) (n' := (4371231/5000000 : ℝ)) (Ab := (51938299/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1940208223/1000000000 : ℝ)) (τ := (189392861/200000000 : ℝ)) (σ := (496621959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (189392861/200000000 : ℝ)) (n' := (4371231/5000000 : ℝ)) (Ab := (51938299/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1940208223/1000000000 : ℝ)) (τ := (189392861/200000000 : ℝ)) (σ := (496621959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (189392861/200000000 : ℝ)) (n' := (4371231/5000000 : ℝ)) (Ab := (51938299/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1940208223/1000000000 : ℝ)) (τ := (189392861/200000000 : ℝ)) (σ := (496621959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1712000833/1841822376 : ℝ) ^ p + (611700159/613940792 : ℝ) ^ p := by
    exact cert_lt (x := (1712000833/1841822376 : ℝ)) (y := (611700159/613940792 : ℝ)) (X := (5306802984637/50000000000000 : ℝ)) (Y := (89386394310601/100000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (545912923/579088812 : ℝ) ^ p + (383818575/386059208 : ℝ) ^ p := by
    exact cert_lt (x := (545912923/579088812 : ℝ)) (y := (383818575/386059208 : ℝ)) (X := (16358031294433/100000000000000 : ℝ)) (Y := (20910492345727/25000000000000 : ℝ)) 491 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496621959/500000000 : ℝ)) (U := (144772203/125000000 : ℝ)) (Ab := (1712000833/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (189392861/200000000 : ℝ)) (σ := (496621959/500000000 : ℝ)) (Ab := (545912923/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab074
