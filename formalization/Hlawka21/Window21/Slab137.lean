import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 137, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab137 (p : ℝ) (hpa : (809/32 : ℝ) ≤ p) (hpb : p ≤ (405/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2080774593281/110428500000000 : ℝ) (38733/4000000 : ℝ) (4000000662571/22085700000000 : ℝ) (3033/2500 : ℝ) (48649397/25000000 : ℝ) (194591001/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597056811/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(447/400 : ℝ) ≤ X j i ∧ X j i ≤ -(467/1000 : ℝ)
      else (3909/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2080774593281/110428500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (38733/4000000 : ℝ) := by norm_num
  have pc0 : 1 < (924769083/1000000000 : ℝ) ^ p + (994145609/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924769083/1000000000 : ℝ)) (y := (994145609/1000000000 : ℝ)) (X := (3452692995809/25000000000000 : ℝ)) (Y := (86189247796791/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994145609/1000000000 : ℝ) ^ p + (924769083/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994145609/1000000000 : ℝ)) (y := (924769083/1000000000 : ℝ)) (X := (86189247796791/100000000000000 : ℝ)) (Y := (3452692995809/25000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (479728673/250000000 : ℝ)) (τ := (924769083/1000000000 : ℝ)) (σ := (994145609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (790067625/833764294 : ℝ) ^ p + (412040522/416882147 : ℝ) ^ p := by
    exact cert_lt (x := (790067625/833764294 : ℝ)) (y := (412040522/416882147 : ℝ)) (X := (5119745626103/20000000000000 : ℝ)) (Y := (37200636705557/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (924769083/1000000000 : ℝ)) (n' := (416882147/500000000 : ℝ)) (Ab := (6320541/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46508923/50000000 : ℝ) ^ p + (993131959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46508923/50000000 : ℝ)) (y := (993131959/1000000000 : ℝ)) (X := (8003941879747/50000000000000 : ℝ)) (Y := (16798426863967/20000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993131959/1000000000 : ℝ) ^ p + (46508923/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (993131959/1000000000 : ℝ)) (y := (46508923/50000000 : ℝ)) (X := (16798426863967/20000000000000 : ℝ)) (Y := (8003941879747/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1923310419/1000000000 : ℝ)) (τ := (46508923/50000000 : ℝ)) (σ := (993131959/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (795878715/840114574 : ℝ) ^ p + (415215662/420057287 : ℝ) ^ p := by
    exact cert_lt (x := (795878715/840114574 : ℝ)) (y := (415215662/420057287 : ℝ)) (X := (1271563793603/5000000000000 : ℝ)) (Y := (7456872526733/10000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46508923/50000000 : ℝ)) (n' := (420057287/500000000 : ℝ)) (Ab := (159175743/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (930393111/1000000000 : ℝ) ^ p + (496544067/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (930393111/1000000000 : ℝ)) (y := (496544067/500000000 : ℝ)) (X := (16101651697483/100000000000000 : ℝ)) (Y := (8389836609963/10000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496544067/500000000 : ℝ) ^ p + (930393111/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496544067/500000000 : ℝ)) (y := (930393111/1000000000 : ℝ)) (X := (8389836609963/10000000000000 : ℝ)) (Y := (16101651697483/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (384696249/200000000 : ℝ)) (τ := (930393111/1000000000 : ℝ)) (σ := (496544067/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (113729798/120052259 : ℝ) ^ p + (830682563/840365813 : ℝ) ^ p := by
    exact cert_lt (x := (113729798/120052259 : ℝ)) (y := (830682563/840365813 : ℝ)) (X := (6356173876547/25000000000000 : ℝ)) (Y := (37287652787997/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (930393111/1000000000 : ℝ)) (n' := (840365813/1000000000 : ℝ)) (Ab := (398054293/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (186080309/200000000 : ℝ) ^ p + (496543203/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (186080309/200000000 : ℝ)) (y := (496543203/500000000 : ℝ)) (X := (16105346748487/100000000000000 : ℝ)) (Y := (83894670922147/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496543203/500000000 : ℝ) ^ p + (186080309/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496543203/500000000 : ℝ)) (y := (186080309/200000000 : ℝ)) (X := (83894670922147/100000000000000 : ℝ)) (Y := (16105346748487/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1923487951/1000000000 : ℝ)) (τ := (186080309/200000000 : ℝ)) (σ := (496543203/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (796117617/840375683 : ℝ) ^ p + (830692433/840375683 : ℝ) ^ p := by
    exact cert_lt (x := (796117617/840375683 : ℝ)) (y := (830692433/840375683 : ℝ)) (X := (6356109367661/25000000000000 : ℝ)) (Y := (74575564016469/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (186080309/200000000 : ℝ)) (n' := (840375683/1000000000 : ℝ)) (Ab := (796117617/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (232600469/250000000 : ℝ) ^ p + (496543169/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232600469/250000000 : ℝ)) (y := (496543169/500000000 : ℝ)) (X := (4026372945183/25000000000000 : ℝ)) (Y := (83894525513267/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496543169/500000000 : ℝ) ^ p + (232600469/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496543169/500000000 : ℝ)) (y := (232600469/250000000 : ℝ)) (X := (83894525513267/100000000000000 : ℝ)) (Y := (4026372945183/25000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961744107/500000000 : ℝ)) (τ := (232600469/250000000 : ℝ)) (σ := (496543169/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (796117972/840376071 : ℝ) ^ p + (276897607/280125357 : ℝ) ^ p := by
    exact cert_lt (x := (796117972/840376071 : ℝ)) (y := (276897607/280125357 : ℝ)) (X := (5084885462519/20000000000000 : ℝ)) (Y := (74575574175927/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (232600469/250000000 : ℝ)) (n' := (840376071/1000000000 : ℝ)) (Ab := (199029493/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (29075059/31250000 : ℝ) ^ p + (7758487/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (29075059/31250000 : ℝ)) (y := (7758487/7812500 : ℝ)) (X := (8052748519361/50000000000000 : ℝ)) (Y := (41947260618269/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (7758487/7812500 : ℝ) ^ p + (29075059/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (7758487/7812500 : ℝ)) (y := (29075059/31250000 : ℝ)) (X := (41947260618269/50000000000000 : ℝ)) (Y := (8052748519361/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (60109007/31250000 : ℝ)) (τ := (29075059/31250000 : ℝ)) (σ := (7758487/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (796117984/840376085 : ℝ) ^ p + (166138567/168075217 : ℝ) ^ p := by
    exact cert_lt (x := (796117984/840376085 : ℝ)) (y := (166138567/168075217 : ℝ)) (X := (25424426291873/100000000000000 : ℝ)) (Y := (37287787271253/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (29075059/31250000 : ℝ)) (n' := (168075217/200000000 : ℝ)) (Ab := (24878687/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (93040189/100000000 : ℝ) ^ p + (198617267/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (93040189/100000000 : ℝ)) (y := (198617267/200000000 : ℝ)) (X := (8052748957527/50000000000000 : ℝ)) (Y := (41947259549087/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198617267/200000000 : ℝ) ^ p + (93040189/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198617267/200000000 : ℝ)) (y := (93040189/100000000 : ℝ)) (X := (41947259549087/50000000000000 : ℝ)) (Y := (8052748957527/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (796117986/840376087 : ℝ) ^ p + (830692837/840376087 : ℝ) ^ p := by
    exact cert_lt (x := (796117986/840376087 : ℝ)) (y := (830692837/840376087 : ℝ)) (X := (12712213188509/50000000000000 : ℝ)) (Y := (37287787297437/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (832314047/902943189 : ℝ) ^ p + (299367188/300981063 : ℝ) ^ p := by
    exact cert_lt (x := (832314047/902943189 : ℝ)) (y := (299367188/300981063 : ℝ)) (X := (12723770335939/100000000000000 : ℝ)) (Y := (17455245980553/20000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (558701423/597056811 : ℝ) ^ p + (197405062/199018937 : ℝ) ^ p := by
    exact cert_lt (x := (558701423/597056811 : ℝ)) (y := (197405062/199018937 : ℝ)) (X := (18624807845897/100000000000000 : ℝ)) (Y := (81375192888689/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198617267/200000000 : ℝ)) (U := (597056811/500000000 : ℝ)) (Ab := (832314047/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ)) (Ab := (558701423/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab137
