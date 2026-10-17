import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 33, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab033 (p : ℝ) (hpa : (705/32 : ℝ) ≤ p) (hpb : p ≤ (353/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (84671916803/3849300000000 : ℝ) (2837471/250000000 : ℝ) (800000115479/3849300000000 : ℝ) (3033/2500 : ℝ) (242267741/125000000 : ℝ) (969027779/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596398757/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1383/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(56/125 : ℝ)
      else (7631/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11837/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (84671916803/3849300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2837471/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (228266249/250000000 : ℝ) ^ p + (993476657/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (228266249/250000000 : ℝ)) (y := (993476657/1000000000 : ℝ)) (X := (13445241762967/100000000000000 : ℝ)) (Y := (43277387723201/50000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993476657/1000000000 : ℝ) ^ p + (228266249/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993476657/1000000000 : ℝ)) (y := (228266249/250000000 : ℝ)) (X := (43277387723201/50000000000000 : ℝ)) (Y := (13445241762967/100000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1906541653/1000000000 : ℝ)) (τ := (228266249/250000000 : ℝ)) (σ := (993476657/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (774659136/822872057 : ℝ) ^ p + (115931739/117553151 : ℝ) ^ p := by
    exact cert_lt (x := (774659136/822872057 : ℝ)) (y := (115931739/117553151 : ℝ)) (X := (3299092320839/12500000000000 : ℝ)) (Y := (18401815677619/25000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (228266249/250000000 : ℝ)) (n' := (822872057/1000000000 : ℝ)) (Ab := (12104049/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (22972961/25000000 : ℝ) ^ p + (198481099/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (22972961/25000000 : ℝ)) (y := (198481099/200000000 : ℝ)) (X := (15480966694239/100000000000000 : ℝ)) (Y := (42259524279877/50000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198481099/200000000 : ℝ) ^ p + (22972961/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (198481099/200000000 : ℝ)) (y := (22972961/25000000 : ℝ)) (X := (42259524279877/50000000000000 : ℝ)) (Y := (15480966694239/100000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (382264787/200000000 : ℝ)) (τ := (22972961/25000000 : ℝ)) (σ := (198481099/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (390490326/414930451 : ℝ) ^ p + (31481193/31917727 : ℝ) ^ p := by
    exact cert_lt (x := (390490326/414930451 : ℝ)) (y := (31481193/31917727 : ℝ)) (X := (818788191253/3125000000000 : ℝ)) (Y := (2951951153109/4000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (22972961/25000000 : ℝ)) (n' := (414930451/500000000 : ℝ)) (Ab := (195245163/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (183839869/200000000 : ℝ) ^ p + (248087429/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (183839869/200000000 : ℝ)) (y := (248087429/250000000 : ℝ)) (X := (48705349599/312500000000 : ℝ)) (Y := (21103575857457/25000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248087429/250000000 : ℝ) ^ p + (183839869/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248087429/250000000 : ℝ)) (y := (183839869/200000000 : ℝ)) (X := (21103575857457/25000000000000 : ℝ)) (Y := (48705349599/312500000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1911549061/1000000000 : ℝ)) (τ := (183839869/200000000 : ℝ)) (σ := (248087429/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (781282969/830195200 : ℝ) ^ p + (204711329/207548800 : ℝ) ^ p := by
    exact cert_lt (x := (781282969/830195200 : ℝ)) (y := (204711329/207548800 : ℝ)) (X := (5238426061649/20000000000000 : ℝ)) (Y := (3690393531403/5000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (183839869/200000000 : ℝ)) (n' := (64859/78125 : ℝ)) (Ab := (781282969/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (919212677/1000000000 : ℝ) ^ p + (496173529/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (919212677/1000000000 : ℝ)) (y := (496173529/500000000 : ℝ)) (X := (15590699950441/100000000000000 : ℝ)) (Y := (10551164396719/12500000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496173529/500000000 : ℝ) ^ p + (919212677/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496173529/500000000 : ℝ)) (y := (919212677/1000000000 : ℝ)) (X := (10551164396719/12500000000000 : ℝ)) (Y := (15590699950441/100000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (382311947/200000000 : ℝ)) (τ := (919212677/1000000000 : ℝ)) (σ := (496173529/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (781297315/830211064 : ℝ) ^ p + (204715295/207552766 : ℝ) ^ p := by
    exact cert_lt (x := (781297315/830211064 : ℝ)) (y := (204715295/207552766 : ℝ)) (X := (13095849427787/50000000000000 : ℝ)) (Y := (73808301920999/100000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (919212677/1000000000 : ℝ)) (n' := (103776383/125000000 : ℝ)) (Ab := (156259463/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (919213309/1000000000 : ℝ) ^ p + (248086733/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (919213309/1000000000 : ℝ)) (y := (248086733/250000000 : ℝ)) (X := (3897734111713/25000000000000 : ℝ)) (Y := (21102269679283/25000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248086733/250000000 : ℝ) ^ p + (919213309/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248086733/250000000 : ℝ)) (y := (919213309/1000000000 : ℝ)) (X := (21102269679283/25000000000000 : ℝ)) (Y := (3897734111713/25000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1911560241/1000000000 : ℝ)) (τ := (919213309/1000000000 : ℝ)) (σ := (248086733/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (195324499/207552954 : ℝ) ^ p + (29245069/29650422 : ℝ) ^ p := by
    exact cert_lt (x := (195324499/207552954 : ℝ)) (y := (29245069/29650422 : ℝ)) (X := (26191679112311/100000000000000 : ℝ)) (Y := (73808322365197/100000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (919213309/1000000000 : ℝ)) (n' := (103776477/125000000 : ℝ)) (Ab := (195324499/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (919213339/1000000000 : ℝ) ^ p + (496173463/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (919213339/1000000000 : ℝ)) (y := (496173463/500000000 : ℝ)) (X := (1948868459129/12500000000000 : ℝ)) (Y := (21102266864327/25000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496173463/500000000 : ℝ) ^ p + (919213339/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496173463/500000000 : ℝ)) (y := (919213339/1000000000 : ℝ)) (X := (21102266864327/25000000000000 : ℝ)) (Y := (1948868459129/12500000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (382312053/200000000 : ℝ)) (τ := (919213339/1000000000 : ℝ)) (σ := (496173463/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (781298027/830211851 : ℝ) ^ p + (116980281/118601693 : ℝ) ^ p := by
    exact cert_lt (x := (781298027/830211851 : ℝ)) (y := (116980281/118601693 : ℝ)) (X := (26191677679029/100000000000000 : ℝ)) (Y := (73808323316721/100000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (919213339/1000000000 : ℝ)) (n' := (830211851/1000000000 : ℝ)) (Ab := (781298027/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (45960667/50000000 : ℝ) ^ p + (496173463/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (45960667/50000000 : ℝ)) (y := (496173463/500000000 : ℝ)) (X := (7795474023619/50000000000000 : ℝ)) (Y := (21102266864327/25000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496173463/500000000 : ℝ) ^ p + (45960667/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (496173463/500000000 : ℝ)) (y := (45960667/50000000 : ℝ)) (X := (21102266864327/25000000000000 : ℝ)) (Y := (7795474023619/50000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (955780133/500000000 : ℝ)) (τ := (45960667/50000000 : ℝ)) (σ := (496173463/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (65108169/69184321 : ℝ) ^ p + (204715492/207552963 : ℝ) ^ p := by
    exact cert_lt (x := (65108169/69184321 : ℝ)) (y := (204715492/207552963 : ℝ)) (X := (5238335544521/20000000000000 : ℝ)) (Y := (73808323343907/100000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (45960667/50000000 : ℝ)) (n' := (207552963/250000000 : ℝ)) (Ab := (195324507/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (955780133/500000000 : ℝ)) (τ := (45960667/50000000 : ℝ)) (σ := (496173463/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (45960667/50000000 : ℝ)) (n' := (207552963/250000000 : ℝ)) (Ab := (195324507/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (955780133/500000000 : ℝ)) (τ := (45960667/50000000 : ℝ)) (σ := (496173463/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (45960667/50000000 : ℝ)) (n' := (207552963/250000000 : ℝ)) (Ab := (195324507/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (955780133/500000000 : ℝ)) (τ := (45960667/50000000 : ℝ)) (σ := (496173463/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (45960667/50000000 : ℝ)) (n' := (207552963/250000000 : ℝ)) (Ab := (195324507/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (955780133/500000000 : ℝ)) (τ := (45960667/50000000 : ℝ)) (σ := (496173463/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1647444171/1807202486 : ℝ) ^ p + (897926301/903601243 : ℝ) ^ p := by
    exact cert_lt (x := (1647444171/1807202486 : ℝ)) (y := (897926301/903601243 : ℝ)) (X := (648848556809/5000000000000 : ℝ)) (Y := (43511514567941/50000000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1106353287/1192797514 : ℝ) ^ p + (590723815/596398757 : ℝ) ^ p := by
    exact cert_lt (x := (1106353287/1192797514 : ℝ)) (y := (590723815/596398757 : ℝ)) (X := (4754384122863/25000000000000 : ℝ)) (Y := (5061404008363/6250000000000 : ℝ)) 353 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496173463/500000000 : ℝ)) (U := (596398757/500000000 : ℝ)) (Ab := (1647444171/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (45960667/50000000 : ℝ)) (σ := (496173463/500000000 : ℝ)) (Ab := (1106353287/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab033
