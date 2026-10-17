import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 74, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab074 (p : ℝ) (hpa : (373/16 : ℝ) ≤ p) (hpb : p ≤ (747/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1050704263801/50914500000000 : ℝ) (10629721/1000000000 : ℝ) (2000000305487/10182900000000 : ℝ) (3033/2500 : ℝ) (30335733/15625000 : ℝ) (970704817/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149164171/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1111/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(2281/5000 : ℝ)
      else (482/625 : ℝ) ≤ X j i ∧ X j i ≤ (5923/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1050704263801/50914500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10629721/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (57380461/62500000 : ℝ) ^ p + (993756869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57380461/62500000 : ℝ)) (y := (993756869/1000000000 : ℝ)) (X := (13601090879641/100000000000000 : ℝ)) (Y := (5399932973091/6250000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993756869/1000000000 : ℝ) ^ p + (57380461/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (993756869/1000000000 : ℝ)) (y := (57380461/62500000 : ℝ)) (X := (5399932973091/6250000000000 : ℝ)) (Y := (13601090879641/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (382368849/200000000 : ℝ)) (τ := (57380461/62500000 : ℝ)) (σ := (993756869/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (781255236/827597383 : ℝ) ^ p + (42998298/43557757 : ℝ) ^ p := by
    exact cert_lt (x := (781255236/827597383 : ℝ)) (y := (42998298/43557757 : ℝ)) (X := (26049260482821/100000000000000 : ℝ)) (Y := (73950740519569/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (57380461/62500000 : ℝ)) (n' := (827597383/1000000000 : ℝ)) (Ab := (195313809/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (115470903/125000000 : ℝ) ^ p + (198541361/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (115470903/125000000 : ℝ)) (y := (198541361/200000000 : ℝ)) (X := (3926817913297/25000000000000 : ℝ)) (Y := (84292744601651/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198541361/200000000 : ℝ) ^ p + (115470903/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (198541361/200000000 : ℝ)) (y := (115470903/125000000 : ℝ)) (X := (84292744601651/100000000000000 : ℝ)) (Y := (3926817913297/25000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1916474029/1000000000 : ℝ)) (τ := (115470903/125000000 : ℝ)) (σ := (198541361/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (787374908/834329863 : ℝ) ^ p + (823700142/834329863 : ℝ) ^ p := by
    exact cert_lt (x := (787374908/834329863 : ℝ)) (y := (823700142/834329863 : ℝ)) (X := (5173560533269/20000000000000 : ℝ)) (Y := (3706609942739/5000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (115470903/125000000 : ℝ)) (n' := (834329863/1000000000 : ℝ)) (Ab := (196843727/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (924019047/1000000000 : ℝ) ^ p + (198531239/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (924019047/1000000000 : ℝ)) (y := (198531239/200000000 : ℝ)) (X := (493985362129/3125000000000 : ℝ)) (Y := (16838496868719/20000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198531239/200000000 : ℝ) ^ p + (924019047/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198531239/200000000 : ℝ)) (y := (924019047/1000000000 : ℝ)) (X := (16838496868719/20000000000000 : ℝ)) (Y := (493985362129/3125000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958337621/500000000 : ℝ)) (τ := (924019047/1000000000 : ℝ)) (σ := (198531239/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (787645328/834627417 : ℝ) ^ p + (823997696/834627417 : ℝ) ^ p := by
    exact cert_lt (x := (787645328/834627417 : ℝ)) (y := (823997696/834627417 : ℝ)) (X := (25859839893027/100000000000000 : ℝ)) (Y := (74140160919411/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (924019047/1000000000 : ℝ)) (n' := (834627417/1000000000 : ℝ)) (Ab := (49227833/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462015047/500000000 : ℝ) ^ p + (992653967/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462015047/500000000 : ℝ)) (y := (992653967/1000000000 : ℝ)) (X := (247061621837/1562500000000 : ℝ)) (Y := (42094036609181/50000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992653967/1000000000 : ℝ) ^ p + (462015047/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992653967/1000000000 : ℝ)) (y := (462015047/500000000 : ℝ)) (X := (42094036609181/50000000000000 : ℝ)) (Y := (247061621837/1562500000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1916684061/1000000000 : ℝ)) (τ := (462015047/500000000 : ℝ)) (σ := (992653967/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (787657189/834640468 : ℝ) ^ p + (824010747/834640468 : ℝ) ^ p := by
    exact cert_lt (x := (787657189/834640468 : ℝ)) (y := (824010747/834640468 : ℝ)) (X := (12929745458061/50000000000000 : ℝ)) (Y := (18535127507967/25000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (462015047/500000000 : ℝ)) (n' := (208660117/250000000 : ℝ)) (Ab := (787657189/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (462015289/500000000 : ℝ) ^ p + (992653869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462015289/500000000 : ℝ)) (y := (992653869/1000000000 : ℝ)) (X := (15812137135769/100000000000000 : ℝ)) (Y := (84187879197287/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992653869/1000000000 : ℝ) ^ p + (462015289/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992653869/1000000000 : ℝ)) (y := (462015289/500000000 : ℝ)) (X := (84187879197287/100000000000000 : ℝ)) (Y := (15812137135769/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1916684447/1000000000 : ℝ)) (τ := (462015289/500000000 : ℝ)) (σ := (992653869/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (787657709/834641040 : ℝ) ^ p + (824011319/834641040 : ℝ) ^ p := by
    exact cert_lt (x := (787657709/834641040 : ℝ)) (y := (824011319/834641040 : ℝ)) (X := (5171895148117/20000000000000 : ℝ)) (Y := (2316891416643/3125000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (462015289/500000000 : ℝ)) (n' := (10433013/12500000 : ℝ)) (Ab := (787657709/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924030599/1000000000 : ℝ) ^ p + (198530773/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (924030599/1000000000 : ℝ)) (y := (198530773/200000000 : ℝ)) (X := (15812145524461/100000000000000 : ℝ)) (Y := (21046967819517/25000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198530773/200000000 : ℝ) ^ p + (924030599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198530773/200000000 : ℝ)) (y := (924030599/1000000000 : ℝ)) (X := (21046967819517/25000000000000 : ℝ)) (Y := (15812145524461/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (119792779/62500000 : ℝ)) (τ := (924030599/1000000000 : ℝ)) (σ := (198530773/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (787657732/834641065 : ℝ) ^ p + (824011344/834641065 : ℝ) ^ p := by
    exact cert_lt (x := (787657732/834641065 : ℝ)) (y := (824011344/834641065 : ℝ)) (X := (404054301349/1562500000000 : ℝ)) (Y := (74140526001313/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924030599/1000000000 : ℝ)) (n' := (166928213/200000000 : ℝ)) (Ab := (196914433/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (4620153/5000000 : ℝ) ^ p + (198530773/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (4620153/5000000 : ℝ)) (y := (198530773/200000000 : ℝ)) (X := (15812145923923/100000000000000 : ℝ)) (Y := (21046967819517/25000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198530773/200000000 : ℝ) ^ p + (4620153/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (198530773/200000000 : ℝ)) (y := (4620153/5000000 : ℝ)) (X := (21046967819517/25000000000000 : ℝ)) (Y := (15812145923923/100000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (383336893/200000000 : ℝ)) (τ := (4620153/5000000 : ℝ)) (σ := (198530773/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (787657733/834641066 : ℝ) ^ p + (824011345/834641066 : ℝ) ^ p := by
    exact cert_lt (x := (787657733/834641066 : ℝ)) (y := (824011345/834641066 : ℝ)) (X := (12929737664739/50000000000000 : ℝ)) (Y := (37070263014031/50000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (4620153/5000000 : ℝ)) (n' := (417320533/500000000 : ℝ)) (Ab := (787657733/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (383336893/200000000 : ℝ)) (τ := (4620153/5000000 : ℝ)) (σ := (198530773/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (4620153/5000000 : ℝ)) (n' := (417320533/500000000 : ℝ)) (Ab := (787657733/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (383336893/200000000 : ℝ)) (τ := (4620153/5000000 : ℝ)) (σ := (198530773/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (4620153/5000000 : ℝ)) (n' := (417320533/500000000 : ℝ)) (Ab := (787657733/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (383336893/200000000 : ℝ)) (τ := (4620153/5000000 : ℝ)) (σ := (198530773/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (4620153/5000000 : ℝ)) (n' := (417320533/500000000 : ℝ)) (Ab := (787657733/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (383336893/200000000 : ℝ)) (τ := (4620153/5000000 : ℝ)) (σ := (198530773/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1654765691/1806686632 : ℝ) ^ p + (1796056911/1806686632 : ℝ) ^ p := by
    exact cert_lt (x := (1654765691/1806686632 : ℝ)) (y := (1796056911/1806686632 : ℝ)) (X := (2573663493267/20000000000000 : ℝ)) (Y := (17426336566249/20000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1110990489/1193313368 : ℝ) ^ p + (1182683647/1193313368 : ℝ) ^ p := by
    exact cert_lt (x := (1110990489/1193313368 : ℝ)) (y := (1182683647/1193313368 : ℝ)) (X := (1178128863517/6250000000000 : ℝ)) (Y := (20287484680159/25000000000000 : ℝ)) 747 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198530773/200000000 : ℝ)) (U := (149164171/125000000 : ℝ)) (Ab := (1654765691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (4620153/5000000 : ℝ)) (σ := (198530773/200000000 : ℝ)) (Ab := (1110990489/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab074
