import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 99, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab099 (p : ℝ) (hpa : (771/32 : ℝ) ≤ p) (hpb : p ≤ (193/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (523205290067/26310375000000 : ℝ) (10233147/1000000000 : ℝ) (4000000631449/21048300000000 : ℝ) (3033/2500 : ℝ) (121459667/62500000 : ℝ) (485820563/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193631349/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11137/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4607/10000 : ℝ)
      else (1939/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11851/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (523205290067/26310375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10233147/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (92087559/100000000 : ℝ) ^ p + (248479211/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (92087559/100000000 : ℝ)) (y := (248479211/250000000 : ℝ)) (X := (13688258143231/100000000000000 : ℝ)) (Y := (86311760093623/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248479211/250000000 : ℝ) ^ p + (92087559/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248479211/250000000 : ℝ)) (y := (92087559/100000000 : ℝ)) (X := (86311760093623/100000000000000 : ℝ)) (Y := (13688258143231/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (957396217/500000000 : ℝ)) (τ := (92087559/100000000 : ℝ)) (σ := (248479211/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784927259/830187419 : ℝ) ^ p + (819954272/830187419 : ℝ) ^ p := by
    exact cert_lt (x := (784927259/830187419 : ℝ)) (y := (819954272/830187419 : ℝ)) (X := (25860385368279/100000000000000 : ℝ)) (Y := (37069808026557/50000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (92087559/100000000 : ℝ)) (n' := (830187419/1000000000 : ℝ)) (Ab := (784927259/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (115805991/125000000 : ℝ) ^ p + (496440413/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115805991/125000000 : ℝ)) (y := (496440413/500000000 : ℝ)) (X := (7916386246581/50000000000000 : ℝ)) (Y := (84167245457647/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496440413/500000000 : ℝ) ^ p + (115805991/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496440413/500000000 : ℝ)) (y := (115805991/125000000 : ℝ)) (X := (84167245457647/100000000000000 : ℝ)) (Y := (7916386246581/50000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (959664377/500000000 : ℝ)) (τ := (115805991/125000000 : ℝ)) (σ := (496440413/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (395461784/418382949 : ℝ) ^ p + (275510917/278921966 : ℝ) ^ p := by
    exact cert_lt (x := (395461784/418382949 : ℝ)) (y := (275510917/278921966 : ℝ)) (X := (12842346674323/50000000000000 : ℝ)) (Y := (18578826966659/25000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (115805991/125000000 : ℝ)) (n' := (418382949/500000000 : ℝ)) (Ab := (49432723/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (463342003/500000000 : ℝ) ^ p + (198566613/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (463342003/500000000 : ℝ)) (y := (198566613/200000000 : ℝ)) (X := (3982598128999/25000000000000 : ℝ)) (Y := (5254351501389/6250000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198566613/200000000 : ℝ) ^ p + (463342003/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198566613/200000000 : ℝ)) (y := (463342003/500000000 : ℝ)) (X := (5254351501389/6250000000000 : ℝ)) (Y := (3982598128999/25000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1919517071/1000000000 : ℝ)) (τ := (463342003/500000000 : ℝ)) (σ := (198566613/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (791176783/837043745 : ℝ) ^ p + (826810598/837043745 : ℝ) ^ p := by
    exact cert_lt (x := (791176783/837043745 : ℝ)) (y := (826810598/837043745 : ℝ)) (X := (12838662261869/50000000000000 : ℝ)) (Y := (37161338131187/50000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (463342003/500000000 : ℝ)) (n' := (167408749/200000000 : ℝ)) (Ab := (791176783/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (185338781/200000000 : ℝ) ^ p + (198566211/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (185338781/200000000 : ℝ)) (y := (198566211/200000000 : ℝ)) (X := (3186899680797/20000000000000 : ℝ)) (Y := (84065518049253/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198566211/200000000 : ℝ) ^ p + (185338781/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198566211/200000000 : ℝ)) (y := (185338781/200000000 : ℝ)) (X := (84065518049253/100000000000000 : ℝ)) (Y := (3186899680797/20000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (11997031/6250000 : ℝ)) (τ := (185338781/200000000 : ℝ)) (σ := (198566211/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (395593700/418527697 : ℝ) ^ p + (826822247/837055394 : ℝ) ^ p := by
    exact cert_lt (x := (395593700/418527697 : ℝ)) (y := (826822247/837055394 : ℝ)) (X := (25677016293599/100000000000000 : ℝ)) (Y := (18580746274457/25000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (185338781/200000000 : ℝ)) (n' := (418527697/500000000 : ℝ)) (Ab := (3955937/5000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (926694319/1000000000 : ℝ) ^ p + (992830971/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926694319/1000000000 : ℝ)) (y := (992830971/1000000000 : ℝ)) (X := (7967335072099/50000000000000 : ℝ)) (Y := (84065346460537/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992830971/1000000000 : ℝ) ^ p + (926694319/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992830971/1000000000 : ℝ)) (y := (926694319/1000000000 : ℝ)) (X := (84065346460537/100000000000000 : ℝ)) (Y := (7967335072099/50000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (191952529/100000000 : ℝ)) (τ := (926694319/1000000000 : ℝ)) (σ := (992830971/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (791187844/837055881 : ℝ) ^ p + (275607578/279018627 : ℝ) ^ p := by
    exact cert_lt (x := (791187844/837055881 : ℝ)) (y := (275607578/279018627 : ℝ)) (X := (25677003520657/100000000000000 : ℝ)) (Y := (74322998008893/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (926694319/1000000000 : ℝ)) (n' := (837055881/1000000000 : ℝ)) (Ab := (197796961/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (14479599/15625000 : ℝ) ^ p + (124103871/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (14479599/15625000 : ℝ)) (y := (124103871/125000000 : ℝ)) (X := (1593467719637/10000000000000 : ℝ)) (Y := (672522722659/800000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124103871/125000000 : ℝ) ^ p + (14479599/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (124103871/125000000 : ℝ)) (y := (14479599/15625000 : ℝ)) (X := (672522722659/800000000000 : ℝ)) (Y := (1593467719637/10000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (239940663/125000000 : ℝ)) (τ := (14479599/15625000 : ℝ)) (σ := (124103871/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (791187862/837055901 : ℝ) ^ p + (826822754/837055901 : ℝ) ^ p := by
    exact cert_lt (x := (791187862/837055901 : ℝ)) (y := (826822754/837055901 : ℝ)) (X := (1027080112513/4000000000000 : ℝ)) (Y := (74322998539121/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (14479599/15625000 : ℝ)) (n' := (837055901/1000000000 : ℝ)) (Ab := (395593931/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (463347169/500000000 : ℝ) ^ p + (992830967/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (463347169/500000000 : ℝ)) (y := (992830967/1000000000 : ℝ)) (X := (15934678026037/100000000000000 : ℝ)) (Y := (16813067657931/20000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992830967/1000000000 : ℝ) ^ p + (463347169/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992830967/1000000000 : ℝ)) (y := (463347169/500000000 : ℝ)) (X := (16813067657931/20000000000000 : ℝ)) (Y := (15934678026037/100000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (383905061/200000000 : ℝ)) (τ := (463347169/500000000 : ℝ)) (σ := (992830967/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (791187865/837055904 : ℝ) ^ p + (826822757/837055904 : ℝ) ^ p := by
    exact cert_lt (x := (791187865/837055904 : ℝ)) (y := (826822757/837055904 : ℝ)) (X := (12838501470767/50000000000000 : ℝ)) (Y := (14864599723731/20000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (463347169/500000000 : ℝ)) (n' := (26157997/31250000 : ℝ)) (Ab := (158237573/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (383905061/200000000 : ℝ)) (τ := (463347169/500000000 : ℝ)) (σ := (992830967/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (463347169/500000000 : ℝ)) (n' := (26157997/31250000 : ℝ)) (Ab := (158237573/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (383905061/200000000 : ℝ)) (τ := (463347169/500000000 : ℝ)) (σ := (992830967/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (463347169/500000000 : ℝ)) (n' := (26157997/31250000 : ℝ)) (Ab := (158237573/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (383905061/200000000 : ℝ)) (τ := (463347169/500000000 : ℝ)) (σ := (992830967/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (463347169/500000000 : ℝ)) (n' := (26157997/31250000 : ℝ)) (Ab := (158237573/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (383905061/200000000 : ℝ)) (τ := (463347169/500000000 : ℝ)) (σ := (992830967/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1658864060/1806368651 : ℝ) ^ p + (1796135504/1806368651 : ℝ) ^ p := by
    exact cert_lt (x := (1658864060/1806368651 : ℝ)) (y := (1796135504/1806368651 : ℝ)) (X := (2561600495093/20000000000000 : ℝ)) (Y := (21797999463767/25000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1113632011/1193631349 : ℝ) ^ p + (1183398202/1193631349 : ℝ) ^ p := by
    exact cert_lt (x := (1113632011/1193631349 : ℝ)) (y := (1183398202/1193631349 : ℝ)) (X := (4689102194789/25000000000000 : ℝ)) (Y := (40621795850117/50000000000000 : ℝ)) 193 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992830967/1000000000 : ℝ)) (U := (1193631349/1000000000 : ℝ)) (Ab := (82943203/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (463347169/500000000 : ℝ)) (σ := (992830967/1000000000 : ℝ)) (Ab := (1113632011/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab099
