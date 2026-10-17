import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 64, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab064 (p : ℝ) (hpa : (23 : ℝ) ≤ p) (hpb : p ≤ (737/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (32890711223/1569750000000 : ℝ) (10796949/1000000000 : ℝ) (125000018837/627900000000 : ℝ) (3033/2500 : ℝ) (970352431/500000000 : ℝ) (60644547/62500000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193186591/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11099/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4543/10000 : ℝ)
      else (7693/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2961/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (32890711223/1569750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10796949/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (916916483/1000000000 : ℝ) ^ p + (496845317/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (916916483/1000000000 : ℝ)) (y := (496845317/500000000 : ℝ)) (X := (6782311746451/50000000000000 : ℝ)) (Y := (17287078853197/20000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496845317/500000000 : ℝ) ^ p + (916916483/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496845317/500000000 : ℝ)) (y := (916916483/1000000000 : ℝ)) (X := (17287078853197/20000000000000 : ℝ)) (Y := (6782311746451/50000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1910607117/1000000000 : ℝ)) (τ := (916916483/1000000000 : ℝ)) (σ := (496845317/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779715389/826502623 : ℝ) ^ p + (815705674/826502623 : ℝ) ^ p := by
    exact cert_lt (x := (779715389/826502623 : ℝ)) (y := (815705674/826502623 : ℝ)) (X := (13064479963727/50000000000000 : ℝ)) (Y := (36935520666797/50000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916916483/1000000000 : ℝ)) (n' := (826502623/1000000000 : ℝ)) (Ab := (779715389/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (28832473/31250000 : ℝ) ^ p + (992635167/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28832473/31250000 : ℝ)) (y := (992635167/1000000000 : ℝ)) (X := (3130907992143/20000000000000 : ℝ)) (Y := (1686909523247/2000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992635167/1000000000 : ℝ) ^ p + (28832473/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (992635167/1000000000 : ℝ)) (y := (28832473/31250000 : ℝ)) (X := (1686909523247/2000000000000 : ℝ)) (Y := (3130907992143/20000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1915274303/1000000000 : ℝ)) (τ := (28832473/31250000 : ℝ)) (σ := (992635167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785884491/833297336 : ℝ) ^ p + (822500387/833297336 : ℝ) ^ p := by
    exact cert_lt (x := (785884491/833297336 : ℝ)) (y := (822500387/833297336 : ℝ)) (X := (5189023386527/20000000000000 : ℝ)) (Y := (74054884224587/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (28832473/31250000 : ℝ)) (n' := (104162167/125000000 : ℝ)) (Ab := (785884491/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922897661/1000000000 : ℝ) ^ p + (198516671/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (922897661/1000000000 : ℝ)) (y := (198516671/200000000 : ℝ)) (X := (15755877312183/100000000000000 : ℝ)) (Y := (84244138632477/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198516671/200000000 : ℝ) ^ p + (922897661/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198516671/200000000 : ℝ)) (y := (922897661/1000000000 : ℝ)) (X := (84244138632477/100000000000000 : ℝ)) (Y := (15755877312183/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (239435127/125000000 : ℝ)) (τ := (922897661/1000000000 : ℝ)) (σ := (198516671/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (786162249/833603318 : ℝ) ^ p + (822806369/833603318 : ℝ) ^ p := by
    exact cert_lt (x := (786162249/833603318 : ℝ)) (y := (822806369/833603318 : ℝ)) (X := (25936898545381/100000000000000 : ℝ)) (Y := (74063102783103/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922897661/1000000000 : ℝ)) (n' := (416801659/500000000 : ℝ)) (Ab := (786162249/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (184581843/200000000 : ℝ) ^ p + (992581031/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184581843/200000000 : ℝ)) (y := (992581031/1000000000 : ℝ)) (X := (15760420898797/100000000000000 : ℝ)) (Y := (84239595921167/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992581031/1000000000 : ℝ) ^ p + (184581843/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992581031/1000000000 : ℝ)) (y := (184581843/200000000 : ℝ)) (X := (84239595921167/100000000000000 : ℝ)) (Y := (15760420898797/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957745123/500000000 : ℝ)) (τ := (184581843/200000000 : ℝ)) (σ := (992581031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (786174660/833616991 : ℝ) ^ p + (822820042/833616991 : ℝ) ^ p := by
    exact cert_lt (x := (786174660/833616991 : ℝ)) (y := (822820042/833616991 : ℝ)) (X := (12968265449099/50000000000000 : ℝ)) (Y := (74063469914141/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (184581843/200000000 : ℝ)) (n' := (833616991/1000000000 : ℝ)) (Ab := (39308733/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922909731/1000000000 : ℝ) ^ p + (992580927/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922909731/1000000000 : ℝ)) (y := (992580927/1000000000 : ℝ)) (X := (3152124768793/20000000000000 : ℝ)) (Y := (84239392638359/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992580927/1000000000 : ℝ) ^ p + (922909731/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992580927/1000000000 : ℝ)) (y := (922909731/1000000000 : ℝ)) (X := (84239392638359/100000000000000 : ℝ)) (Y := (3152124768793/20000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (957745329/500000000 : ℝ)) (τ := (922909731/1000000000 : ℝ)) (σ := (992580927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (786175214/833617601 : ℝ) ^ p + (822820652/833617601 : ℝ) ^ p := by
    exact cert_lt (x := (786175214/833617601 : ℝ)) (y := (822820652/833617601 : ℝ)) (X := (6484128681549/25000000000000 : ℝ)) (Y := (18515871573223/25000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922909731/1000000000 : ℝ)) (n' := (833617601/1000000000 : ℝ)) (Ab := (393087607/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (184581951/200000000 : ℝ) ^ p + (496290461/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184581951/200000000 : ℝ)) (y := (496290461/500000000 : ℝ)) (X := (1970079160417/12500000000000 : ℝ)) (Y := (84239382865159/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496290461/500000000 : ℝ) ^ p + (184581951/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496290461/500000000 : ℝ)) (y := (184581951/200000000 : ℝ)) (X := (84239382865159/100000000000000 : ℝ)) (Y := (1970079160417/12500000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1915490677/1000000000 : ℝ)) (τ := (184581951/200000000 : ℝ)) (σ := (496290461/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (78617524/83361763 : ℝ) ^ p + (822820681/833617630 : ℝ) ^ p := by
    exact cert_lt (x := (78617524/83361763 : ℝ)) (y := (822820681/833617630 : ℝ)) (X := (25936513700769/100000000000000 : ℝ)) (Y := (74063487071553/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (184581951/200000000 : ℝ)) (n' := (83361763/100000000 : ℝ)) (Ab := (19654381/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (230727439/250000000 : ℝ) ^ p + (496290461/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (230727439/250000000 : ℝ)) (y := (496290461/500000000 : ℝ)) (X := (15760633676643/100000000000000 : ℝ)) (Y := (84239382865159/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496290461/500000000 : ℝ) ^ p + (230727439/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496290461/500000000 : ℝ)) (y := (230727439/250000000 : ℝ)) (X := (84239382865159/100000000000000 : ℝ)) (Y := (15760633676643/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (957745339/500000000 : ℝ)) (τ := (230727439/250000000 : ℝ)) (σ := (496290461/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (786175241/833617631 : ℝ) ^ p + (822820682/833617631 : ℝ) ^ p := by
    exact cert_lt (x := (786175241/833617631 : ℝ)) (y := (822820682/833617631 : ℝ)) (X := (6484128436003/25000000000000 : ℝ)) (Y := (74063487098403/100000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (230727439/250000000 : ℝ)) (n' := (833617631/1000000000 : ℝ)) (Ab := (786175241/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (957745339/500000000 : ℝ)) (τ := (230727439/250000000 : ℝ)) (σ := (496290461/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (230727439/250000000 : ℝ)) (n' := (833617631/1000000000 : ℝ)) (Ab := (786175241/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (957745339/500000000 : ℝ)) (τ := (230727439/250000000 : ℝ)) (σ := (496290461/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (230727439/250000000 : ℝ)) (n' := (833617631/1000000000 : ℝ)) (Ab := (786175241/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (957745339/500000000 : ℝ)) (τ := (230727439/250000000 : ℝ)) (σ := (496290461/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (230727439/250000000 : ℝ)) (n' := (833617631/1000000000 : ℝ)) (Ab := (786175241/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (957745339/500000000 : ℝ)) (τ := (230727439/250000000 : ℝ)) (σ := (496290461/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1653051840/1806813409 : ℝ) ^ p + (1796016460/1806813409 : ℝ) ^ p := by
    exact cert_lt (x := (1653051840/1806813409 : ℝ)) (y := (1796016460/1806813409 : ℝ)) (X := (1289364724727/10000000000000 : ℝ)) (Y := (43553176503783/50000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109895611/1193186591 : ℝ) ^ p + (1182389642/1193186591 : ℝ) ^ p := by
    exact cert_lt (x := (1109895611/1193186591 : ℝ)) (y := (1182389642/1193186591 : ℝ)) (X := (472231166421/2500000000000 : ℝ)) (Y := (16222150800509/20000000000000 : ℝ)) 737 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496290461/500000000 : ℝ)) (U := (1193186591/1000000000 : ℝ)) (Ab := (5165787/3125000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (230727439/250000000 : ℝ)) (σ := (496290461/500000000 : ℝ)) (Ab := (1109895611/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab064
