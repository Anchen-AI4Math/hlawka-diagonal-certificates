import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 45, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab045 (p : ℝ) (hpa : (717/32 : ℝ) ≤ p) (hpb : p ≤ (359/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2112113389133/97870500000000 : ℝ) (11129369/1000000000 : ℝ) (4000000587223/19574100000000 : ℝ) (3033/2500 : ℝ) (48478997/25000000 : ℝ) (193907633/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298236801/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5539/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(901/2000 : ℝ)
      else (957/1250 : ℝ) ≤ X j i ∧ X j i ≤ (148/125 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2112113389133/97870500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11129369/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (18291947/20000000 : ℝ) ^ p + (993561079/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18291947/20000000 : ℝ)) (y := (993561079/1000000000 : ℝ)) (X := (13492634301171/100000000000000 : ℝ)) (Y := (1730147661393/2000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993561079/1000000000 : ℝ) ^ p + (18291947/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (993561079/1000000000 : ℝ)) (y := (18291947/20000000 : ℝ)) (X := (1730147661393/2000000000000 : ℝ)) (Y := (13492634301171/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908158429/1000000000 : ℝ)) (τ := (18291947/20000000 : ℝ)) (σ := (993561079/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (776669216/824321929 : ℝ) ^ p + (813192560/824321929 : ℝ) ^ p := by
    exact cert_lt (x := (776669216/824321929 : ℝ)) (y := (813192560/824321929 : ℝ)) (X := (13143746332671/50000000000000 : ℝ)) (Y := (73712508274413/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (18291947/20000000 : ℝ)) (n' := (824321929/1000000000 : ℝ)) (Ab := (24270913/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (184080123/200000000 : ℝ) ^ p + (992495779/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184080123/200000000 : ℝ)) (y := (992495779/1000000000 : ℝ)) (X := (15550046710727/100000000000000 : ℝ)) (Y := (16889993925421/20000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992495779/1000000000 : ℝ) ^ p + (184080123/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992495779/1000000000 : ℝ)) (y := (184080123/200000000 : ℝ)) (X := (16889993925421/20000000000000 : ℝ)) (Y := (15550046710727/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956448197/500000000 : ℝ)) (τ := (184080123/200000000 : ℝ)) (σ := (992495779/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (391465993/415617756 : ℝ) ^ p + (820106143/831235512 : ℝ) ^ p := by
    exact cert_lt (x := (391465993/415617756 : ℝ)) (y := (820106143/831235512 : ℝ)) (X := (26098996999383/100000000000000 : ℝ)) (Y := (1478020083151/2000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (184080123/200000000 : ℝ)) (n' := (103904439/125000000 : ℝ)) (Ab := (391465993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (11508407/12500000 : ℝ) ^ p + (992441579/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (11508407/12500000 : ℝ)) (y := (992441579/1000000000 : ℝ)) (X := (3130692475847/20000000000000 : ℝ)) (Y := (84346552995513/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992441579/1000000000 : ℝ) ^ p + (11508407/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (992441579/1000000000 : ℝ)) (y := (11508407/12500000 : ℝ)) (X := (84346552995513/100000000000000 : ℝ)) (Y := (3130692475847/20000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1913114139/1000000000 : ℝ)) (τ := (11508407/12500000 : ℝ)) (σ := (992441579/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (783224459/831558441 : ℝ) ^ p + (820429072/831558441 : ℝ) ^ p := by
    exact cert_lt (x := (783224459/831558441 : ℝ)) (y := (820429072/831558441 : ℝ)) (X := (26090257903303/100000000000000 : ℝ)) (Y := (36954871602391/50000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (11508407/12500000 : ℝ)) (n' := (831558441/1000000000 : ℝ)) (Ab := (783224459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (920685163/1000000000 : ℝ) ^ p + (496219529/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (920685163/1000000000 : ℝ)) (y := (496219529/500000000 : ℝ)) (X := (7829135482359/50000000000000 : ℝ)) (Y := (84341745732601/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496219529/500000000 : ℝ) ^ p + (920685163/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496219529/500000000 : ℝ)) (y := (920685163/1000000000 : ℝ)) (X := (84341745732601/100000000000000 : ℝ)) (Y := (7829135482359/50000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1913124221/1000000000 : ℝ)) (τ := (920685163/1000000000 : ℝ)) (σ := (496219529/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (783238012/831573405 : ℝ) ^ p + (820444036/831573405 : ℝ) ^ p := by
    exact cert_lt (x := (783238012/831573405 : ℝ)) (y := (820444036/831573405 : ℝ)) (X := (13044926695151/50000000000000 : ℝ)) (Y := (9238768502159/12500000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (920685163/1000000000 : ℝ)) (n' := (166314681/200000000 : ℝ)) (Ab := (195809503/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (920685747/1000000000 : ℝ) ^ p + (992438941/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920685747/1000000000 : ℝ)) (y := (992438941/1000000000 : ℝ)) (X := (3914623454999/25000000000000 : ℝ)) (Y := (42170761316571/50000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992438941/1000000000 : ℝ) ^ p + (920685747/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992438941/1000000000 : ℝ)) (y := (920685747/1000000000 : ℝ)) (X := (42170761316571/50000000000000 : ℝ)) (Y := (3914623454999/25000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (119570293/62500000 : ℝ)) (τ := (920685747/1000000000 : ℝ)) (σ := (992438941/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (783238639/831574098 : ℝ) ^ p + (820444729/831574098 : ℝ) ^ p := by
    exact cert_lt (x := (783238639/831574098 : ℝ)) (y := (820444729/831574098 : ℝ)) (X := (5217966833563/20000000000000 : ℝ)) (Y := (73910166764301/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (920685747/1000000000 : ℝ)) (n' := (415787049/500000000 : ℝ)) (Ab := (783238639/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (36827431/40000000 : ℝ) ^ p + (198487787/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (36827431/40000000 : ℝ)) (y := (198487787/200000000 : ℝ)) (X := (3131700900983/20000000000000 : ℝ)) (Y := (84341511192159/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198487787/200000000 : ℝ) ^ p + (36827431/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (198487787/200000000 : ℝ)) (y := (36827431/40000000 : ℝ)) (X := (84341511192159/100000000000000 : ℝ)) (Y := (3131700900983/20000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (191312471/100000000 : ℝ)) (τ := (36827431/40000000 : ℝ)) (σ := (198487787/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (783238669/831574131 : ℝ) ^ p + (820444762/831574131 : ℝ) ^ p := by
    exact cert_lt (x := (783238669/831574131 : ℝ)) (y := (820444762/831574131 : ℝ)) (X := (26089833359231/100000000000000 : ℝ)) (Y := (9238770957127/12500000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (36827431/40000000 : ℝ)) (n' := (831574131/1000000000 : ℝ)) (Ab := (783238669/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (57542861/62500000 : ℝ) ^ p + (198487787/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (57542861/62500000 : ℝ)) (y := (198487787/200000000 : ℝ)) (X := (15658504886519/100000000000000 : ℝ)) (Y := (84341511192159/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198487787/200000000 : ℝ) ^ p + (57542861/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (198487787/200000000 : ℝ)) (y := (57542861/62500000 : ℝ)) (X := (84341511192159/100000000000000 : ℝ)) (Y := (15658504886519/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1913124711/1000000000 : ℝ)) (τ := (57542861/62500000 : ℝ)) (σ := (198487787/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (391619335/415787066 : ℝ) ^ p + (820444763/831574132 : ℝ) ^ p := by
    exact cert_lt (x := (391619335/415787066 : ℝ)) (y := (820444763/831574132 : ℝ)) (X := (26089833402673/100000000000000 : ℝ)) (Y := (18477541921017/25000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (57542861/62500000 : ℝ)) (n' := (207893533/250000000 : ℝ)) (Ab := (78323867/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1913124711/1000000000 : ℝ)) (τ := (57542861/62500000 : ℝ)) (σ := (198487787/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (57542861/62500000 : ℝ)) (n' := (207893533/250000000 : ℝ)) (Ab := (78323867/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1913124711/1000000000 : ℝ)) (τ := (57542861/62500000 : ℝ)) (σ := (198487787/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (57542861/62500000 : ℝ)) (n' := (207893533/250000000 : ℝ)) (Ab := (78323867/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1913124711/1000000000 : ℝ)) (τ := (57542861/62500000 : ℝ)) (σ := (198487787/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (57542861/62500000 : ℝ)) (n' := (207893533/250000000 : ℝ)) (Ab := (78323867/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1913124711/1000000000 : ℝ)) (τ := (57542861/62500000 : ℝ)) (σ := (198487787/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (45824161/50195911 : ℝ) ^ p + (1795923427/1807052796 : ℝ) ^ p := by
    exact cert_lt (x := (45824161/50195911 : ℝ)) (y := (1795923427/1807052796 : ℝ)) (X := (12943819515961/100000000000000 : ℝ)) (Y := (21764045207647/25000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (553875931/596473602 : ℝ) ^ p + (1181817835/1192947204 : ℝ) ^ p := by
    exact cert_lt (x := (553875931/596473602 : ℝ)) (y := (1181817835/1192947204 : ℝ)) (X := (9483303277591/50000000000000 : ℝ)) (Y := (81033394047637/100000000000000 : ℝ)) 359 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198487787/200000000 : ℝ)) (U := (298236801/250000000 : ℝ)) (Ab := (412417449/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (57542861/62500000 : ℝ)) (σ := (198487787/200000000 : ℝ)) (Ab := (553875931/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab045
