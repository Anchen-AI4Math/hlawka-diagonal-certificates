import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 49, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab049 (p : ℝ) (hpa : (721/32 : ℝ) ≤ p) (hpb : p ≤ (361/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1055292983209/49208250000000 : ℝ) (11057723/1000000000 : ℝ) (4000000590499/19683300000000 : ℝ) (3033/2500 : ℝ) (969745897/500000000 : ℝ) (7575817/7812500 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298249347/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11083/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4513/10000 : ℝ)
      else (479/625 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1055292983209/49208250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11057723/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (915096247/1000000000 : ℝ) ^ p + (496794383/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915096247/1000000000 : ℝ)) (y := (496794383/500000000 : ℝ)) (X := (6754047299463/50000000000000 : ℝ)) (Y := (86491922124141/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496794383/500000000 : ℝ) ^ p + (915096247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496794383/500000000 : ℝ)) (y := (915096247/1000000000 : ℝ)) (X := (86491922124141/100000000000000 : ℝ)) (Y := (6754047299463/50000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908685013/1000000000 : ℝ)) (τ := (915096247/1000000000 : ℝ)) (σ := (496794383/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (777324101/824792432 : ℝ) ^ p + (813734709/824792432 : ℝ) ^ p := by
    exact cert_lt (x := (777324101/824792432 : ℝ)) (y := (813734709/824792432 : ℝ)) (X := (13126655222309/50000000000000 : ℝ)) (Y := (36873345417397/50000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915096247/1000000000 : ℝ)) (n' := (51549527/62500000 : ℝ)) (Ab := (777324101/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (920882643/1000000000 : ℝ) ^ p + (248131371/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (920882643/1000000000 : ℝ)) (y := (248131371/250000000 : ℝ)) (X := (622901282539/4000000000000 : ℝ)) (Y := (16885496913743/20000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248131371/250000000 : ℝ) ^ p + (920882643/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248131371/250000000 : ℝ)) (y := (920882643/1000000000 : ℝ)) (X := (16885496913743/20000000000000 : ℝ)) (Y := (622901282539/4000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1913408127/1000000000 : ℝ)) (τ := (920882643/1000000000 : ℝ)) (σ := (248131371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (783567201/831680944 : ℝ) ^ p + (820623221/831680944 : ℝ) ^ p := by
    exact cert_lt (x := (783567201/831680944 : ℝ)) (y := (820623221/831680944 : ℝ)) (X := (26065806889181/100000000000000 : ℝ)) (Y := (14786838779923/20000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (920882643/1000000000 : ℝ)) (n' := (51980059/62500000 : ℝ)) (Ab := (783567201/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (460575843/500000000 : ℝ) ^ p + (496235899/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460575843/500000000 : ℝ)) (y := (496235899/500000000 : ℝ)) (X := (15675507205421/100000000000000 : ℝ)) (Y := (21081127071741/25000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496235899/500000000 : ℝ) ^ p + (460575843/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496235899/500000000 : ℝ)) (y := (460575843/500000000 : ℝ)) (X := (21081127071741/25000000000000 : ℝ)) (Y := (15675507205421/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478405871/250000000 : ℝ)) (τ := (460575843/500000000 : ℝ)) (σ := (496235899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (783856489/832000200 : ℝ) ^ p + (820942477/832000200 : ℝ) ^ p := by
    exact cert_lt (x := (783856489/832000200 : ℝ)) (y := (820942477/832000200 : ℝ)) (X := (162857382491/625000000000 : ℝ)) (Y := (73942819598897/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (460575843/500000000 : ℝ)) (n' := (4160001/5000000 : ℝ)) (Ab := (783856489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (460582029/500000000 : ℝ) ^ p + (24811733/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (460582029/500000000 : ℝ)) (y := (24811733/25000000 : ℝ)) (X := (15680258155529/100000000000000 : ℝ)) (Y := (84319758080641/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (24811733/25000000 : ℝ) ^ p + (460582029/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (24811733/25000000 : ℝ)) (y := (460582029/500000000 : ℝ)) (X := (84319758080641/100000000000000 : ℝ)) (Y := (15680258155529/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (956816689/500000000 : ℝ)) (τ := (460582029/500000000 : ℝ)) (σ := (24811733/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261289930/277338293 : ℝ) ^ p + (820957156/832014879 : ℝ) ^ p := by
    exact cert_lt (x := (261289930/277338293 : ℝ)) (y := (820957156/832014879 : ℝ)) (X := (26056784743581/100000000000000 : ℝ)) (Y := (73943216061927/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (460582029/500000000 : ℝ)) (n' := (832014879/1000000000 : ℝ)) (Ab := (78386979/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921164627/1000000000 : ℝ) ^ p + (496234603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (921164627/1000000000 : ℝ)) (y := (496234603/500000000 : ℝ)) (X := (15680476689321/100000000000000 : ℝ)) (Y := (843195395543/1000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496234603/500000000 : ℝ) ^ p + (921164627/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496234603/500000000 : ℝ)) (y := (921164627/1000000000 : ℝ)) (X := (843195395543/1000000000000 : ℝ)) (Y := (15680476689321/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1913633833/1000000000 : ℝ)) (τ := (921164627/1000000000 : ℝ)) (σ := (496234603/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (130645067/138669259 : ℝ) ^ p + (820957831/832015554 : ℝ) ^ p := by
    exact cert_lt (x := (130645067/138669259 : ℝ)) (y := (820957831/832015554 : ℝ)) (X := (26056766787973/100000000000000 : ℝ)) (Y := (73943234292619/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921164627/1000000000 : ℝ)) (n' := (416007777/500000000 : ℝ)) (Ab := (391935201/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (921164653/1000000000 : ℝ) ^ p + (992469201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921164653/1000000000 : ℝ)) (y := (992469201/1000000000 : ℝ)) (X := (15680486675117/100000000000000 : ℝ)) (Y := (84319529969823/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992469201/1000000000 : ℝ) ^ p + (921164653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992469201/1000000000 : ℝ)) (y := (921164653/1000000000 : ℝ)) (X := (84319529969823/100000000000000 : ℝ)) (Y := (15680486675117/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (956816927/500000000 : ℝ)) (τ := (921164653/1000000000 : ℝ)) (σ := (992469201/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (261290143/277338528 : ℝ) ^ p + (820957861/832015584 : ℝ) ^ p := by
    exact cert_lt (x := (261290143/277338528 : ℝ)) (y := (820957861/832015584 : ℝ)) (X := (13028382919973/50000000000000 : ℝ)) (Y := (73943235102871/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (921164653/1000000000 : ℝ)) (n' := (26000487/31250000 : ℝ)) (Ab := (783870429/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (184232931/200000000 : ℝ) ^ p + (2481173/2500000 : ℝ) ^ p := by
    exact cert_lt (x := (184232931/200000000 : ℝ)) (y := (2481173/2500000 : ℝ)) (X := (1960060930407/12500000000000 : ℝ)) (Y := (1317492625827/1562500000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (2481173/2500000 : ℝ) ^ p + (184232931/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (2481173/2500000 : ℝ)) (y := (184232931/200000000 : ℝ)) (X := (1317492625827/1562500000000 : ℝ)) (Y := (1960060930407/12500000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (261290144/277338529 : ℝ) ^ p + (820957864/832015587 : ℝ) ^ p := by
    exact cert_lt (x := (261290144/277338529 : ℝ)) (y := (820957864/832015587 : ℝ)) (X := (5211353194029/20000000000000 : ℝ)) (Y := (73943235183897/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (n' := (832015587/1000000000 : ℝ)) (Ab := (24495951/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (382726771/200000000 : ℝ)) (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (275065991/301167102 : ℝ) ^ p + (1795944889/1807002612 : ℝ) ^ p := by
    exact cert_lt (x := (275065991/301167102 : ℝ)) (y := (1795944889/1807002612 : ℝ)) (X := (12933024848981/100000000000000 : ℝ)) (Y := (87066975462059/100000000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108210253/1192997388 : ℝ) ^ p + (1181939665/1192997388 : ℝ) ^ p := by
    exact cert_lt (x := (1108210253/1192997388 : ℝ)) (y := (1181939665/1192997388 : ℝ)) (X := (18949991341573/100000000000000 : ℝ)) (Y := (10131251155043/12500000000000 : ℝ)) 361 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (2481173/2500000 : ℝ)) (U := (298249347/250000000 : ℝ)) (Ab := (825197973/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (184232931/200000000 : ℝ)) (σ := (2481173/2500000 : ℝ)) (Ab := (1108210253/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab049
