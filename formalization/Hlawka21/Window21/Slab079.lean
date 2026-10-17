import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 79, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab079 (p : ℝ) (hpa : (751/32 : ℝ) ≤ p) (hpb : p ≤ (47/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1049822831431/51255750000000 : ℝ) (2637001/250000000 : ℝ) (4000000615069/20502300000000 : ℝ) (3033/2500 : ℝ) (485467563/250000000 : ℝ) (30340531/31250000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193376881/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2779/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(4571/10000 : ℝ)
      else (7721/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1049822831431/51255750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2637001/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (28708143/31250000 : ℝ) ^ p + (124223687/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (28708143/31250000 : ℝ)) (y := (124223687/125000000 : ℝ)) (X := (3404743264151/25000000000000 : ℝ)) (Y := (21595261031899/25000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124223687/125000000 : ℝ) ^ p + (28708143/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (124223687/125000000 : ℝ)) (y := (28708143/31250000 : ℝ)) (X := (21595261031899/25000000000000 : ℝ)) (Y := (3404743264151/25000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (239056259/125000000 : ℝ)) (τ := (28708143/31250000 : ℝ)) (σ := (124223687/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782009523/828131786 : ℝ) ^ p + (408791891/414065893 : ℝ) ^ p := by
    exact cert_lt (x := (782009523/828131786 : ℝ)) (y := (408791891/414065893 : ℝ)) (X := (13005163228617/50000000000000 : ℝ)) (Y := (36994837497497/50000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (28708143/31250000 : ℝ)) (n' := (414065893/500000000 : ℝ)) (Ab := (782009523/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (11553987/12500000 : ℝ) ^ p + (198548437/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (11553987/12500000 : ℝ)) (y := (198548437/200000000 : ℝ)) (X := (15733079834947/100000000000000 : ℝ)) (Y := (21066734230477/25000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198548437/200000000 : ℝ) ^ p + (11553987/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (198548437/200000000 : ℝ)) (y := (11553987/12500000 : ℝ)) (X := (21066734230477/25000000000000 : ℝ)) (Y := (15733079834947/100000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (383412229/200000000 : ℝ)) (τ := (11553987/12500000 : ℝ)) (σ := (198548437/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (262701493/278277756 : ℝ) ^ p + (206071316/208708317 : ℝ) ^ p := by
    exact cert_lt (x := (262701493/278277756 : ℝ)) (y := (206071316/208708317 : ℝ)) (X := (12915021746117/50000000000000 : ℝ)) (Y := (9271244718603/12500000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (11553987/12500000 : ℝ)) (n' := (208708317/250000000 : ℝ)) (Ab := (788104479/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (5778547/6250000 : ℝ) ^ p + (992692163/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (5778547/6250000 : ℝ)) (y := (992692163/1000000000 : ℝ)) (X := (7916402571119/50000000000000 : ℝ)) (Y := (21041803012957/25000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992692163/1000000000 : ℝ) ^ p + (5778547/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (992692163/1000000000 : ℝ)) (y := (5778547/6250000 : ℝ)) (X := (21041803012957/25000000000000 : ℝ)) (Y := (7916402571119/50000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1917259683/1000000000 : ℝ)) (τ := (5778547/6250000 : ℝ)) (σ := (992692163/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (788371330/835126727 : ℝ) ^ p + (824578723/835126727 : ℝ) ^ p := by
    exact cert_lt (x := (788371330/835126727 : ℝ)) (y := (824578723/835126727 : ℝ)) (X := (25822205119223/100000000000000 : ℝ)) (Y := (74177795756133/100000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (5778547/6250000 : ℝ)) (n' := (835126727/1000000000 : ℝ)) (Ab := (78837133/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (36983133/40000000 : ℝ) ^ p + (49634499/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (36983133/40000000 : ℝ)) (y := (49634499/50000000 : ℝ)) (X := (989822121097/6250000000000 : ℝ)) (Y := (42081431276579/50000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49634499/50000000 : ℝ) ^ p + (36983133/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (49634499/50000000 : ℝ)) (y := (36983133/40000000 : ℝ)) (X := (42081431276579/50000000000000 : ℝ)) (Y := (989822121097/6250000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (383453661/200000000 : ℝ)) (τ := (36983133/40000000 : ℝ)) (σ := (49634499/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (788382929/835139482 : ℝ) ^ p + (412295739/417569741 : ℝ) ^ p := by
    exact cert_lt (x := (788382929/835139482 : ℝ)) (y := (412295739/417569741 : ℝ)) (X := (5164372998037/20000000000000 : ℝ)) (Y := (18544534080741/25000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (36983133/40000000 : ℝ)) (n' := (417569741/500000000 : ℝ)) (Ab := (788382929/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (462289397/500000000 : ℝ) ^ p + (198537977/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (462289397/500000000 : ℝ)) (y := (198537977/200000000 : ℝ)) (X := (395933568163/2500000000000 : ℝ)) (Y := (84162673276151/100000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198537977/200000000 : ℝ) ^ p + (462289397/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198537977/200000000 : ℝ)) (y := (462289397/500000000 : ℝ)) (X := (84162673276151/100000000000000 : ℝ)) (Y := (395933568163/2500000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1917268679/1000000000 : ℝ)) (τ := (462289397/500000000 : ℝ)) (σ := (198537977/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (788383433/835140036 : ℝ) ^ p + (206148008/208785009 : ℝ) ^ p := by
    exact cert_lt (x := (788383433/835140036 : ℝ)) (y := (206148008/208785009 : ℝ)) (X := (6455462594683/25000000000000 : ℝ)) (Y := (2967126044597/4000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (462289397/500000000 : ℝ)) (n' := (208785009/250000000 : ℝ)) (Ab := (788383433/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (462289407/500000000 : ℝ) ^ p + (992689881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462289407/500000000 : ℝ)) (y := (992689881/1000000000 : ℝ)) (X := (1583735077727/10000000000000 : ℝ)) (Y := (42081332653301/50000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992689881/1000000000 : ℝ) ^ p + (462289407/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992689881/1000000000 : ℝ)) (y := (462289407/500000000 : ℝ)) (X := (42081332653301/50000000000000 : ℝ)) (Y := (1583735077727/10000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383453739/200000000 : ℝ)) (τ := (462289407/500000000 : ℝ)) (σ := (992689881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (60644881/64241543 : ℝ) ^ p + (824592055/835140059 : ℝ) ^ p := by
    exact cert_lt (x := (60644881/64241543 : ℝ)) (y := (824592055/835140059 : ℝ)) (X := (25821849060779/100000000000000 : ℝ)) (Y := (74178151729031/100000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (462289407/500000000 : ℝ)) (n' := (835140059/1000000000 : ℝ)) (Ab := (788383453/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (184915763/200000000 : ℝ) ^ p + (992689881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184915763/200000000 : ℝ)) (y := (992689881/1000000000 : ℝ)) (X := (494917224369/3125000000000 : ℝ)) (Y := (42081332653301/50000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992689881/1000000000 : ℝ) ^ p + (184915763/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992689881/1000000000 : ℝ)) (y := (184915763/200000000 : ℝ)) (X := (42081332653301/50000000000000 : ℝ)) (Y := (494917224369/3125000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (239658587/125000000 : ℝ)) (τ := (184915763/200000000 : ℝ)) (σ := (992689881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (20746933/21977370 : ℝ) ^ p + (206148014/208785015 : ℝ) ^ p := by
    exact cert_lt (x := (20746933/21977370 : ℝ)) (y := (206148014/208785015 : ℝ)) (X := (25821849103871/100000000000000 : ℝ)) (Y := (74178151755731/100000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (184915763/200000000 : ℝ)) (n' := (41757003/50000000 : ℝ)) (Ab := (394191727/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (239658587/125000000 : ℝ)) (τ := (184915763/200000000 : ℝ)) (σ := (992689881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (184915763/200000000 : ℝ)) (n' := (41757003/50000000 : ℝ)) (Ab := (394191727/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (239658587/125000000 : ℝ)) (τ := (184915763/200000000 : ℝ)) (σ := (992689881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (184915763/200000000 : ℝ)) (n' := (41757003/50000000 : ℝ)) (Ab := (394191727/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (239658587/125000000 : ℝ)) (τ := (184915763/200000000 : ℝ)) (σ := (992689881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (184915763/200000000 : ℝ)) (n' := (41757003/50000000 : ℝ)) (Ab := (394191727/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (239658587/125000000 : ℝ)) (τ := (184915763/200000000 : ℝ)) (σ := (992689881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1655606243/1806623119 : ℝ) ^ p + (1796075115/1806623119 : ℝ) ^ p := by
    exact cert_lt (x := (1655606243/1806623119 : ℝ)) (y := (1796075115/1806623119 : ℝ)) (X := (6427958485071/50000000000000 : ℝ)) (Y := (43572041631957/50000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1111529564/1193376881 : ℝ) ^ p + (1182828877/1193376881 : ℝ) ^ p := by
    exact cert_lt (x := (1111529564/1193376881 : ℝ)) (y := (1182828877/1193376881 : ℝ)) (X := (1883084719283/10000000000000 : ℝ)) (Y := (40584576615753/50000000000000 : ℝ)) 47 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992689881/1000000000 : ℝ)) (U := (1193376881/1000000000 : ℝ)) (Ab := (1655606243/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (184915763/200000000 : ℝ)) (σ := (992689881/1000000000 : ℝ)) (Ab := (277882391/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab079
