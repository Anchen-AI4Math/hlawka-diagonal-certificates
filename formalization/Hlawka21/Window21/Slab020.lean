import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 20, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab020 (p : ℝ) (hpa : (173/8 : ℝ) ≤ p) (hpb : p ≤ (693/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (530513480957/23614500000000 : ℝ) (11598669/1000000000 : ℝ) (1000000141687/4722900000000 : ℝ) (3033/2500 : ℝ) (1937/1000 : ℝ) (193691041/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238527441/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1381/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(4451/10000 : ℝ)
      else (7603/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5917/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (530513480957/23614500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11598669/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (227835481/250000000 : ℝ) ^ p + (496691419/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (227835481/250000000 : ℝ)) (y := (496691419/500000000 : ℝ)) (X := (6696058303291/50000000000000 : ℝ)) (Y := (43303950202223/50000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496691419/500000000 : ℝ) ^ p + (227835481/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496691419/500000000 : ℝ)) (y := (227835481/250000000 : ℝ)) (X := (43303950202223/50000000000000 : ℝ)) (Y := (6696058303291/50000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (952362381/500000000 : ℝ)) (τ := (227835481/250000000 : ℝ)) (σ := (496691419/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (772401343/821233204 : ℝ) ^ p + (809634535/821233204 : ℝ) ^ p := by
    exact cert_lt (x := (772401343/821233204 : ℝ)) (y := (809634535/821233204 : ℝ)) (X := (2651155843351/10000000000000 : ℝ)) (Y := (36744221232369/50000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (227835481/250000000 : ℝ)) (n' := (205308301/250000000 : ℝ)) (Ab := (772401343/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (458624403/500000000 : ℝ) ^ p + (992305693/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458624403/500000000 : ℝ)) (y := (992305693/1000000000 : ℝ)) (X := (15403253135001/100000000000000 : ℝ)) (Y := (21149190509053/25000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992305693/1000000000 : ℝ) ^ p + (458624403/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992305693/1000000000 : ℝ)) (y := (458624403/500000000 : ℝ)) (X := (21149190509053/25000000000000 : ℝ)) (Y := (15403253135001/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1909554499/1000000000 : ℝ)) (τ := (458624403/500000000 : ℝ)) (σ := (992305693/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (778785867/828303470 : ℝ) ^ p + (816704801/828303470 : ℝ) ^ p := by
    exact cert_lt (x := (778785867/828303470 : ℝ)) (y := (816704801/828303470 : ℝ)) (X := (13158350719249/50000000000000 : ℝ)) (Y := (9210412448579/12500000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (458624403/500000000 : ℝ)) (n' := (82830347/100000000 : ℝ)) (Ab := (778785867/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (917539867/1000000000 : ℝ) ^ p + (496124069/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (917539867/1000000000 : ℝ)) (y := (496124069/500000000 : ℝ)) (X := (15509451179037/100000000000000 : ℝ)) (Y := (84490564502391/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496124069/500000000 : ℝ) ^ p + (917539867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496124069/500000000 : ℝ)) (y := (917539867/1000000000 : ℝ)) (X := (84490564502391/100000000000000 : ℝ)) (Y := (15509451179037/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (381957601/200000000 : ℝ)) (τ := (917539867/1000000000 : ℝ)) (σ := (496124069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (779099361/828650707 : ℝ) ^ p + (817052038/828650707 : ℝ) ^ p := by
    exact cert_lt (x := (779099361/828650707 : ℝ)) (y := (817052038/828650707 : ℝ)) (X := (6576801227657/25000000000000 : ℝ)) (Y := (73692796372449/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (917539867/1000000000 : ℝ)) (n' := (828650707/1000000000 : ℝ)) (Ab := (779099361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (7168391/7812500 : ℝ) ^ p + (496122661/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (7168391/7812500 : ℝ)) (y := (496122661/500000000 : ℝ)) (X := (7757321567057/50000000000000 : ℝ)) (Y := (16897074365587/20000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496122661/500000000 : ℝ) ^ p + (7168391/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (496122661/500000000 : ℝ)) (y := (7168391/7812500 : ℝ)) (X := (16897074365587/20000000000000 : ℝ)) (Y := (7757321567057/50000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (190979937/100000000 : ℝ)) (τ := (7168391/7812500 : ℝ)) (σ := (496122661/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (389557316/414333811 : ℝ) ^ p + (817068953/828667622 : ℝ) ^ p := by
    exact cert_lt (x := (389557316/414333811 : ℝ)) (y := (817068953/828667622 : ℝ)) (X := (26306742392217/100000000000000 : ℝ)) (Y := (14738651763399/20000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (7168391/7812500 : ℝ)) (n' := (414333811/500000000 : ℝ)) (Ab := (97389329/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (917554739/1000000000 : ℝ) ^ p + (198449037/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (917554739/1000000000 : ℝ)) (y := (198449037/200000000 : ℝ)) (X := (7757448082873/50000000000000 : ℝ)) (Y := (84485119209137/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198449037/200000000 : ℝ) ^ p + (917554739/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198449037/200000000 : ℝ)) (y := (917554739/1000000000 : ℝ)) (X := (84485119209137/100000000000000 : ℝ)) (Y := (7757448082873/50000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (477449981/250000000 : ℝ)) (τ := (917554739/1000000000 : ℝ)) (σ := (198449037/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (389557688/414334223 : ℝ) ^ p + (817069777/828668446 : ℝ) ^ p := by
    exact cert_lt (x := (389557688/414334223 : ℝ)) (y := (817069777/828668446 : ℝ)) (X := (26306719924643/100000000000000 : ℝ)) (Y := (3684664067209/5000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (917554739/1000000000 : ℝ)) (n' := (414334223/500000000 : ℝ)) (Ab := (48694711/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (917554773/1000000000 : ℝ) ^ p + (496122589/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (917554773/1000000000 : ℝ)) (y := (496122589/500000000 : ℝ)) (X := (15514908616029/100000000000000 : ℝ)) (Y := (84485106301627/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496122589/500000000 : ℝ) ^ p + (917554773/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496122589/500000000 : ℝ)) (y := (917554773/1000000000 : ℝ)) (X := (84485106301627/100000000000000 : ℝ)) (Y := (15514908616029/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1909799951/1000000000 : ℝ)) (τ := (917554773/1000000000 : ℝ)) (σ := (496122589/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (779115413/828668487 : ℝ) ^ p + (272356606/276222829 : ℝ) ^ p := by
    exact cert_lt (x := (779115413/828668487 : ℝ)) (y := (272356606/276222829 : ℝ)) (X := (26306718792521/100000000000000 : ℝ)) (Y := (73693282465071/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (917554773/1000000000 : ℝ)) (n' := (828668487/1000000000 : ℝ)) (Ab := (779115413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (458777387/500000000 : ℝ) ^ p + (496122589/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (458777387/500000000 : ℝ)) (y := (496122589/500000000 : ℝ)) (X := (7757454491107/50000000000000 : ℝ)) (Y := (84485106301627/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496122589/500000000 : ℝ) ^ p + (458777387/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496122589/500000000 : ℝ)) (y := (458777387/500000000 : ℝ)) (X := (84485106301627/100000000000000 : ℝ)) (Y := (7757454491107/50000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (119362497/62500000 : ℝ)) (τ := (458777387/500000000 : ℝ)) (σ := (496122589/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (389557707/414334244 : ℝ) ^ p + (817069819/828668488 : ℝ) ^ p := by
    exact cert_lt (x := (389557707/414334244 : ℝ)) (y := (817069819/828668488 : ℝ)) (X := (26306718836247/100000000000000 : ℝ)) (Y := (7369328249241/10000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (458777387/500000000 : ℝ)) (n' := (103583561/125000000 : ℝ)) (Ab := (389557707/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (119362497/62500000 : ℝ)) (τ := (458777387/500000000 : ℝ)) (σ := (496122589/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (458777387/500000000 : ℝ)) (n' := (103583561/125000000 : ℝ)) (Ab := (389557707/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (119362497/62500000 : ℝ)) (τ := (458777387/500000000 : ℝ)) (σ := (496122589/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (458777387/500000000 : ℝ)) (n' := (103583561/125000000 : ℝ)) (Ab := (389557707/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (119362497/62500000 : ℝ)) (τ := (458777387/500000000 : ℝ)) (σ := (496122589/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (458777387/500000000 : ℝ)) (n' := (103583561/125000000 : ℝ)) (Ab := (389557707/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (119362497/62500000 : ℝ)) (τ := (458777387/500000000 : ℝ)) (σ := (496122589/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (548316683/602454265 : ℝ) ^ p + (598588042/602454265 : ℝ) ^ p := by
    exact cert_lt (x := (548316683/602454265 : ℝ)) (y := (598588042/602454265 : ℝ)) (X := (13014249382451/100000000000000 : ℝ)) (Y := (86985750802893/100000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1104797443/1192637205 : ℝ) ^ p + (131226504/132515245 : ℝ) ^ p := by
    exact cert_lt (x := (1104797443/1192637205 : ℝ)) (y := (131226504/132515245 : ℝ)) (X := (19074628522093/100000000000000 : ℝ)) (Y := (3237014887369/4000000000000 : ℝ)) 693 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496122589/500000000 : ℝ)) (U := (238527441/200000000 : ℝ)) (Ab := (1644950049/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (458777387/500000000 : ℝ)) (σ := (496122589/500000000 : ℝ)) (Ab := (1104797443/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab020
