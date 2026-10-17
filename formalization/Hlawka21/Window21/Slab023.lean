import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 23, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab023 (p : ℝ) (hpa : (695/32 : ℝ) ≤ p) (hpb : p ≤ (87/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (212082355487/9486750000000 : ℝ) (1154031/100000000 : ℝ) (800000113841/3794700000000 : ℝ) (3033/2500 : ℝ) (121079203/62500000 : ℝ) (121073651/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192673997/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2763/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2229/5000 : ℝ)
      else (761/1000 : ℝ) ≤ X j i ∧ X j i ≤ (2367/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (212082355487/9486750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1154031/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (91174557/100000000 : ℝ) ^ p + (99340471/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (91174557/100000000 : ℝ)) (y := (99340471/100000000 : ℝ)) (X := (13404547096577/100000000000000 : ℝ)) (Y := (86595469515627/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99340471/100000000 : ℝ) ^ p + (91174557/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (99340471/100000000 : ℝ)) (y := (91174557/100000000 : ℝ)) (X := (86595469515627/100000000000000 : ℝ)) (Y := (13404547096577/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (47628757/25000000 : ℝ)) (τ := (91174557/100000000 : ℝ)) (σ := (99340471/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (772930019/821617932 : ℝ) ^ p + (135012937/136936322 : ℝ) ^ p := by
    exact cert_lt (x := (772930019/821617932 : ℝ)) (y := (135012937/136936322 : ℝ)) (X := (26483676458061/100000000000000 : ℝ)) (Y := (18379081215643/25000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (91174557/100000000 : ℝ)) (n' := (205404483/250000000 : ℝ)) (Ab := (772930019/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (917640219/1000000000 : ℝ) ^ p + (992328909/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917640219/1000000000 : ℝ)) (y := (992328909/1000000000 : ℝ)) (X := (3855365672233/25000000000000 : ℝ)) (Y := (42289276285599/50000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992328909/1000000000 : ℝ) ^ p + (917640219/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992328909/1000000000 : ℝ)) (y := (917640219/1000000000 : ℝ)) (X := (42289276285599/50000000000000 : ℝ)) (Y := (3855365672233/25000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (238746141/125000000 : ℝ)) (τ := (917640219/1000000000 : ℝ)) (σ := (992328909/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (779300075/828669433 : ℝ) ^ p + (817129123/828669433 : ℝ) ^ p := by
    exact cert_lt (x := (779300075/828669433 : ℝ)) (y := (817129123/828669433 : ℝ)) (X := (13144798254183/50000000000000 : ℝ)) (Y := (73710404713169/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (917640219/1000000000 : ℝ)) (n' := (828669433/1000000000 : ℝ)) (Ab := (31172003/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (917928893/1000000000 : ℝ) ^ p + (99227177/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (917928893/1000000000 : ℝ)) (y := (99227177/100000000 : ℝ)) (X := (7763662105113/50000000000000 : ℝ)) (Y := (84472691307221/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99227177/100000000 : ℝ) ^ p + (917928893/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99227177/100000000 : ℝ)) (y := (917928893/1000000000 : ℝ)) (X := (84472691307221/100000000000000 : ℝ)) (Y := (7763662105113/50000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1910200663/1000000000 : ℝ)) (τ := (917928893/1000000000 : ℝ)) (σ := (99227177/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (194902735/207253406 : ℝ) ^ p + (408736657/414506812 : ℝ) ^ p := by
    exact cert_lt (x := (194902735/207253406 : ℝ)) (y := (408736657/414506812 : ℝ)) (X := (26280195368849/100000000000000 : ℝ)) (Y := (73719805822549/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (917928893/1000000000 : ℝ)) (n' := (103626703/125000000 : ℝ)) (Ab := (38980547/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (114742859/125000000 : ℝ) ^ p + (15504203/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (114742859/125000000 : ℝ)) (y := (15504203/15625000 : ℝ)) (X := (3883117024743/25000000000000 : ℝ)) (Y := (42233773869033/50000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (15504203/15625000 : ℝ) ^ p + (114742859/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (15504203/15625000 : ℝ)) (y := (114742859/125000000 : ℝ)) (X := (42233773869033/50000000000000 : ℝ)) (Y := (3883117024743/25000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (238776483/125000000 : ℝ)) (τ := (114742859/125000000 : ℝ)) (σ := (15504203/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (389812995/414515144 : ℝ) ^ p + (408744989/414515144 : ℝ) ^ p := by
    exact cert_lt (x := (389812995/414515144 : ℝ)) (y := (408744989/414515144 : ℝ)) (X := (13139870054679/50000000000000 : ℝ)) (Y := (73720260807961/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (114742859/125000000 : ℝ)) (n' := (51814393/62500000 : ℝ)) (Ab := (77962599/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (917943549/1000000000 : ℝ) ^ p + (992268857/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917943549/1000000000 : ℝ)) (y := (992268857/1000000000 : ℝ)) (X := (194158965721/1250000000000 : ℝ)) (Y := (16893459557643/20000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992268857/1000000000 : ℝ) ^ p + (917943549/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992268857/1000000000 : ℝ)) (y := (917943549/1000000000 : ℝ)) (X := (16893459557643/20000000000000 : ℝ)) (Y := (194158965721/1250000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (955106203/500000000 : ℝ)) (τ := (917943549/1000000000 : ℝ)) (σ := (992268857/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (779626719/829031095 : ℝ) ^ p + (163498157/165806219 : ℝ) ^ p := by
    exact cert_lt (x := (779626719/829031095 : ℝ)) (y := (163498157/165806219 : ℝ)) (X := (42047549091/160000000000 : ℝ)) (Y := (18430070710371/25000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (917943549/1000000000 : ℝ)) (n' := (165806219/200000000 : ℝ)) (Ab := (779626719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (917943581/1000000000 : ℝ) ^ p + (992268851/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917943581/1000000000 : ℝ)) (y := (992268851/1000000000 : ℝ)) (X := (485397782339/3125000000000 : ℝ)) (Y := (84467286679349/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992268851/1000000000 : ℝ) ^ p + (917943581/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992268851/1000000000 : ℝ)) (y := (917943581/1000000000 : ℝ)) (X := (84467286679349/100000000000000 : ℝ)) (Y := (485397782339/3125000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (119388277/62500000 : ℝ)) (τ := (917943581/1000000000 : ℝ)) (σ := (992268851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (389813377/414515567 : ℝ) ^ p + (408745412/414515567 : ℝ) ^ p := by
    exact cert_lt (x := (389813377/414515567 : ℝ)) (y := (408745412/414515567 : ℝ)) (X := (5255943390641/20000000000000 : ℝ)) (Y := (737202839063/1000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (917943581/1000000000 : ℝ)) (n' := (414515567/500000000 : ℝ)) (Ab := (389813377/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (458971791/500000000 : ℝ) ^ p + (992268851/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458971791/500000000 : ℝ)) (y := (992268851/1000000000 : ℝ)) (X := (3883182350721/25000000000000 : ℝ)) (Y := (84467286679349/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992268851/1000000000 : ℝ) ^ p + (458971791/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992268851/1000000000 : ℝ)) (y := (458971791/500000000 : ℝ)) (X := (84467286679349/100000000000000 : ℝ)) (Y := (3883182350721/25000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1910212433/1000000000 : ℝ)) (τ := (458971791/500000000 : ℝ)) (σ := (992268851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (155925351/165806227 : ℝ) ^ p + (163498165/165806227 : ℝ) ^ p := by
    exact cert_lt (x := (155925351/165806227 : ℝ)) (y := (163498165/165806227 : ℝ)) (X := (821241156153/3125000000000 : ℝ)) (Y := (73720283933603/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (458971791/500000000 : ℝ)) (n' := (165806227/200000000 : ℝ)) (Ab := (155925351/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1910212433/1000000000 : ℝ)) (τ := (458971791/500000000 : ℝ)) (σ := (992268851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (458971791/500000000 : ℝ)) (n' := (165806227/200000000 : ℝ)) (Ab := (155925351/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1910212433/1000000000 : ℝ)) (τ := (458971791/500000000 : ℝ)) (σ := (992268851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (458971791/500000000 : ℝ)) (n' := (165806227/200000000 : ℝ)) (Ab := (155925351/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1910212433/1000000000 : ℝ)) (τ := (458971791/500000000 : ℝ)) (σ := (992268851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (458971791/500000000 : ℝ)) (n' := (165806227/200000000 : ℝ)) (Ab := (155925351/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1910212433/1000000000 : ℝ)) (τ := (458971791/500000000 : ℝ)) (σ := (992268851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (548511169/602442001 : ℝ) ^ p + (598595231/602442001 : ℝ) ^ p := by
    exact cert_lt (x := (548511169/602442001 : ℝ)) (y := (598595231/602442001 : ℝ)) (X := (13005515351333/100000000000000 : ℝ)) (Y := (86994484840971/100000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1105160318/1192673997 : ℝ) ^ p + (393711229/397557999 : ℝ) ^ p := by
    exact cert_lt (x := (1105160318/1192673997 : ℝ)) (y := (393711229/397557999 : ℝ)) (X := (9530634710521/50000000000000 : ℝ)) (Y := (16187746258411/20000000000000 : ℝ)) 87 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992268851/1000000000 : ℝ)) (U := (1192673997/1000000000 : ℝ)) (Ab := (1645533507/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (458971791/500000000 : ℝ)) (σ := (992268851/1000000000 : ℝ)) (Ab := (552580159/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab023
