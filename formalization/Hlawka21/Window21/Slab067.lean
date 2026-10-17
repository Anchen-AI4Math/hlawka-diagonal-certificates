import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 67, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab067 (p : ℝ) (hpa : (739/32 : ℝ) ≤ p) (hpb : p ≤ (185/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (84156654419/4034940000000 : ℝ) (16791/1562500 : ℝ) (4000000605241/20174700000000 : ℝ) (3033/2500 : ℝ) (60654427/31250000 : ℝ) (970431469/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149153073/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11103/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4549/10000 : ℝ)
      else (7699/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2961/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (84156654419/4034940000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (16791/1562500 : ℝ) := by norm_num
  have pc0 : 1 < (917271237/1000000000 : ℝ) ^ p + (993710643/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917271237/1000000000 : ℝ)) (y := (993710643/1000000000 : ℝ)) (X := (6787831650113/50000000000000 : ℝ)) (Y := (86424354095457/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993710643/1000000000 : ℝ) ^ p + (917271237/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993710643/1000000000 : ℝ)) (y := (917271237/1000000000 : ℝ)) (X := (86424354095457/100000000000000 : ℝ)) (Y := (6787831650113/50000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (47774547/25000000 : ℝ)) (τ := (917271237/1000000000 : ℝ)) (σ := (993710643/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (43343433/45935264 : ℝ) ^ p + (4250461/4306431 : ℝ) ^ p := by
    exact cert_lt (x := (43343433/45935264 : ℝ)) (y := (4250461/4306431 : ℝ)) (X := (13052394911689/50000000000000 : ℝ)) (Y := (73895211574481/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (917271237/1000000000 : ℝ)) (n' := (12919293/15625000 : ℝ)) (Ab := (390090897/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (230745267/250000000 : ℝ) ^ p + (992656783/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230745267/250000000 : ℝ)) (y := (992656783/1000000000 : ℝ)) (X := (3917629360349/25000000000000 : ℝ)) (Y := (84329499699483/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992656783/1000000000 : ℝ) ^ p + (230745267/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992656783/1000000000 : ℝ)) (y := (230745267/250000000 : ℝ)) (X := (84329499699483/100000000000000 : ℝ)) (Y := (3917629360349/25000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1915637851/1000000000 : ℝ)) (τ := (230745267/250000000 : ℝ)) (σ := (992656783/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (786336069/833610764 : ℝ) ^ p + (205716131/208402691 : ℝ) ^ p := by
    exact cert_lt (x := (786336069/833610764 : ℝ)) (y := (205716131/208402691 : ℝ)) (X := (25921666893659/100000000000000 : ℝ)) (Y := (74078334402869/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (230745267/250000000 : ℝ)) (n' := (208402691/250000000 : ℝ)) (Ab := (786336069/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (923237559/1000000000 : ℝ) ^ p + (198521067/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (923237559/1000000000 : ℝ)) (y := (198521067/200000000 : ℝ)) (X := (315430621931/2000000000000 : ℝ)) (Y := (21057121419433/25000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198521067/200000000 : ℝ) ^ p + (923237559/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198521067/200000000 : ℝ)) (y := (923237559/1000000000 : ℝ)) (X := (21057121419433/25000000000000 : ℝ)) (Y := (315430621931/2000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (957921447/500000000 : ℝ)) (τ := (923237559/1000000000 : ℝ)) (σ := (198521067/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (16736417/17742855 : ℝ) ^ p + (54877863/55594279 : ℝ) ^ p := by
    exact cert_lt (x := (16736417/17742855 : ℝ)) (y := (54877863/55594279 : ℝ)) (X := (1295676332363/5000000000000 : ℝ)) (Y := (9260809356227/12500000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (923237559/1000000000 : ℝ)) (n' := (166782837/200000000 : ℝ)) (Ab := (786611599/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (923248957/1000000000 : ℝ) ^ p + (6203769/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (923248957/1000000000 : ℝ)) (y := (6203769/6250000 : ℝ)) (X := (15776034388477/100000000000000 : ℝ)) (Y := (84223982327637/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (6203769/6250000 : ℝ) ^ p + (923248957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (6203769/6250000 : ℝ)) (y := (923248957/1000000000 : ℝ)) (X := (84223982327637/100000000000000 : ℝ)) (Y := (15776034388477/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1915851997/1000000000 : ℝ)) (τ := (923248957/1000000000 : ℝ)) (σ := (6203769/6250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (393311920/416963833 : ℝ) ^ p + (411590713/416963833 : ℝ) ^ p := by
    exact cert_lt (x := (393311920/416963833 : ℝ)) (y := (411590713/416963833 : ℝ)) (X := (12956582279439/50000000000000 : ℝ)) (Y := (37043418206207/50000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (923248957/1000000000 : ℝ)) (n' := (416963833/500000000 : ℝ)) (Ab := (4916399/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (115406183/125000000 : ℝ) ^ p + (496301469/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115406183/125000000 : ℝ)) (y := (496301469/500000000 : ℝ)) (X := (7888117365089/50000000000000 : ℝ)) (Y := (84223782184091/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496301469/500000000 : ℝ) ^ p + (115406183/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496301469/500000000 : ℝ)) (y := (115406183/125000000 : ℝ)) (X := (84223782184091/100000000000000 : ℝ)) (Y := (7888117365089/50000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (957926201/500000000 : ℝ)) (τ := (115406183/125000000 : ℝ)) (σ := (496301469/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (786624385/833928266 : ℝ) ^ p + (411591013/416964133 : ℝ) ^ p := by
    exact cert_lt (x := (786624385/833928266 : ℝ)) (y := (411591013/416964133 : ℝ)) (X := (25913148587579/100000000000000 : ℝ)) (Y := (74086852504279/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (115406183/125000000 : ℝ)) (n' := (416964133/500000000 : ℝ)) (Ab := (157324877/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (923249487/1000000000 : ℝ) ^ p + (992602933/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (923249487/1000000000 : ℝ)) (y := (992602933/1000000000 : ℝ)) (X := (3155248763743/20000000000000 : ℝ)) (Y := (10527971546643/12500000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992602933/1000000000 : ℝ) ^ p + (923249487/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992602933/1000000000 : ℝ)) (y := (923249487/1000000000 : ℝ)) (X := (10527971546643/12500000000000 : ℝ)) (Y := (3155248763743/20000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (95792621/50000000 : ℝ)) (τ := (923249487/1000000000 : ℝ)) (σ := (992602933/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (71511310/75811663 : ℝ) ^ p + (823182053/833928293 : ℝ) ^ p := by
    exact cert_lt (x := (71511310/75811663 : ℝ)) (y := (823182053/833928293 : ℝ)) (X := (80978588221/312500000000 : ℝ)) (Y := (18521713307103/25000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (923249487/1000000000 : ℝ)) (n' := (833928293/1000000000 : ℝ)) (Ab := (78662441/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (95792621/50000000 : ℝ)) (τ := (923249487/1000000000 : ℝ)) (σ := (992602933/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (923249487/1000000000 : ℝ)) (n' := (833928293/1000000000 : ℝ)) (Ab := (78662441/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (95792621/50000000 : ℝ)) (τ := (923249487/1000000000 : ℝ)) (σ := (992602933/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (923249487/1000000000 : ℝ)) (n' := (833928293/1000000000 : ℝ)) (Ab := (78662441/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (95792621/50000000 : ℝ)) (τ := (923249487/1000000000 : ℝ)) (σ := (992602933/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (923249487/1000000000 : ℝ)) (n' := (833928293/1000000000 : ℝ)) (Ab := (78662441/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (95792621/50000000 : ℝ)) (τ := (923249487/1000000000 : ℝ)) (σ := (992602933/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (923249487/1000000000 : ℝ)) (n' := (833928293/1000000000 : ℝ)) (Ab := (78662441/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (95792621/50000000 : ℝ)) (τ := (923249487/1000000000 : ℝ)) (σ := (992602933/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (551190217/602258472 : ℝ) ^ p + (74834549/75282309 : ℝ) ^ p := by
    exact cert_lt (x := (551190217/602258472 : ℝ)) (y := (74834549/75282309 : ℝ)) (X := (3221493322169/25000000000000 : ℝ)) (Y := (43557013488407/50000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (185037741/198870764 : ℝ) ^ p + (49269931/49717691 : ℝ) ^ p := by
    exact cert_lt (x := (185037741/198870764 : ℝ)) (y := (49269931/49717691 : ℝ)) (X := (4719346011347/25000000000000 : ℝ)) (Y := (81122616484159/100000000000000 : ℝ)) 185 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992602933/1000000000 : ℝ)) (U := (149153073/125000000 : ℝ)) (Ab := (1653570651/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (923249487/1000000000 : ℝ)) (σ := (992602933/1000000000 : ℝ)) (Ab := (555113223/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab067
