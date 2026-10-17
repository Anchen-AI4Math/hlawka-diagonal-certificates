import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 11, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab011 (p : ℝ) (hpa : (683/32 : ℝ) ≤ p) (hpb : p ≤ (171/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2125808864381/93229500000000 : ℝ) (5888637/500000000 : ℝ) (4000000559377/18645900000000 : ℝ) (3033/2500 : ℝ) (96809221/50000000 : ℝ) (968046247/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192527651/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11037/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4431/10000 : ℝ)
      else (7583/10000 : ℝ) ≤ X j i ∧ X j i ≤ (1479/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2125808864381/93229500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5888637/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (56881789/62500000 : ℝ) ^ p + (248329101/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (56881789/62500000 : ℝ)) (y := (248329101/250000000 : ℝ)) (X := (13354197172139/100000000000000 : ℝ)) (Y := (43322909700543/50000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248329101/250000000 : ℝ) ^ p + (56881789/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248329101/250000000 : ℝ)) (y := (56881789/62500000 : ℝ)) (X := (43322909700543/50000000000000 : ℝ)) (Y := (13354197172139/100000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (475856257/250000000 : ℝ)) (τ := (56881789/62500000 : ℝ)) (σ := (248329101/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (192696722/205013661 : ℝ) ^ p + (134712895/136675774 : ℝ) ^ p := by
    exact cert_lt (x := (192696722/205013661 : ℝ)) (y := (134712895/136675774 : ℝ)) (X := (3324615130271/12500000000000 : ℝ)) (Y := (73403080006497/100000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (56881789/62500000 : ℝ)) (n' := (205013661/250000000 : ℝ)) (Ab := (96348361/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (91605179/100000000 : ℝ) ^ p + (992235373/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (91605179/100000000 : ℝ)) (y := (992235373/1000000000 : ℝ)) (X := (7673802118269/50000000000000 : ℝ)) (Y := (16930482123141/20000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992235373/1000000000 : ℝ) ^ p + (91605179/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992235373/1000000000 : ℝ)) (y := (91605179/100000000 : ℝ)) (X := (16930482123141/20000000000000 : ℝ)) (Y := (7673802118269/50000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1908287163/1000000000 : ℝ)) (τ := (91605179/100000000 : ℝ)) (σ := (992235373/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (388607249/413590530 : ℝ) ^ p + (135900631/137863510 : ℝ) ^ p := by
    exact cert_lt (x := (388607249/413590530 : ℝ)) (y := (135900631/137863510 : ℝ)) (X := (26399710050283/100000000000000 : ℝ)) (Y := (18400072719377/25000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (91605179/100000000 : ℝ)) (n' := (41359053/50000000 : ℝ)) (Ab := (388607249/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (458175083/500000000 : ℝ) ^ p + (248044137/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (458175083/500000000 : ℝ)) (y := (248044137/250000000 : ℝ)) (X := (618192540083/4000000000000 : ℝ)) (Y := (42272600911631/50000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248044137/250000000 : ℝ) ^ p + (458175083/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248044137/250000000 : ℝ)) (y := (458175083/500000000 : ℝ)) (X := (42272600911631/50000000000000 : ℝ)) (Y := (618192540083/4000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (954263357/500000000 : ℝ)) (τ := (458175083/500000000 : ℝ)) (σ := (248044137/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (777536053/827537650 : ℝ) ^ p + (407880188/413768825 : ℝ) ^ p := by
    exact cert_lt (x := (777536053/827537650 : ℝ)) (y := (407880188/413768825 : ℝ)) (X := (26389918091811/100000000000000 : ℝ)) (Y := (2944403310807/4000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (458175083/500000000 : ℝ)) (n' := (16550753/20000000 : ℝ)) (Ab := (777536053/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (57272811/62500000 : ℝ) ^ p + (62010851/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (57272811/62500000 : ℝ)) (y := (62010851/62500000 : ℝ)) (X := (15460153425089/100000000000000 : ℝ)) (Y := (2641870675919/3125000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (62010851/62500000 : ℝ) ^ p + (57272811/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (62010851/62500000 : ℝ)) (y := (57272811/62500000 : ℝ)) (X := (2641870675919/3125000000000 : ℝ)) (Y := (15460153425089/100000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (59641831/31250000 : ℝ)) (τ := (57272811/62500000 : ℝ)) (σ := (62010851/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (777552011/827555347 : ℝ) ^ p + (815778073/827555347 : ℝ) ^ p := by
    exact cert_lt (x := (777552011/827555347 : ℝ)) (y := (815778073/827555347 : ℝ)) (X := (13194716123873/50000000000000 : ℝ)) (Y := (36805284269461/50000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (57272811/62500000 : ℝ)) (n' := (827555347/1000000000 : ℝ)) (Ab := (777552011/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (916365711/1000000000 : ℝ) ^ p + (992173471/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (916365711/1000000000 : ℝ)) (y := (992173471/1000000000 : ℝ)) (X := (15460418483951/100000000000000 : ℝ)) (Y := (10567449692777/12500000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992173471/1000000000 : ℝ) ^ p + (916365711/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992173471/1000000000 : ℝ)) (y := (916365711/1000000000 : ℝ)) (X := (10567449692777/12500000000000 : ℝ)) (Y := (15460418483951/100000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (954269591/500000000 : ℝ)) (τ := (916365711/1000000000 : ℝ)) (σ := (992173471/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (777552803/827556225 : ℝ) ^ p + (271926317/275852075 : ℝ) ^ p := by
    exact cert_lt (x := (777552803/827556225 : ℝ)) (y := (271926317/275852075 : ℝ)) (X := (13194704172613/50000000000000 : ℝ)) (Y := (7361059263887/10000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (916365711/1000000000 : ℝ)) (n' := (33102249/40000000 : ℝ)) (Ab := (777552803/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (229091437/250000000 : ℝ) ^ p + (992173463/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229091437/250000000 : ℝ)) (y := (992173463/1000000000 : ℝ)) (X := (3092086365433/20000000000000 : ℝ)) (Y := (10567447871489/12500000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992173463/1000000000 : ℝ) ^ p + (229091437/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992173463/1000000000 : ℝ)) (y := (229091437/250000000 : ℝ)) (X := (10567447871489/12500000000000 : ℝ)) (Y := (3092086365433/20000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1908539211/1000000000 : ℝ)) (τ := (229091437/250000000 : ℝ)) (σ := (992173463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (777552843/827556269 : ℝ) ^ p + (815778995/827556269 : ℝ) ^ p := by
    exact cert_lt (x := (777552843/827556269 : ℝ)) (y := (815778995/827556269 : ℝ)) (X := (659735184303/2500000000000 : ℝ)) (Y := (18402648461653/25000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (229091437/250000000 : ℝ)) (n' := (827556269/1000000000 : ℝ)) (Ab := (777552843/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (916365749/1000000000 : ℝ) ^ p + (992173463/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (916365749/1000000000 : ℝ)) (y := (992173463/1000000000 : ℝ)) (X := (966277011737/6250000000000 : ℝ)) (Y := (10567447871489/12500000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992173463/1000000000 : ℝ) ^ p + (916365749/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992173463/1000000000 : ℝ)) (y := (916365749/1000000000 : ℝ)) (X := (10567447871489/12500000000000 : ℝ)) (Y := (966277011737/6250000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (477134803/250000000 : ℝ)) (τ := (916365749/1000000000 : ℝ)) (σ := (992173463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (388776422/413778135 : ℝ) ^ p + (135963166/137926045 : ℝ) ^ p := by
    exact cert_lt (x := (388776422/413778135 : ℝ)) (y := (135963166/137926045 : ℝ)) (X := (26389407415953/100000000000000 : ℝ)) (Y := (3680529693703/5000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (916365749/1000000000 : ℝ)) (n' := (82755627/100000000 : ℝ)) (Ab := (194388211/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (477134803/250000000 : ℝ)) (τ := (916365749/1000000000 : ℝ)) (σ := (992173463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (916365749/1000000000 : ℝ)) (n' := (82755627/100000000 : ℝ)) (Ab := (194388211/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (477134803/250000000 : ℝ)) (τ := (916365749/1000000000 : ℝ)) (σ := (992173463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (916365749/1000000000 : ℝ)) (n' := (82755627/100000000 : ℝ)) (Ab := (194388211/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (477134803/250000000 : ℝ)) (τ := (916365749/1000000000 : ℝ)) (σ := (992173463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (916365749/1000000000 : ℝ)) (n' := (82755627/100000000 : ℝ)) (Ab := (194388211/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (477134803/250000000 : ℝ)) (τ := (916365749/1000000000 : ℝ)) (σ := (992173463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1643170373/1807472349 : ℝ) ^ p + (199521675/200830261 : ℝ) ^ p := by
    exact cert_lt (x := (1643170373/1807472349 : ℝ)) (y := (199521675/200830261 : ℝ)) (X := (13040934335961/100000000000000 : ℝ)) (Y := (86959065947777/100000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (367898224/397509217 : ℝ) ^ p + (393583459/397509217 : ℝ) ^ p := by
    exact cert_lt (x := (367898224/397509217 : ℝ)) (y := (393583459/397509217 : ℝ)) (X := (1194711252303/6250000000000 : ℝ)) (Y := (80884620339353/100000000000000 : ℝ)) 171 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992173463/1000000000 : ℝ)) (U := (1192527651/1000000000 : ℝ)) (Ab := (1643170373/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (916365749/1000000000 : ℝ)) (σ := (992173463/1000000000 : ℝ)) (Ab := (68980917/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab011
