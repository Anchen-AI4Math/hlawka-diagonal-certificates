import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 16, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab016 (p : ℝ) (hpa : (43/2 : ℝ) ≤ p) (hpb : p ≤ (689/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (132731905967/5869500000000 : ℝ) (5838693/500000000 : ℝ) (250000035217/1173900000000 : ℝ) (3033/2500 : ℝ) (484160027/250000000 : ℝ) (193654949/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192588347/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2761/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2221/5000 : ℝ)
      else (3797/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5917/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (132731905967/5869500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5838693/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (455398991/500000000 : ℝ) ^ p + (993353463/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (455398991/500000000 : ℝ)) (y := (993353463/1000000000 : ℝ)) (X := (13375382884327/100000000000000 : ℝ)) (Y := (86624633893967/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993353463/1000000000 : ℝ) ^ p + (455398991/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993353463/1000000000 : ℝ)) (y := (455398991/500000000 : ℝ)) (X := (86624633893967/100000000000000 : ℝ)) (Y := (13375382884327/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (380830289/200000000 : ℝ)) (τ := (455398991/500000000 : ℝ)) (σ := (993353463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (771689131/820713978 : ℝ) ^ p + (19262776/19540809 : ℝ) ^ p := by
    exact cert_lt (x := (771689131/820713978 : ℝ)) (y := (19262776/19540809 : ℝ)) (X := (26549171557657/100000000000000 : ℝ)) (Y := (73450829536719/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (455398991/500000000 : ℝ)) (n' := (410356989/500000000 : ℝ)) (Ab := (771689131/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (916721069/1000000000 : ℝ) ^ p + (248068641/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (916721069/1000000000 : ℝ)) (y := (248068641/250000000 : ℝ)) (X := (7689356449373/50000000000000 : ℝ)) (Y := (42310651598163/50000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248068641/250000000 : ℝ) ^ p + (916721069/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248068641/250000000 : ℝ)) (y := (916721069/1000000000 : ℝ)) (X := (42310651598163/50000000000000 : ℝ)) (Y := (7689356449373/50000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1908995633/1000000000 : ℝ)) (τ := (916721069/1000000000 : ℝ)) (σ := (248068641/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (778092865/827809228 : ℝ) ^ p + (408065921/413904614 : ℝ) ^ p := by
    exact cert_lt (x := (778092865/827809228 : ℝ)) (y := (408065921/413904614 : ℝ)) (X := (6588318179947/25000000000000 : ℝ)) (Y := (73646728664597/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (916721069/1000000000 : ℝ)) (n' := (206952307/250000000 : ℝ)) (Ab := (155618573/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (114626919/125000000 : ℝ) ^ p + (7751691/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (114626919/125000000 : ℝ)) (y := (7751691/7812500 : ℝ)) (X := (309707199819/2000000000000 : ℝ)) (Y := (84514655442177/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (7751691/7812500 : ℝ) ^ p + (114626919/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (7751691/7812500 : ℝ)) (y := (114626919/125000000 : ℝ)) (X := (84514655442177/100000000000000 : ℝ)) (Y := (309707199819/2000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (9546159/5000000 : ℝ)) (τ := (114626919/125000000 : ℝ)) (σ := (7751691/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (778409908/828160581 : ℝ) ^ p + (272161065/276053527 : ℝ) ^ p := by
    exact cert_lt (x := (778409908/828160581 : ℝ)) (y := (272161065/276053527 : ℝ)) (X := (26343646254553/100000000000000 : ℝ)) (Y := (36828177535501/50000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (114626919/125000000 : ℝ)) (n' := (828160581/1000000000 : ℝ)) (Ab := (194602477/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (917029809/1000000000 : ℝ) ^ p + (992213581/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917029809/1000000000 : ℝ)) (y := (992213581/1000000000 : ℝ)) (X := (15490617286737/100000000000000 : ℝ)) (Y := (21127349393609/25000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992213581/1000000000 : ℝ) ^ p + (917029809/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992213581/1000000000 : ℝ)) (y := (917029809/1000000000 : ℝ)) (X := (21127349393609/25000000000000 : ℝ)) (Y := (15490617286737/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (190924339/100000000 : ℝ)) (τ := (917029809/1000000000 : ℝ)) (σ := (992213581/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (778425480/828177839 : ℝ) ^ p + (816500453/828177839 : ℝ) ^ p := by
    exact cert_lt (x := (778425480/828177839 : ℝ)) (y := (816500453/828177839 : ℝ)) (X := (26343173174491/100000000000000 : ℝ)) (Y := (14731365545589/20000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (917029809/1000000000 : ℝ)) (n' := (828177839/1000000000 : ℝ)) (Ab := (19460637/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (458515259/500000000 : ℝ) ^ p + (992213441/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458515259/500000000 : ℝ)) (y := (992213441/1000000000 : ℝ)) (X := (7745437579371/50000000000000 : ℝ)) (Y := (84509140832691/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992213441/1000000000 : ℝ) ^ p + (458515259/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992213441/1000000000 : ℝ)) (y := (458515259/500000000 : ℝ)) (X := (84509140832691/100000000000000 : ℝ)) (Y := (7745437579371/50000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1909243959/1000000000 : ℝ)) (τ := (458515259/500000000 : ℝ)) (σ := (992213441/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (778426244/828178685 : ℝ) ^ p + (816501299/828178685 : ℝ) ^ p := by
    exact cert_lt (x := (778426244/828178685 : ℝ)) (y := (816501299/828178685 : ℝ)) (X := (5268630091469/20000000000000 : ℝ)) (Y := (18414212724377/25000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (458515259/500000000 : ℝ)) (n' := (165635737/200000000 : ℝ)) (Ab := (194606561/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (917030553/1000000000 : ℝ) ^ p + (496106717/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (917030553/1000000000 : ℝ)) (y := (496106717/500000000 : ℝ)) (X := (7745443944389/50000000000000 : ℝ)) (Y := (84509127995623/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496106717/500000000 : ℝ) ^ p + (917030553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496106717/500000000 : ℝ)) (y := (917030553/1000000000 : ℝ)) (X := (84509127995623/100000000000000 : ℝ)) (Y := (7745443944389/50000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1909243987/1000000000 : ℝ)) (τ := (917030553/1000000000 : ℝ)) (σ := (496106717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (778426282/828178727 : ℝ) ^ p + (816501341/828178727 : ℝ) ^ p := by
    exact cert_lt (x := (778426282/828178727 : ℝ)) (y := (816501341/828178727 : ℝ)) (X := (13171574690611/50000000000000 : ℝ)) (Y := (9207106505971/12500000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (917030553/1000000000 : ℝ)) (n' := (828178727/1000000000 : ℝ)) (Ab := (389213141/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (183406111/200000000 : ℝ) ^ p + (992213433/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183406111/200000000 : ℝ)) (y := (992213433/1000000000 : ℝ)) (X := (15490888616209/100000000000000 : ℝ)) (Y := (21127281540439/25000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992213433/1000000000 : ℝ) ^ p + (183406111/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992213433/1000000000 : ℝ)) (y := (183406111/200000000 : ℝ)) (X := (21127281540439/25000000000000 : ℝ)) (Y := (15490888616209/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (477310997/250000000 : ℝ)) (τ := (183406111/200000000 : ℝ)) (σ := (992213433/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (778426283/828178729 : ℝ) ^ p + (116643049/118311247 : ℝ) ^ p := by
    exact cert_lt (x := (778426283/828178729 : ℝ)) (y := (116643049/118311247 : ℝ)) (X := (13171574370059/50000000000000 : ℝ)) (Y := (73656852102543/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (183406111/200000000 : ℝ)) (n' := (828178729/1000000000 : ℝ)) (Ab := (778426283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (477310997/250000000 : ℝ)) (τ := (183406111/200000000 : ℝ)) (σ := (992213433/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (183406111/200000000 : ℝ)) (n' := (828178729/1000000000 : ℝ)) (Ab := (778426283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (477310997/250000000 : ℝ)) (τ := (183406111/200000000 : ℝ)) (σ := (992213433/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (183406111/200000000 : ℝ)) (n' := (828178729/1000000000 : ℝ)) (Ab := (778426283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (477310997/250000000 : ℝ)) (τ := (183406111/200000000 : ℝ)) (σ := (992213433/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (183406111/200000000 : ℝ)) (n' := (828178729/1000000000 : ℝ)) (Ab := (778426283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (477310997/250000000 : ℝ)) (τ := (183406111/200000000 : ℝ)) (σ := (992213433/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1644164555/1807411653 : ℝ) ^ p + (598578089/602470551 : ℝ) ^ p := by
    exact cert_lt (x := (1644164555/1807411653 : ℝ)) (y := (598578089/602470551 : ℝ)) (X := (13026016680797/100000000000000 : ℝ)) (Y := (695791868241/800000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1104309944/1192588347 : ℝ) ^ p + (393636987/397529449 : ℝ) ^ p := by
    exact cert_lt (x := (1104309944/1192588347 : ℝ)) (y := (393636987/397529449 : ℝ)) (X := (9546305491661/50000000000000 : ℝ)) (Y := (80907389434833/100000000000000 : ℝ)) 689 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992213433/1000000000 : ℝ)) (U := (1192588347/1000000000 : ℝ)) (Ab := (328832911/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (183406111/200000000 : ℝ)) (σ := (992213433/1000000000 : ℝ)) (Ab := (138038743/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab016
