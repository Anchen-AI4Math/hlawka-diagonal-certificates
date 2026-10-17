import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 64, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab064 (p : ℝ) (hpa : (30 : ℝ) ≤ p) (hpb : p ≤ (481/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (4468408169/332250000000 : ℝ) (1720411/250000000 : ℝ) (20000003987/132900000000 : ℝ) (591/500 : ℝ) (244301727/125000000 : ℝ) (30536249/31250000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578912263/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10903/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5603/10000 : ℝ)
      else (413/500 : ℝ) ≤ X j i ∧ X j i ≤ (11499/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (4468408169/332250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1720411/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (471256889/500000000 : ℝ) ^ p + (496937123/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (471256889/500000000 : ℝ)) (y := (496937123/500000000 : ℝ)) (X := (843323522103/5000000000000 : ℝ)) (Y := (16626709930933/20000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496937123/500000000 : ℝ) ^ p + (471256889/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496937123/500000000 : ℝ)) (y := (471256889/500000000 : ℝ)) (X := (16626709930933/20000000000000 : ℝ)) (Y := (843323522103/5000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (242048503/125000000 : ℝ)) (τ := (471256889/500000000 : ℝ)) (σ := (496937123/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (825929801/869601450 : ℝ) ^ p + (431359903/434800725 : ℝ) ^ p := by
    exact cert_lt (x := (825929801/869601450 : ℝ)) (y := (431359903/434800725 : ℝ)) (X := (2655815377429/12500000000000 : ℝ)) (Y := (19688369524919/25000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (471256889/500000000 : ℝ)) (n' := (17392029/20000000 : ℝ)) (Ab := (825929801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (59106571/62500000 : ℝ) ^ p + (99314917/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (59106571/62500000 : ℝ)) (y := (99314917/100000000 : ℝ)) (X := (18670552224283/100000000000000 : ℝ)) (Y := (81329466759209/100000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99314917/100000000 : ℝ) ^ p + (59106571/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (99314917/100000000 : ℝ)) (y := (59106571/62500000 : ℝ)) (X := (81329466759209/100000000000000 : ℝ)) (Y := (18670552224283/100000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (969427153/500000000 : ℝ)) (τ := (59106571/62500000 : ℝ)) (σ := (99314917/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (829285411/873242387 : ℝ) ^ p + (866360743/873242387 : ℝ) ^ p := by
    exact cert_lt (x := (829285411/873242387 : ℝ)) (y := (866360743/873242387 : ℝ)) (X := (1322984045973/6250000000000 : ℝ)) (Y := (9854032025579/12500000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (59106571/62500000 : ℝ)) (n' := (873242387/1000000000 : ℝ)) (Ab := (829285411/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (472895073/500000000 : ℝ) ^ p + (993128643/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (472895073/500000000 : ℝ)) (y := (993128643/1000000000 : ℝ)) (X := (18721072291239/100000000000000 : ℝ)) (Y := (40639473947017/50000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993128643/1000000000 : ℝ) ^ p + (472895073/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993128643/1000000000 : ℝ)) (y := (472895073/500000000 : ℝ)) (X := (40639473947017/50000000000000 : ℝ)) (Y := (18721072291239/100000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1938918789/1000000000 : ℝ)) (τ := (472895073/500000000 : ℝ)) (σ := (993128643/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (829374637/873339206 : ℝ) ^ p + (433228781/436669603 : ℝ) ^ p := by
    exact cert_lt (x := (829374637/873339206 : ℝ)) (y := (433228781/436669603 : ℝ)) (X := (2116565835629/10000000000000 : ℝ)) (Y := (1576686862481/2000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (472895073/500000000 : ℝ)) (n' := (436669603/500000000 : ℝ)) (Ab := (829374637/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (945792399/1000000000 : ℝ) ^ p + (496564049/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (945792399/1000000000 : ℝ)) (y := (496564049/500000000 : ℝ)) (X := (3744482601733/20000000000000 : ℝ)) (Y := (81277607011609/100000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496564049/500000000 : ℝ) ^ p + (945792399/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496564049/500000000 : ℝ)) (y := (945792399/1000000000 : ℝ)) (X := (81277607011609/100000000000000 : ℝ)) (Y := (3744482601733/20000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1938920497/1000000000 : ℝ)) (τ := (945792399/1000000000 : ℝ)) (σ := (496564049/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (829377001/873341772 : ℝ) ^ p + (216615032/218335443 : ℝ) ^ p := by
    exact cert_lt (x := (829377001/873341772 : ℝ)) (y := (216615032/218335443 : ℝ)) (X := (21165602485057/100000000000000 : ℝ)) (Y := (39417199214119/50000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (945792399/1000000000 : ℝ)) (n' := (218335443/250000000 : ℝ)) (Ab := (829377001/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (945792459/1000000000 : ℝ) ^ p + (993128083/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (945792459/1000000000 : ℝ)) (y := (993128083/1000000000 : ℝ)) (X := (2340306089349/12500000000000 : ℝ)) (Y := (8127757010689/10000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993128083/1000000000 : ℝ) ^ p + (945792459/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993128083/1000000000 : ℝ)) (y := (945792459/1000000000 : ℝ)) (X := (8127757010689/10000000000000 : ℝ)) (Y := (2340306089349/12500000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (969460271/500000000 : ℝ)) (τ := (945792459/1000000000 : ℝ)) (σ := (993128083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (103672133/109167730 : ℝ) ^ p + (30945007/31190780 : ℝ) ^ p := by
    exact cert_lt (x := (103672133/109167730 : ℝ)) (y := (30945007/31190780 : ℝ)) (X := (21165601275333/100000000000000 : ℝ)) (Y := (9854299986727/12500000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (945792459/1000000000 : ℝ)) (n' := (10916773/12500000 : ℝ)) (Ab := (103672133/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (47289623/50000000 : ℝ) ^ p + (993128083/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (47289623/50000000 : ℝ)) (y := (993128083/1000000000 : ℝ)) (X := (3744489861979/20000000000000 : ℝ)) (Y := (8127757010689/10000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993128083/1000000000 : ℝ) ^ p + (47289623/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (993128083/1000000000 : ℝ)) (y := (47289623/50000000 : ℝ)) (X := (8127757010689/10000000000000 : ℝ)) (Y := (3744489861979/20000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1938920543/1000000000 : ℝ)) (τ := (47289623/50000000 : ℝ)) (σ := (993128083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (829377065/873341841 : ℝ) ^ p + (866460197/873341841 : ℝ) ^ p := by
    exact cert_lt (x := (829377065/873341841 : ℝ)) (y := (866460197/873341841 : ℝ)) (X := (10582800656977/50000000000000 : ℝ)) (Y := (78834399915369/100000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (47289623/50000000 : ℝ)) (n' := (873341841/1000000000 : ℝ)) (Ab := (165875413/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1938920543/1000000000 : ℝ)) (τ := (47289623/50000000 : ℝ)) (σ := (993128083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (47289623/50000000 : ℝ)) (n' := (873341841/1000000000 : ℝ)) (Ab := (165875413/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1938920543/1000000000 : ℝ)) (τ := (47289623/50000000 : ℝ)) (σ := (993128083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (47289623/50000000 : ℝ)) (n' := (873341841/1000000000 : ℝ)) (Ab := (165875413/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1938920543/1000000000 : ℝ)) (τ := (47289623/50000000 : ℝ)) (σ := (993128083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (47289623/50000000 : ℝ)) (n' := (873341841/1000000000 : ℝ)) (Ab := (165875413/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1938920543/1000000000 : ℝ)) (τ := (47289623/50000000 : ℝ)) (σ := (993128083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (47289623/50000000 : ℝ)) (n' := (873341841/1000000000 : ℝ)) (Ab := (165875413/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1938920543/1000000000 : ℝ)) (τ := (47289623/50000000 : ℝ)) (σ := (993128083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (854938682/921087737 : ℝ) ^ p + (917646915/921087737 : ℝ) ^ p := by
    exact cert_lt (x := (854938682/921087737 : ℝ)) (y := (917646915/921087737 : ℝ)) (X := (5320667720019/50000000000000 : ℝ)) (Y := (89358664778591/100000000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1090263837/1157824526 : ℝ) ^ p + (575471441/578912263 : ℝ) ^ p := by
    exact cert_lt (x := (1090263837/1157824526 : ℝ)) (y := (575471441/578912263 : ℝ)) (X := (16407179231141/100000000000000 : ℝ)) (Y := (2612275664251/3125000000000 : ℝ)) 481 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993128083/1000000000 : ℝ)) (U := (578912263/500000000 : ℝ)) (Ab := (427469341/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (47289623/50000000 : ℝ)) (σ := (993128083/1000000000 : ℝ)) (Ab := (1090263837/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab064
