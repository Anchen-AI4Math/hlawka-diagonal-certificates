import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 72, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab072 (p : ℝ) (hpa : (93/4 : ℝ) ≤ p) (hpb : p ≤ (745/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (262765065247/12694500000000 : ℝ) (10662759/1000000000 : ℝ) (500000076167/2538900000000 : ℝ) (3033/2500 : ℝ) (485333039/250000000 : ℝ) (194125447/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193287987/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2777/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2279/5000 : ℝ)
      else (1927/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5923/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (262765065247/12694500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10662759/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (917855833/1000000000 : ℝ) ^ p + (993743727/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917855833/1000000000 : ℝ)) (y := (993743727/1000000000 : ℝ)) (X := (13593872155509/100000000000000 : ℝ)) (Y := (86406144982107/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993743727/1000000000 : ℝ) ^ p + (917855833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993743727/1000000000 : ℝ)) (y := (917855833/1000000000 : ℝ)) (X := (86406144982107/100000000000000 : ℝ)) (Y := (13593872155509/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (47789989/25000000 : ℝ)) (τ := (917855833/1000000000 : ℝ)) (σ := (993743727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (780950634/827381225 : ℝ) ^ p + (816718466/827381225 : ℝ) ^ p := by
    exact cert_lt (x := (780950634/827381225 : ℝ)) (y := (816718466/827381225 : ℝ)) (X := (13032503005967/50000000000000 : ℝ)) (Y := (73934995017373/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (917855833/1000000000 : ℝ)) (n' := (33095249/40000000 : ℝ)) (Ab := (390475317/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (14430379/15625000 : ℝ) ^ p + (248173143/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (14430379/15625000 : ℝ)) (y := (248173143/250000000 : ℝ)) (X := (3139368835823/20000000000000 : ℝ)) (Y := (42151585967519/50000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248173143/250000000 : ℝ) ^ p + (14430379/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (248173143/250000000 : ℝ)) (y := (14430379/15625000 : ℝ)) (X := (42151585967519/50000000000000 : ℝ)) (Y := (3139368835823/20000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (479059207/250000000 : ℝ)) (τ := (14430379/15625000 : ℝ)) (σ := (248173143/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (787080192/834126127 : ℝ) ^ p + (823463368/834126127 : ℝ) ^ p := by
    exact cert_lt (x := (787080192/834126127 : ℝ)) (y := (823463368/834126127 : ℝ)) (X := (25883074128379/100000000000000 : ℝ)) (Y := (18529231675761/25000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (14430379/15625000 : ℝ)) (n' := (834126127/1000000000 : ℝ)) (Ab := (1537266/1953125 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (4618987/5000000 : ℝ) ^ p + (39705669/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (4618987/5000000 : ℝ)) (y := (39705669/40000000 : ℝ)) (X := (789865927619/5000000000000 : ℝ)) (Y := (84202698102919/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39705669/40000000 : ℝ) ^ p + (4618987/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (39705669/40000000 : ℝ)) (y := (4618987/5000000 : ℝ)) (X := (84202698102919/100000000000000 : ℝ)) (Y := (789865927619/5000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (15331513/8000000 : ℝ)) (τ := (4618987/5000000 : ℝ)) (σ := (39705669/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (787352059/834425340 : ℝ) ^ p + (274587527/278141780 : ℝ) ^ p := by
    exact cert_lt (x := (787352059/834425340 : ℝ)) (y := (274587527/278141780 : ℝ)) (X := (25875062374051/100000000000000 : ℝ)) (Y := (7412493913669/10000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (4618987/5000000 : ℝ)) (n' := (41721267/50000000 : ℝ)) (Ab := (787352059/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (461904273/500000000 : ℝ) ^ p + (496319739/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461904273/500000000 : ℝ)) (y := (496319739/500000000 : ℝ)) (X := (1975219572947/12500000000000 : ℝ)) (Y := (84198260669029/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496319739/500000000 : ℝ) ^ p + (461904273/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496319739/500000000 : ℝ)) (y := (461904273/500000000 : ℝ)) (X := (84198260669029/100000000000000 : ℝ)) (Y := (1975219572947/12500000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239556003/125000000 : ℝ)) (τ := (461904273/500000000 : ℝ)) (σ := (496319739/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (787364027/834438512 : ℝ) ^ p + (823775753/834438512 : ℝ) ^ p := by
    exact cert_lt (x := (787364027/834438512 : ℝ)) (y := (823775753/834438512 : ℝ)) (X := (25874709735699/100000000000000 : ℝ)) (Y := (74125291748251/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (461904273/500000000 : ℝ)) (n' := (52152407/62500000 : ℝ)) (Ab := (787364027/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (230952259/250000000 : ℝ) ^ p + (992639379/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230952259/250000000 : ℝ)) (y := (992639379/1000000000 : ℝ)) (X := (7900975857751/50000000000000 : ℝ)) (Y := (10524758145801/12500000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992639379/1000000000 : ℝ) ^ p + (230952259/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992639379/1000000000 : ℝ)) (y := (230952259/250000000 : ℝ)) (X := (10524758145801/12500000000000 : ℝ)) (Y := (7900975857751/50000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383289683/200000000 : ℝ)) (τ := (230952259/250000000 : ℝ)) (σ := (992639379/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (787364553/834439091 : ℝ) ^ p + (823776332/834439091 : ℝ) ^ p := by
    exact cert_lt (x := (787364553/834439091 : ℝ)) (y := (823776332/834439091 : ℝ)) (X := (5174938835419/20000000000000 : ℝ)) (Y := (9265663405967/12500000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (230952259/250000000 : ℝ)) (n' := (834439091/1000000000 : ℝ)) (Ab := (787364553/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (923809059/1000000000 : ℝ) ^ p + (496319687/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (923809059/1000000000 : ℝ)) (y := (496319687/500000000 : ℝ)) (X := (15801960874813/100000000000000 : ℝ)) (Y := (1683961105851/2000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496319687/500000000 : ℝ) ^ p + (923809059/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496319687/500000000 : ℝ)) (y := (923809059/1000000000 : ℝ)) (X := (1683961105851/2000000000000 : ℝ)) (Y := (15801960874813/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1916448433/1000000000 : ℝ)) (τ := (923809059/1000000000 : ℝ)) (σ := (496319687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (787364577/834439118 : ℝ) ^ p + (823776359/834439118 : ℝ) ^ p := by
    exact cert_lt (x := (787364577/834439118 : ℝ)) (y := (823776359/834439118 : ℝ)) (X := (3234336630903/12500000000000 : ℝ)) (Y := (74125307970509/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (923809059/1000000000 : ℝ)) (n' := (417219559/500000000 : ℝ)) (Ab := (787364577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1916448433/1000000000 : ℝ)) (τ := (923809059/1000000000 : ℝ)) (σ := (496319687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (923809059/1000000000 : ℝ)) (n' := (417219559/500000000 : ℝ)) (Ab := (787364577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1916448433/1000000000 : ℝ)) (τ := (923809059/1000000000 : ℝ)) (σ := (496319687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (923809059/1000000000 : ℝ)) (n' := (417219559/500000000 : ℝ)) (Ab := (787364577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1916448433/1000000000 : ℝ)) (τ := (923809059/1000000000 : ℝ)) (σ := (496319687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (923809059/1000000000 : ℝ)) (n' := (417219559/500000000 : ℝ)) (Ab := (787364577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1916448433/1000000000 : ℝ)) (τ := (923809059/1000000000 : ℝ)) (σ := (496319687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (923809059/1000000000 : ℝ)) (n' := (417219559/500000000 : ℝ)) (Ab := (787364577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1916448433/1000000000 : ℝ)) (τ := (923809059/1000000000 : ℝ)) (σ := (496319687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1654426450/1806712013 : ℝ) ^ p + (1796049254/1806712013 : ℝ) ^ p := by
    exact cert_lt (x := (1654426450/1806712013 : ℝ)) (y := (1796049254/1806712013 : ℝ)) (X := (3218331996623/25000000000000 : ℝ)) (Y := (87126672273149/100000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (65339607/70193411 : ℝ) ^ p + (1182625228/1193287987 : ℝ) ^ p := by
    exact cert_lt (x := (65339607/70193411 : ℝ)) (y := (1182625228/1193287987 : ℝ)) (X := (18857819604109/100000000000000 : ℝ)) (Y := (16228436196307/20000000000000 : ℝ)) 745 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496319687/500000000 : ℝ)) (U := (1193287987/1000000000 : ℝ)) (Ab := (33088529/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (923809059/1000000000 : ℝ)) (σ := (496319687/500000000 : ℝ)) (Ab := (1110773319/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab072
