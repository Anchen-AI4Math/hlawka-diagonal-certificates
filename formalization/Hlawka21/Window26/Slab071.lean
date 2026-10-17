import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 71, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab071 (p : ℝ) (hpa : (487/16 : ℝ) ≤ p) (hpb : p ≤ (61/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (713740157879/53935250000000 : ℝ) (846131/125000000 : ℝ) (3200000647223/21574100000000 : ℝ) (591/500 : ℝ) (977530157/500000000 : ℝ) (48874227/50000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144759077/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5457/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(351/625 : ℝ)
      else (8273/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11503/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (713740157879/53935250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (846131/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (188675203/200000000 : ℝ) ^ p + (496974347/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (188675203/200000000 : ℝ)) (y := (496974347/500000000 : ℝ)) (X := (16900024069471/100000000000000 : ℝ)) (Y := (83099996584161/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496974347/500000000 : ℝ) ^ p + (188675203/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496974347/500000000 : ℝ)) (y := (188675203/200000000 : ℝ)) (X := (83099996584161/100000000000000 : ℝ)) (Y := (16900024069471/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1937324709/1000000000 : ℝ)) (τ := (188675203/200000000 : ℝ)) (σ := (496974347/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (827121151/870285756 : ℝ) ^ p + (215879177/217571439 : ℝ) ^ p := by
    exact cert_lt (x := (827121151/870285756 : ℝ)) (y := (215879177/217571439 : ℝ)) (X := (2119196176643/10000000000000 : ℝ)) (Y := (78808039271883/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (188675203/200000000 : ℝ)) (n' := (217571439/250000000 : ℝ)) (Ab := (827121151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (118316667/125000000 : ℝ) ^ p + (993230073/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (118316667/125000000 : ℝ)) (y := (993230073/1000000000 : ℝ)) (X := (18713084435623/100000000000000 : ℝ)) (Y := (40643467609711/50000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993230073/1000000000 : ℝ) ^ p + (118316667/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993230073/1000000000 : ℝ)) (y := (118316667/125000000 : ℝ)) (X := (40643467609711/50000000000000 : ℝ)) (Y := (18713084435623/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1939763409/1000000000 : ℝ)) (τ := (118316667/125000000 : ℝ)) (σ := (993230073/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (830440259/873883182 : ℝ) ^ p + (433557067/436941591 : ℝ) ^ p := by
    exact cert_lt (x := (830440259/873883182 : ℝ)) (y := (433557067/436941591 : ℝ)) (X := (21114360021157/100000000000000 : ℝ)) (Y := (78885641184869/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (118316667/125000000 : ℝ)) (n' := (436941591/500000000 : ℝ)) (Ab := (830440259/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (946615911/1000000000 : ℝ) ^ p + (496605047/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (946615911/1000000000 : ℝ)) (y := (496605047/500000000 : ℝ)) (X := (4690735091651/25000000000000 : ℝ)) (Y := (8123707942671/10000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496605047/500000000 : ℝ) ^ p + (946615911/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496605047/500000000 : ℝ)) (y := (946615911/1000000000 : ℝ)) (X := (8123707942671/10000000000000 : ℝ)) (Y := (4690735091651/25000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (387965201/200000000 : ℝ)) (τ := (946615911/1000000000 : ℝ)) (σ := (496605047/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (830526911/873977107 : ℝ) ^ p + (867208059/873977107 : ℝ) ^ p := by
    exact cert_lt (x := (830526911/873977107 : ℝ)) (y := (867208059/873977107 : ℝ)) (X := (21112341178979/100000000000000 : ℝ)) (Y := (15777531943383/20000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (946615911/1000000000 : ℝ)) (n' := (873977107/1000000000 : ℝ)) (Ab := (830526911/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (47330903/50000000 : ℝ) ^ p + (993209573/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (47330903/50000000 : ℝ)) (y := (993209573/1000000000 : ℝ)) (X := (18764239572239/100000000000000 : ℝ)) (Y := (2030894492849/2500000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993209573/1000000000 : ℝ) ^ p + (47330903/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (993209573/1000000000 : ℝ)) (y := (47330903/50000000 : ℝ)) (X := (2030894492849/2500000000000 : ℝ)) (Y := (18764239572239/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1939827633/1000000000 : ℝ)) (τ := (47330903/50000000 : ℝ)) (σ := (993209573/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (830529166/873979551 : ℝ) ^ p + (867210503/873979551 : ℝ) ^ p := by
    exact cert_lt (x := (830529166/873979551 : ℝ)) (y := (867210503/873979551 : ℝ)) (X := (4222457769701/20000000000000 : ℝ)) (Y := (78887712235531/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (47330903/50000000 : ℝ)) (n' := (873979551/1000000000 : ℝ)) (Ab := (415264583/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (189323623/200000000 : ℝ) ^ p + (24830239/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (189323623/200000000 : ℝ)) (y := (24830239/25000000 : ℝ)) (X := (938213641217/5000000000000 : ℝ)) (Y := (16247149456753/20000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (24830239/25000000 : ℝ) ^ p + (189323623/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (24830239/25000000 : ℝ)) (y := (189323623/200000000 : ℝ)) (X := (16247149456753/20000000000000 : ℝ)) (Y := (938213641217/5000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (77593107/40000000 : ℝ)) (τ := (189323623/200000000 : ℝ)) (σ := (24830239/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (415264612/436989807 : ℝ) ^ p + (433605283/436989807 : ℝ) ^ p := by
    exact cert_lt (x := (415264612/436989807 : ℝ)) (y := (433605283/436989807 : ℝ)) (X := (1319517962517/6250000000000 : ℝ)) (Y := (39443856794661/50000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (189323623/200000000 : ℝ)) (n' := (436989807/500000000 : ℝ)) (Ab := (103816153/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (236654529/250000000 : ℝ) ^ p + (24830239/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (236654529/250000000 : ℝ)) (y := (24830239/25000000 : ℝ)) (X := (4691068357231/25000000000000 : ℝ)) (Y := (16247149456753/20000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (24830239/25000000 : ℝ) ^ p + (236654529/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (24830239/25000000 : ℝ)) (y := (236654529/250000000 : ℝ)) (X := (16247149456753/20000000000000 : ℝ)) (Y := (4691068357231/25000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (484956919/250000000 : ℝ)) (τ := (236654529/250000000 : ℝ)) (σ := (24830239/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (166105845/174795923 : ℝ) ^ p + (867210567/873979615 : ℝ) ^ p := by
    exact cert_lt (x := (166105845/174795923 : ℝ)) (y := (867210567/873979615 : ℝ)) (X := (21112287438817/100000000000000 : ℝ)) (Y := (7888771361081/10000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (236654529/250000000 : ℝ)) (n' := (174795923/200000000 : ℝ)) (Ab := (33221169/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (484956919/250000000 : ℝ)) (τ := (236654529/250000000 : ℝ)) (σ := (24830239/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (236654529/250000000 : ℝ)) (n' := (174795923/200000000 : ℝ)) (Ab := (33221169/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (484956919/250000000 : ℝ)) (τ := (236654529/250000000 : ℝ)) (σ := (24830239/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (236654529/250000000 : ℝ)) (n' := (174795923/200000000 : ℝ)) (Ab := (33221169/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (484956919/250000000 : ℝ)) (τ := (236654529/250000000 : ℝ)) (σ := (24830239/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (236654529/250000000 : ℝ)) (n' := (174795923/200000000 : ℝ)) (Ab := (33221169/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (484956919/250000000 : ℝ)) (τ := (236654529/250000000 : ℝ)) (σ := (24830239/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (236654529/250000000 : ℝ)) (n' := (174795923/200000000 : ℝ)) (Ab := (33221169/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (484956919/250000000 : ℝ)) (τ := (236654529/250000000 : ℝ)) (σ := (24830239/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1711372601/1841927384 : ℝ) ^ p + (20854072/20930993 : ℝ) ^ p := by
    exact cert_lt (x := (1711372601/1841927384 : ℝ)) (y := (20854072/20930993 : ℝ)) (X := (1062180042277/10000000000000 : ℝ)) (Y := (89378199874539/100000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (545681377/579036308 : ℝ) ^ p + (143912946/144759077 : ℝ) ^ p := by
    exact cert_lt (x := (545681377/579036308 : ℝ)) (y := (143912946/144759077 : ℝ)) (X := (8186282840783/50000000000000 : ℝ)) (Y := (8362743508369/10000000000000 : ℝ)) 61 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (24830239/25000000 : ℝ)) (U := (144759077/125000000 : ℝ)) (Ab := (1711372601/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (236654529/250000000 : ℝ)) (σ := (24830239/25000000 : ℝ)) (Ab := (545681377/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab071
