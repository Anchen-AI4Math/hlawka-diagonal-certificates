import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 136, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab136 (p : ℝ) (hpa : (101/4 : ℝ) ≤ p) (hpb : p ≤ (809/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (260134669843/13786500000000 : ℝ) (4848487/500000000 : ℝ) (500000082719/2757300000000 : ℝ) (3033/2500 : ℝ) (486477503/250000000 : ℝ) (972921991/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (4664457/3906250 : ℝ)) ∧
    (∀ j i, if j = i then -(5587/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1167/2500 : ℝ)
      else (7817/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (260134669843/13786500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4848487/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (462335761/500000000 : ℝ) ^ p + (994139799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462335761/500000000 : ℝ)) (y := (994139799/1000000000 : ℝ)) (X := (13807690401913/100000000000000 : ℝ)) (Y := (17238465614441/20000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994139799/1000000000 : ℝ) ^ p + (462335761/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (994139799/1000000000 : ℝ)) (y := (462335761/500000000 : ℝ)) (X := (17238465614441/20000000000000 : ℝ)) (Y := (13807690401913/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1918811321/1000000000 : ℝ)) (τ := (462335761/500000000 : ℝ)) (σ := (994139799/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (789938635/833675234 : ℝ) ^ p + (58855590/59548231 : ℝ) ^ p := by
    exact cert_lt (x := (789938635/833675234 : ℝ)) (y := (58855590/59548231 : ℝ)) (X := (25605256481811/100000000000000 : ℝ)) (Y := (9299343104317/12500000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462335761/500000000 : ℝ)) (n' := (416837617/500000000 : ℝ)) (Ab := (157987727/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (930085161/1000000000 : ℝ) ^ p + (19862511/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (930085161/1000000000 : ℝ)) (y := (19862511/20000000 : ℝ)) (X := (1600349731109/10000000000000 : ℝ)) (Y := (83996520347321/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (19862511/20000000 : ℝ) ^ p + (930085161/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19862511/20000000 : ℝ)) (y := (930085161/1000000000 : ℝ)) (X := (83996520347321/100000000000000 : ℝ)) (Y := (1600349731109/10000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1923210711/1000000000 : ℝ)) (τ := (930085161/1000000000 : ℝ)) (σ := (19862511/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (795754547/840031413 : ℝ) ^ p + (830334439/840031413 : ℝ) ^ p := by
    exact cert_lt (x := (795754547/840031413 : ℝ)) (y := (830334439/840031413 : ℝ)) (X := (25437595956463/100000000000000 : ℝ)) (Y := (3728120280187/5000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (930085161/1000000000 : ℝ)) (n' := (840031413/1000000000 : ℝ)) (Ab := (795754547/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (930300341/1000000000 : ℝ) ^ p + (993081627/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (930300341/1000000000 : ℝ)) (y := (993081627/1000000000 : ℝ)) (X := (3219472862899/20000000000000 : ℝ)) (Y := (20975663252183/25000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993081627/1000000000 : ℝ) ^ p + (930300341/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993081627/1000000000 : ℝ)) (y := (930300341/1000000000 : ℝ)) (X := (20975663252183/25000000000000 : ℝ)) (Y := (3219472862899/20000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (120211373/62500000 : ℝ)) (τ := (930300341/1000000000 : ℝ)) (σ := (993081627/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795984993/840283306 : ℝ) ^ p + (415293166/420141653 : ℝ) ^ p := by
    exact cert_lt (x := (795984993/840283306 : ℝ)) (y := (415293166/420141653 : ℝ)) (X := (12715498028733/50000000000000 : ℝ)) (Y := (37284502547489/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (930300341/1000000000 : ℝ)) (n' := (420141653/500000000 : ℝ)) (Ab := (795984993/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (116288601/125000000 : ℝ) ^ p + (993079893/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116288601/125000000 : ℝ)) (y := (993079893/1000000000 : ℝ)) (X := (16101068627571/100000000000000 : ℝ)) (Y := (8389894936523/10000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993079893/1000000000 : ℝ) ^ p + (116288601/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993079893/1000000000 : ℝ)) (y := (116288601/125000000 : ℝ)) (X := (8389894936523/10000000000000 : ℝ)) (Y := (16101068627571/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1923388701/1000000000 : ℝ)) (τ := (116288601/125000000 : ℝ)) (σ := (993079893/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (113713437/120041888 : ℝ) ^ p + (59328303/60020944 : ℝ) ^ p := by
    exact cert_lt (x := (113713437/120041888 : ℝ)) (y := (59328303/60020944 : ℝ)) (X := (25430736332357/100000000000000 : ℝ)) (Y := (14913852932681/20000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (116288601/125000000 : ℝ)) (n' := (26259163/31250000 : ℝ)) (Ab := (795994059/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (930309141/1000000000 : ℝ) ^ p + (39723193/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (930309141/1000000000 : ℝ)) (y := (39723193/40000000 : ℝ)) (X := (8050607165913/50000000000000 : ℝ)) (Y := (20974701031877/25000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39723193/40000000 : ℝ) ^ p + (930309141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39723193/40000000 : ℝ)) (y := (930309141/1000000000 : ℝ)) (X := (20974701031877/25000000000000 : ℝ)) (Y := (8050607165913/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961694483/500000000 : ℝ)) (τ := (930309141/1000000000 : ℝ)) (σ := (39723193/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (397997208/420146803 : ℝ) ^ p + (415298316/420146803 : ℝ) ^ p := by
    exact cert_lt (x := (397997208/420146803 : ℝ)) (y := (415298316/420146803 : ℝ)) (X := (5086145256973/20000000000000 : ℝ)) (Y := (37284637439201/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (930309141/1000000000 : ℝ)) (n' := (420146803/500000000 : ℝ)) (Ab := (49749651/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186061831/200000000 : ℝ) ^ p + (496539911/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (186061831/200000000 : ℝ)) (y := (496539911/500000000 : ℝ)) (X := (8050610228779/50000000000000 : ℝ)) (Y := (83898797719967/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496539911/500000000 : ℝ) ^ p + (186061831/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496539911/500000000 : ℝ)) (y := (186061831/200000000 : ℝ)) (X := (83898797719967/100000000000000 : ℝ)) (Y := (8050610228779/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795994432/840293623 : ℝ) ^ p + (830596649/840293623 : ℝ) ^ p := by
    exact cert_lt (x := (795994432/840293623 : ℝ)) (y := (830596649/840293623 : ℝ)) (X := (25430726201041/100000000000000 : ℝ)) (Y := (74569275323671/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1664483075/1805899008 : ℝ) ^ p + (898101017/902949504 : ℝ) ^ p := by
    exact cert_lt (x := (1664483075/1805899008 : ℝ)) (y := (898101017/902949504 : ℝ)) (X := (12725882000609/100000000000000 : ℝ)) (Y := (87274118343191/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (62072621/66338944 : ℝ) ^ p + (84600287/85292928 : ℝ) ^ p := by
    exact cert_lt (x := (62072621/66338944 : ℝ)) (y := (84600287/85292928 : ℝ)) (X := (18628118224419/100000000000000 : ℝ)) (Y := (20342970637083/25000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496539911/500000000 : ℝ)) (U := (4664457/3906250 : ℝ)) (Ab := (66579323/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ)) (Ab := (558653589/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab136
