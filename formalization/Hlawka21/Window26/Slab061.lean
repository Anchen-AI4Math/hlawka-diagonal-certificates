import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 61, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab061 (p : ℝ) (hpa : (477/16 : ℝ) ≤ p) (hpb : p ≤ (239/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1430944820737/105655500000000 : ℝ) (3465519/500000000 : ℝ) (3200000633933/21131100000000 : ℝ) (591/500 : ℝ) (244266377/125000000 : ℝ) (977017983/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289429217/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5449/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5597/10000 : ℝ)
      else (4127/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5749/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1430944820737/105655500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3465519/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (471068091/500000000 : ℝ) ^ p + (993841789/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471068091/500000000 : ℝ)) (y := (993841789/1000000000 : ℝ)) (X := (16851799186039/100000000000000 : ℝ)) (Y := (41574110596751/50000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993841789/1000000000 : ℝ) ^ p + (471068091/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993841789/1000000000 : ℝ)) (y := (471068091/500000000 : ℝ)) (X := (41574110596751/50000000000000 : ℝ)) (Y := (16851799186039/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1935977971/1000000000 : ℝ)) (τ := (471068091/500000000 : ℝ)) (σ := (993841789/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (412704252/434650463 : ℝ) ^ p + (431184944/434650463 : ℝ) ^ p := by
    exact cert_lt (x := (412704252/434650463 : ℝ)) (y := (431184944/434650463 : ℝ)) (X := (21270443885207/100000000000000 : ℝ)) (Y := (492059731929/625000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (471068091/500000000 : ℝ)) (n' := (434650463/500000000 : ℝ)) (Ab := (103176063/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (472671139/500000000 : ℝ) ^ p + (248278483/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (472671139/500000000 : ℝ)) (y := (248278483/250000000 : ℝ)) (X := (9325965405861/50000000000000 : ℝ)) (Y := (81348088048873/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248278483/250000000 : ℝ) ^ p + (472671139/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248278483/250000000 : ℝ)) (y := (472671139/500000000 : ℝ)) (X := (81348088048873/100000000000000 : ℝ)) (Y := (9325965405861/50000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (193845621/100000000 : ℝ)) (τ := (472671139/500000000 : ℝ)) (σ := (248278483/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (828779934/872960761 : ℝ) ^ p + (866029723/872960761 : ℝ) ^ p := by
    exact cert_lt (x := (828779934/872960761 : ℝ)) (y := (866029723/872960761 : ℝ)) (X := (4238230513693/20000000000000 : ℝ)) (Y := (78808848947823/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (472671139/500000000 : ℝ)) (n' := (872960761/1000000000 : ℝ)) (Ab := (414389967/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (236357091/250000000 : ℝ) ^ p + (993093163/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236357091/250000000 : ℝ)) (y := (993093163/1000000000 : ℝ)) (X := (374054809329/2000000000000 : ℝ)) (Y := (40648639524033/50000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993093163/1000000000 : ℝ) ^ p + (236357091/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993093163/1000000000 : ℝ)) (y := (236357091/250000000 : ℝ)) (X := (40648639524033/50000000000000 : ℝ)) (Y := (374054809329/2000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1938521527/1000000000 : ℝ)) (τ := (236357091/250000000 : ℝ)) (σ := (993093163/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (207217574/218264715 : ℝ) ^ p + (144354637/145509810 : ℝ) ^ p := by
    exact cert_lt (x := (207217574/218264715 : ℝ)) (y := (144354637/145509810 : ℝ)) (X := (21189035306589/100000000000000 : ℝ)) (Y := (39405483106063/50000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (236357091/250000000 : ℝ)) (n' := (43652943/50000000 : ℝ)) (Ab := (103608787/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (118178833/125000000 : ℝ) ^ p + (993092607/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (118178833/125000000 : ℝ)) (y := (993092607/1000000000 : ℝ)) (X := (18704099804969/100000000000000 : ℝ)) (Y := (81295919278823/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993092607/1000000000 : ℝ) ^ p + (118178833/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993092607/1000000000 : ℝ)) (y := (118178833/125000000 : ℝ)) (X := (81295919278823/100000000000000 : ℝ)) (Y := (18704099804969/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1938523271/1000000000 : ℝ)) (τ := (118178833/125000000 : ℝ)) (σ := (993092607/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (828872710/873061481 : ℝ) ^ p + (866130443/873061481 : ℝ) ^ p := by
    exact cert_lt (x := (828872710/873061481 : ℝ)) (y := (866130443/873061481 : ℝ)) (X := (21188978530561/100000000000000 : ℝ)) (Y := (39405511387613/50000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (118178833/125000000 : ℝ)) (n' := (873061481/1000000000 : ℝ)) (Ab := (82887271/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (236357681/250000000 : ℝ) ^ p + (993092593/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236357681/250000000 : ℝ)) (y := (993092593/1000000000 : ℝ)) (X := (4676033816813/25000000000000 : ℝ)) (Y := (81295885040313/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993092593/1000000000 : ℝ) ^ p + (236357681/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993092593/1000000000 : ℝ)) (y := (236357681/250000000 : ℝ)) (X := (81295885040313/100000000000000 : ℝ)) (Y := (4676033816813/25000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1938523317/1000000000 : ℝ)) (τ := (236357681/250000000 : ℝ)) (σ := (993092593/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (828872773/873061550 : ℝ) ^ p + (433065256/436530775 : ℝ) ^ p := by
    exact cert_lt (x := (828872773/873061550 : ℝ)) (y := (433065256/436530775 : ℝ)) (X := (21188976615427/100000000000000 : ℝ)) (Y := (19702756066073/25000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (236357681/250000000 : ℝ)) (n' := (17461231/20000000 : ℝ)) (Ab := (828872773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (472715363/500000000 : ℝ) ^ p + (62068287/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (472715363/500000000 : ℝ)) (y := (62068287/62500000 : ℝ)) (X := (18704136449329/100000000000000 : ℝ)) (Y := (16259176518941/20000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (62068287/62500000 : ℝ) ^ p + (472715363/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62068287/62500000 : ℝ)) (y := (472715363/500000000 : ℝ)) (X := (16259176518941/20000000000000 : ℝ)) (Y := (18704136449329/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (969261659/500000000 : ℝ)) (τ := (472715363/500000000 : ℝ)) (σ := (62068287/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (828872775/873061552 : ℝ) ^ p + (433065257/436530776 : ℝ) ^ p := by
    exact cert_lt (x := (828872775/873061552 : ℝ)) (y := (433065257/436530776 : ℝ)) (X := (4237795338547/20000000000000 : ℝ)) (Y := (39405512153727/50000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (472715363/500000000 : ℝ)) (n' := (54566347/62500000 : ℝ)) (Ab := (33154911/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (969261659/500000000 : ℝ)) (τ := (472715363/500000000 : ℝ)) (σ := (62068287/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (472715363/500000000 : ℝ)) (n' := (54566347/62500000 : ℝ)) (Ab := (33154911/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (969261659/500000000 : ℝ)) (τ := (472715363/500000000 : ℝ)) (σ := (62068287/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (472715363/500000000 : ℝ)) (n' := (54566347/62500000 : ℝ)) (Ab := (33154911/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (969261659/500000000 : ℝ)) (τ := (472715363/500000000 : ℝ)) (σ := (62068287/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (472715363/500000000 : ℝ)) (n' := (54566347/62500000 : ℝ)) (Ab := (33154911/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (969261659/500000000 : ℝ)) (τ := (472715363/500000000 : ℝ)) (σ := (62068287/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (472715363/500000000 : ℝ)) (n' := (54566347/62500000 : ℝ)) (Ab := (33154911/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (969261659/500000000 : ℝ)) (τ := (472715363/500000000 : ℝ)) (σ := (62068287/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (427305907/460570783 : ℝ) ^ p + (917676047/921141566 : ℝ) ^ p := by
    exact cert_lt (x := (427305907/460570783 : ℝ)) (y := (917676047/921141566 : ℝ)) (X := (10649888199391/100000000000000 : ℝ)) (Y := (89350111997711/100000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1089784819/1157716868 : ℝ) ^ p + (575392915/578858434 : ℝ) ^ p := by
    exact cert_lt (x := (1089784819/1157716868 : ℝ)) (y := (575392915/578858434 : ℝ)) (X := (16422318965029/100000000000000 : ℝ)) (Y := (41788840832753/50000000000000 : ℝ)) 239 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (62068287/62500000 : ℝ)) (U := (289429217/250000000 : ℝ)) (Ab := (427305907/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (472715363/500000000 : ℝ)) (σ := (62068287/62500000 : ℝ)) (Ab := (1089784819/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab061
