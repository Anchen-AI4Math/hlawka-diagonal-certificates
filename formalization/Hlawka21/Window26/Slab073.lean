import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 73, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab073 (p : ℝ) (hpa : (489/16 : ℝ) ≤ p) (hpb : p ≤ (245/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1426803954433/108313500000000 : ℝ) (6737541/1000000000 : ℝ) (3200000649881/21662700000000 : ℝ) (591/500 : ℝ) (977620837/500000000 : ℝ) (977575587/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (11581427/10000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10917/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5619/10000 : ℝ)
      else (2069/2500 : ℝ) ≤ X j i ∧ X j i ≤ (719/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1426803954433/108313500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6737541/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (943617653/1000000000 : ℝ) ^ p + (993969641/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943617653/1000000000 : ℝ)) (y := (993969641/1000000000 : ℝ)) (X := (8454720388157/50000000000000 : ℝ)) (Y := (20772645253097/25000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993969641/1000000000 : ℝ) ^ p + (943617653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993969641/1000000000 : ℝ)) (y := (943617653/1000000000 : ℝ)) (X := (20772645253097/25000000000000 : ℝ)) (Y := (8454720388157/50000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (968793647/500000000 : ℝ)) (τ := (943617653/1000000000 : ℝ)) (σ := (993969641/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (275818421/290159016 : ℝ) ^ p + (287913169/290159016 : ℝ) ^ p := by
    exact cert_lt (x := (275818421/290159016 : ℝ)) (y := (287913169/290159016 : ℝ)) (X := (21176683339651/100000000000000 : ℝ)) (Y := (78823317848239/100000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (943617653/1000000000 : ℝ)) (n' := (108809631/125000000 : ℝ)) (Ab := (827455263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (473382671/500000000 : ℝ) ^ p + (496626427/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (473382671/500000000 : ℝ)) (y := (496626427/500000000 : ℝ)) (X := (9362504019767/50000000000000 : ℝ)) (Y := (16255002212369/20000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496626427/500000000 : ℝ) ^ p + (473382671/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496626427/500000000 : ℝ)) (y := (473382671/500000000 : ℝ)) (X := (16255002212369/20000000000000 : ℝ)) (Y := (9362504019767/50000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (485004549/250000000 : ℝ)) (τ := (473382671/500000000 : ℝ)) (σ := (496626427/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (830764048/874062193 : ℝ) ^ p + (867324652/874062193 : ℝ) ^ p := by
    exact cert_lt (x := (830764048/874062193 : ℝ)) (y := (867324652/874062193 : ℝ)) (X := (21099411784533/100000000000000 : ℝ)) (Y := (78900589406961/100000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (473382671/500000000 : ℝ)) (n' := (874062193/1000000000 : ℝ)) (Ab := (51922753/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (946847239/1000000000 : ℝ) ^ p + (248308257/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (946847239/1000000000 : ℝ)) (y := (248308257/250000000 : ℝ)) (X := (4693669114183/25000000000000 : ℝ)) (Y := (40612671339869/50000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248308257/250000000 : ℝ) ^ p + (946847239/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248308257/250000000 : ℝ)) (y := (946847239/1000000000 : ℝ)) (X := (40612671339869/50000000000000 : ℝ)) (Y := (4693669114183/25000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1940080267/1000000000 : ℝ)) (τ := (946847239/1000000000 : ℝ)) (σ := (248308257/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (830849985/874155314 : ℝ) ^ p + (867417773/874155314 : ℝ) ^ p := by
    exact cert_lt (x := (830849985/874155314 : ℝ)) (y := (867417773/874155314 : ℝ)) (X := (2637176536051/12500000000000 : ℝ)) (Y := (78902588994529/100000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (946847239/1000000000 : ℝ)) (n' := (437077657/500000000 : ℝ)) (Ab := (166169997/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (946849357/1000000000 : ℝ) ^ p + (198646503/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (946849357/1000000000 : ℝ)) (y := (198646503/200000000 : ℝ)) (X := (234699533227/1250000000000 : ℝ)) (Y := (2538251809203/3125000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198646503/200000000 : ℝ) ^ p + (946849357/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198646503/200000000 : ℝ)) (y := (946849357/1000000000 : ℝ)) (X := (2538251809203/3125000000000 : ℝ)) (Y := (234699533227/1250000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (121255117/62500000 : ℝ)) (τ := (946849357/1000000000 : ℝ)) (σ := (198646503/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (830852207/874157722 : ℝ) ^ p + (867420181/874157722 : ℝ) ^ p := by
    exact cert_lt (x := (830852207/874157722 : ℝ)) (y := (867420181/874157722 : ℝ)) (X := (21097360412869/100000000000000 : ℝ)) (Y := (78902640696521/100000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (946849357/1000000000 : ℝ)) (n' := (437078861/500000000 : ℝ)) (Ab := (830852207/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (946849413/1000000000 : ℝ) ^ p + (993232501/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946849413/1000000000 : ℝ)) (y := (993232501/1000000000 : ℝ)) (X := (18775996666531/100000000000000 : ℝ)) (Y := (40612011416203/50000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993232501/1000000000 : ℝ) ^ p + (946849413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993232501/1000000000 : ℝ)) (y := (946849413/1000000000 : ℝ)) (X := (40612011416203/50000000000000 : ℝ)) (Y := (18775996666531/100000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (970040957/500000000 : ℝ)) (τ := (946849413/1000000000 : ℝ)) (σ := (993232501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (415426133/437078893 : ℝ) ^ p + (867420245/874157786 : ℝ) ^ p := by
    exact cert_lt (x := (415426133/437078893 : ℝ)) (y := (867420245/874157786 : ℝ)) (X := (10548679495101/50000000000000 : ℝ)) (Y := (78902642070657/100000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (946849413/1000000000 : ℝ)) (n' := (437078893/500000000 : ℝ)) (Ab := (415426133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (473424707/500000000 : ℝ) ^ p + (993232501/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (473424707/500000000 : ℝ)) (y := (993232501/1000000000 : ℝ)) (X := (586749914807/3125000000000 : ℝ)) (Y := (40612011416203/50000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993232501/1000000000 : ℝ) ^ p + (473424707/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993232501/1000000000 : ℝ)) (y := (473424707/500000000 : ℝ)) (X := (40612011416203/50000000000000 : ℝ)) (Y := (586749914807/3125000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (388016383/200000000 : ℝ)) (τ := (473424707/500000000 : ℝ)) (σ := (993232501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (830852267/874157787 : ℝ) ^ p + (289140082/291385929 : ℝ) ^ p := by
    exact cert_lt (x := (830852267/874157787 : ℝ)) (y := (289140082/291385929 : ℝ)) (X := (10548679514363/50000000000000 : ℝ)) (Y := (2465707565379/3125000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (473424707/500000000 : ℝ)) (n' := (874157787/1000000000 : ℝ)) (Ab := (830852267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (388016383/200000000 : ℝ)) (τ := (473424707/500000000 : ℝ)) (σ := (993232501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (473424707/500000000 : ℝ)) (n' := (874157787/1000000000 : ℝ)) (Ab := (830852267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (388016383/200000000 : ℝ)) (τ := (473424707/500000000 : ℝ)) (σ := (993232501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (473424707/500000000 : ℝ)) (n' := (874157787/1000000000 : ℝ)) (Ab := (830852267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (388016383/200000000 : ℝ)) (τ := (473424707/500000000 : ℝ)) (σ := (993232501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (473424707/500000000 : ℝ)) (n' := (874157787/1000000000 : ℝ)) (Ab := (830852267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (388016383/200000000 : ℝ)) (τ := (473424707/500000000 : ℝ)) (σ := (993232501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (473424707/500000000 : ℝ)) (n' := (874157787/1000000000 : ℝ)) (Ab := (830852267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (388016383/200000000 : ℝ)) (τ := (473424707/500000000 : ℝ)) (σ := (993232501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (855896119/920928650 : ℝ) ^ p + (1835119759/1841857300 : ℝ) ^ p := by
    exact cert_lt (x := (855896119/920928650 : ℝ)) (y := (1835119759/1841857300 : ℝ)) (X := (10616322736419/100000000000000 : ℝ)) (Y := (2234591940163/2500000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1091671981/1158142700 : ℝ) ^ p + (1151405159/1158142700 : ℝ) ^ p := by
    exact cert_lt (x := (1091671981/1158142700 : ℝ)) (y := (1151405159/1158142700 : ℝ)) (X := (3272570363721/20000000000000 : ℝ)) (Y := (1672742975749/2000000000000 : ℝ)) 245 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993232501/1000000000 : ℝ)) (U := (11581427/10000000 : ℝ)) (Ab := (855896119/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (473424707/500000000 : ℝ)) (σ := (993232501/1000000000 : ℝ)) (Ab := (1091671981/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab073
