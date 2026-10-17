import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 76, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab076 (p : ℝ) (hpa : (123/4 : ℝ) ≤ p) (hpb : p ≤ (493/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (44556254483/3405562500000 : ℝ) (3345411/500000000 : ℝ) (800000163467/5448900000000 : ℝ) (591/500 : ℝ) (244438873/125000000 : ℝ) (488855393/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (579123591/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5461/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(703/1250 : ℝ)
      else (4141/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2301/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (44556254483/3405562500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3345411/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (943976273/1000000000 : ℝ) ^ p + (994000797/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943976273/1000000000 : ℝ)) (y := (994000797/1000000000 : ℝ)) (X := (1692342368487/10000000000000 : ℝ)) (Y := (83076597049433/100000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994000797/1000000000 : ℝ) ^ p + (943976273/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994000797/1000000000 : ℝ)) (y := (943976273/1000000000 : ℝ)) (X := (83076597049433/100000000000000 : ℝ)) (Y := (1692342368487/10000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193797707/100000000 : ℝ)) (τ := (943976273/1000000000 : ℝ)) (σ := (994000797/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (206987833/217690138 : ℝ) ^ p + (432034865/435380276 : ℝ) ^ p := by
    exact cert_lt (x := (206987833/217690138 : ℝ)) (y := (432034865/435380276 : ℝ)) (X := (5288506956573/25000000000000 : ℝ)) (Y := (39422986677729/50000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (943976273/1000000000 : ℝ)) (n' := (108845069/125000000 : ℝ)) (Ab := (206987833/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (947109587/1000000000 : ℝ) ^ p + (248321689/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (947109587/1000000000 : ℝ)) (y := (248321689/250000000 : ℝ)) (X := (9371350368183/50000000000000 : ℝ)) (Y := (81257319935067/100000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248321689/250000000 : ℝ) ^ p + (947109587/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248321689/250000000 : ℝ)) (y := (947109587/1000000000 : ℝ)) (X := (81257319935067/100000000000000 : ℝ)) (Y := (9371350368183/50000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1940396343/1000000000 : ℝ)) (τ := (947109587/1000000000 : ℝ)) (σ := (248321689/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (831244717/874327395 : ℝ) ^ p + (289212191/291442465 : ℝ) ^ p := by
    exact cert_lt (x := (831244717/874327395 : ℝ)) (y := (289212191/291442465 : ℝ)) (X := (2107724739599/10000000000000 : ℝ)) (Y := (39461376983057/50000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (947109587/1000000000 : ℝ)) (n' := (174865479/200000000 : ℝ)) (Ab := (831244717/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (947190483/1000000000 : ℝ) ^ p + (248316789/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (947190483/1000000000 : ℝ)) (y := (248316789/250000000 : ℝ)) (X := (18792090729549/100000000000000 : ℝ)) (Y := (81207929469429/100000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248316789/250000000 : ℝ) ^ p + (947190483/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248316789/250000000 : ℝ)) (y := (947190483/1000000000 : ℝ)) (X := (81207929469429/100000000000000 : ℝ)) (Y := (18792090729549/100000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1940457639/1000000000 : ℝ)) (τ := (947190483/1000000000 : ℝ)) (σ := (248316789/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (118761371/124917047 : ℝ) ^ p + (867728507/874419329 : ℝ) ^ p := by
    exact cert_lt (x := (118761371/124917047 : ℝ)) (y := (867728507/874419329 : ℝ)) (X := (21075275771551/100000000000000 : ℝ)) (Y := (1973118140701/2500000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (947190483/1000000000 : ℝ)) (n' := (874419329/1000000000 : ℝ)) (Ab := (831329597/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (11839907/12500000 : ℝ) ^ p + (248316663/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (11839907/12500000 : ℝ)) (y := (248316663/250000000 : ℝ)) (X := (1879336047131/10000000000000 : ℝ)) (Y := (40603329906011/50000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248316663/250000000 : ℝ) ^ p + (11839907/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (248316663/250000000 : ℝ)) (y := (11839907/12500000 : ℝ)) (X := (40603329906011/50000000000000 : ℝ)) (Y := (1879336047131/10000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (485114803/250000000 : ℝ)) (τ := (11839907/12500000 : ℝ)) (σ := (248316663/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (831331776/874421689 : ℝ) ^ p + (867730867/874421689 : ℝ) ^ p := by
    exact cert_lt (x := (831331776/874421689 : ℝ)) (y := (867730867/874421689 : ℝ)) (X := (21075225229353/100000000000000 : ℝ)) (Y := (78924776236933/100000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (11839907/12500000 : ℝ)) (n' := (874421689/1000000000 : ℝ)) (Ab := (12989559/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (473596307/500000000 : ℝ) ^ p + (993266639/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (473596307/500000000 : ℝ)) (y := (993266639/1000000000 : ℝ)) (X := (18793393484481/100000000000000 : ℝ)) (Y := (10150828382897/12500000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993266639/1000000000 : ℝ) ^ p + (473596307/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993266639/1000000000 : ℝ)) (y := (473596307/500000000 : ℝ)) (X := (10150828382897/12500000000000 : ℝ)) (Y := (18793393484481/100000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1940459253/1000000000 : ℝ)) (τ := (473596307/500000000 : ℝ)) (σ := (993266639/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (415665916/437210875 : ℝ) ^ p + (433865464/437210875 : ℝ) ^ p := by
    exact cert_lt (x := (415665916/437210875 : ℝ)) (y := (433865464/437210875 : ℝ)) (X := (84300894687/400000000000 : ℝ)) (Y := (78924777545041/100000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (473596307/500000000 : ℝ)) (n' := (3497687/4000000 : ℝ)) (Ab := (103916479/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (118399077/125000000 : ℝ) ^ p + (496633319/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (118399077/125000000 : ℝ)) (y := (496633319/500000000 : ℝ)) (X := (2349174338399/12500000000000 : ℝ)) (Y := (16241324908807/20000000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496633319/500000000 : ℝ) ^ p + (118399077/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496633319/500000000 : ℝ)) (y := (118399077/125000000 : ℝ)) (X := (16241324908807/20000000000000 : ℝ)) (Y := (2349174338399/12500000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (970229627/500000000 : ℝ)) (τ := (118399077/125000000 : ℝ)) (σ := (496633319/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (831331835/874421753 : ℝ) ^ p + (867730931/874421753 : ℝ) ^ p := by
    exact cert_lt (x := (831331835/874421753 : ℝ)) (y := (867730931/874421753 : ℝ)) (X := (21075223787229/100000000000000 : ℝ)) (Y := (5051185767/6400000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (118399077/125000000 : ℝ)) (n' := (874421753/1000000000 : ℝ)) (Ab := (166266367/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (970229627/500000000 : ℝ)) (τ := (118399077/125000000 : ℝ)) (σ := (496633319/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (118399077/125000000 : ℝ)) (n' := (874421753/1000000000 : ℝ)) (Ab := (166266367/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (970229627/500000000 : ℝ)) (τ := (118399077/125000000 : ℝ)) (σ := (496633319/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (118399077/125000000 : ℝ)) (n' := (874421753/1000000000 : ℝ)) (Ab := (166266367/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (970229627/500000000 : ℝ)) (τ := (118399077/125000000 : ℝ)) (σ := (496633319/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (118399077/125000000 : ℝ)) (n' := (874421753/1000000000 : ℝ)) (Ab := (166266367/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (970229627/500000000 : ℝ)) (τ := (118399077/125000000 : ℝ)) (σ := (496633319/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (118399077/125000000 : ℝ)) (n' := (874421753/1000000000 : ℝ)) (Ab := (166266367/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (970229627/500000000 : ℝ)) (τ := (118399077/125000000 : ℝ)) (σ := (496633319/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1712415545/1841752818 : ℝ) ^ p + (305843666/306958803 : ℝ) ^ p := by
    exact cert_lt (x := (1712415545/1841752818 : ℝ)) (y := (305843666/306958803 : ℝ)) (X := (265204900229/2500000000000 : ℝ)) (Y := (698373471137/781250000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1092131975/1158247182 : ℝ) ^ p + (6618140/6656593 : ℝ) ^ p := by
    exact cert_lt (x := (1092131975/1158247182 : ℝ)) (y := (6618140/6656593 : ℝ)) (X := (8174216350953/50000000000000 : ℝ)) (Y := (5228223007973/6250000000000 : ℝ)) 493 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496633319/500000000 : ℝ)) (U := (579123591/500000000 : ℝ)) (Ab := (342483109/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (118399077/125000000 : ℝ)) (σ := (496633319/500000000 : ℝ)) (Ab := (43685279/40000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab076
