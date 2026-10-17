import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 43, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab043 (p : ℝ) (hpa : (459/16 : ℝ) ≤ p) (hpb : p ≤ (115/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (179694845417/12708562500000 : ℝ) (452671/62500000 : ℝ) (3200000610011/20333700000000 : ℝ) (591/500 : ℝ) (195235769/100000000 : ℝ) (97612757/100000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (36157933/31250000 : ℝ)) ∧
    (∀ j i, if j = i then -(10869/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5561/10000 : ℝ)
      else (8217/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11489/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (179694845417/12708562500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (452671/62500000 : ℝ) := by norm_num
  have pc0 : 1 < (469881233/500000000 : ℝ) ^ p + (124204973/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (469881233/500000000 : ℝ)) (y := (124204973/125000000 : ℝ)) (X := (8379927205831/50000000000000 : ℝ)) (Y := (4162008301077/5000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124204973/125000000 : ℝ) ^ p + (469881233/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124204973/125000000 : ℝ)) (y := (469881233/500000000 : ℝ)) (X := (4162008301077/5000000000000 : ℝ)) (Y := (8379927205831/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (7733609/4000000 : ℝ)) (τ := (469881233/500000000 : ℝ)) (σ := (124204973/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (822137357/867399885 : ℝ) ^ p + (860157149/867399885 : ℝ) ^ p := by
    exact cert_lt (x := (822137357/867399885 : ℝ)) (y := (860157149/867399885 : ℝ)) (X := (21421229315409/100000000000000 : ℝ)) (Y := (15715754349837/20000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (469881233/500000000 : ℝ)) (n' := (173479977/200000000 : ℝ)) (Ab := (822137357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (943058839/1000000000 : ℝ) ^ p + (992895091/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943058839/1000000000 : ℝ)) (y := (992895091/1000000000 : ℝ)) (X := (9267449217479/50000000000000 : ℝ)) (Y := (40732559893817/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992895091/1000000000 : ℝ) ^ p + (943058839/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992895091/1000000000 : ℝ)) (y := (943058839/1000000000 : ℝ)) (X := (40732559893817/50000000000000 : ℝ)) (Y := (9267449217479/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (193595393/100000000 : ℝ)) (τ := (943058839/1000000000 : ℝ)) (σ := (992895091/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (825605857/871176262 : ℝ) ^ p + (431966763/435588131 : ℝ) ^ p := by
    exact cert_lt (x := (825605857/871176262 : ℝ)) (y := (431966763/435588131 : ℝ)) (X := (21338728997043/100000000000000 : ℝ)) (Y := (1966531809207/2500000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (943058839/1000000000 : ℝ)) (n' := (435588131/500000000 : ℝ)) (Ab := (825605857/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (14736747/15625000 : ℝ) ^ p + (62054549/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (14736747/15625000 : ℝ)) (y := (62054549/62500000 : ℝ)) (X := (9293751388109/50000000000000 : ℝ)) (Y := (20353129152517/25000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (62054549/62500000 : ℝ) ^ p + (14736747/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (62054549/62500000 : ℝ)) (y := (14736747/15625000 : ℝ)) (X := (20353129152517/25000000000000 : ℝ)) (Y := (9293751388109/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (121001537/62500000 : ℝ)) (τ := (14736747/15625000 : ℝ)) (σ := (62054549/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (825703498/871282579 : ℝ) ^ p + (864039843/871282579 : ℝ) ^ p := by
    exact cert_lt (x := (825703498/871282579 : ℝ)) (y := (864039843/871282579 : ℝ)) (X := (10668207485259/50000000000000 : ℝ)) (Y := (39331792938101/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (14736747/15625000 : ℝ)) (n' := (871282579/1000000000 : ℝ)) (Ab := (412851749/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (58947151/62500000 : ℝ) ^ p + (992872157/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (58947151/62500000 : ℝ)) (y := (992872157/1000000000 : ℝ)) (X := (18588980528177/100000000000000 : ℝ)) (Y := (3256441541037/4000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992872157/1000000000 : ℝ) ^ p + (58947151/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992872157/1000000000 : ℝ)) (y := (58947151/62500000 : ℝ)) (X := (3256441541037/4000000000000 : ℝ)) (Y := (18588980528177/100000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1936026573/1000000000 : ℝ)) (τ := (58947151/62500000 : ℝ)) (σ := (992872157/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (58979017/62234683 : ℝ) ^ p + (432021413/435642781 : ℝ) ^ p := by
    exact cert_lt (x := (58979017/62234683 : ℝ)) (y := (432021413/435642781 : ℝ)) (X := (21336350373899/100000000000000 : ℝ)) (Y := (78663650780489/100000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (58947151/62500000 : ℝ)) (n' := (435642781/500000000 : ℝ)) (Ab := (412853119/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (94315449/100000000 : ℝ) ^ p + (992872139/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94315449/100000000 : ℝ)) (y := (992872139/1000000000 : ℝ)) (X := (1858902245991/10000000000000 : ℝ)) (Y := (8141099609327/10000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992872139/1000000000 : ℝ) ^ p + (94315449/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992872139/1000000000 : ℝ)) (y := (94315449/100000000 : ℝ)) (X := (8141099609327/10000000000000 : ℝ)) (Y := (1858902245991/10000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1936026629/1000000000 : ℝ)) (τ := (94315449/100000000 : ℝ)) (σ := (992872139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (117958045/124469378 : ℝ) ^ p + (432021455/435642823 : ℝ) ^ p := by
    exact cert_lt (x := (117958045/124469378 : ℝ)) (y := (432021455/435642823 : ℝ)) (X := (5334087109523/25000000000000 : ℝ)) (Y := (491647828801/625000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (94315449/100000000 : ℝ)) (n' := (435642823/500000000 : ℝ)) (Ab := (165141263/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (943154491/1000000000 : ℝ) ^ p + (992872139/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943154491/1000000000 : ℝ)) (y := (992872139/1000000000 : ℝ)) (X := (3717804605311/20000000000000 : ℝ)) (Y := (8141099609327/10000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992872139/1000000000 : ℝ) ^ p + (943154491/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992872139/1000000000 : ℝ)) (y := (943154491/1000000000 : ℝ)) (X := (8141099609327/10000000000000 : ℝ)) (Y := (3717804605311/20000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (193602663/100000000 : ℝ)) (τ := (943154491/1000000000 : ℝ)) (σ := (992872139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (825706316/871285647 : ℝ) ^ p + (864042911/871285647 : ℝ) ^ p := by
    exact cert_lt (x := (825706316/871285647 : ℝ)) (y := (864042911/871285647 : ℝ)) (X := (4267269695391/20000000000000 : ℝ)) (Y := (39331826314959/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (943154491/1000000000 : ℝ)) (n' := (871285647/1000000000 : ℝ)) (Ab := (206426579/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (193602663/100000000 : ℝ)) (τ := (943154491/1000000000 : ℝ)) (σ := (992872139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (943154491/1000000000 : ℝ)) (n' := (871285647/1000000000 : ℝ)) (Ab := (206426579/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (193602663/100000000 : ℝ)) (τ := (943154491/1000000000 : ℝ)) (σ := (992872139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (943154491/1000000000 : ℝ)) (n' := (871285647/1000000000 : ℝ)) (Ab := (206426579/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (193602663/100000000 : ℝ)) (τ := (943154491/1000000000 : ℝ)) (σ := (992872139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (943154491/1000000000 : ℝ)) (n' := (871285647/1000000000 : ℝ)) (Ab := (206426579/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (193602663/100000000 : ℝ)) (τ := (943154491/1000000000 : ℝ)) (σ := (992872139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (943154491/1000000000 : ℝ)) (n' := (871285647/1000000000 : ℝ)) (Ab := (206426579/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (193602663/100000000 : ℝ)) (τ := (943154491/1000000000 : ℝ)) (σ := (992872139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (852564451/921473072 : ℝ) ^ p + (114731463/115184134 : ℝ) ^ p := by
    exact cert_lt (x := (852564451/921473072 : ℝ)) (y := (114731463/115184134 : ℝ)) (X := (10703638550899/100000000000000 : ℝ)) (Y := (44648180882571/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1086804451/1157053856 : ℝ) ^ p + (71863195/72315866 : ℝ) ^ p := by
    exact cert_lt (x := (1086804451/1157053856 : ℝ)) (y := (71863195/72315866 : ℝ)) (X := (16517249870419/100000000000000 : ℝ)) (Y := (41741375364087/50000000000000 : ℝ)) 115 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992872139/1000000000 : ℝ)) (U := (36157933/31250000 : ℝ)) (Ab := (852564451/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (943154491/1000000000 : ℝ)) (σ := (992872139/1000000000 : ℝ)) (Ab := (1086804451/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab043
