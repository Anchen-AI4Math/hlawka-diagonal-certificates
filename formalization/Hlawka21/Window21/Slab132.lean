import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 132, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab132 (p : ℝ) (hpa : (201/8 : ℝ) ≤ p) (hpb : p ≤ (805/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (52057379147/2743650000000 : ℝ) (2438063/250000000 : ℝ) (1000000164619/5487300000000 : ℝ) (3033/2500 : ℝ) (15200351/7812500 : ℝ) (243197281/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194050413/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1117/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(2331/5000 : ℝ)
      else (7811/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5929/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (52057379147/2743650000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2438063/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (231069687/250000000 : ℝ) ^ p + (19882329/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (231069687/250000000 : ℝ)) (y := (19882329/20000000 : ℝ)) (X := (13795292030371/100000000000000 : ℝ)) (Y := (86204726634247/100000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (19882329/20000000 : ℝ) ^ p + (231069687/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (19882329/20000000 : ℝ)) (y := (231069687/250000000 : ℝ)) (X := (86204726634247/100000000000000 : ℝ)) (Y := (13795292030371/100000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (959197599/500000000 : ℝ)) (τ := (231069687/250000000 : ℝ)) (σ := (19882329/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (789419424/833316397 : ℝ) ^ p + (823564145/833316397 : ℝ) ^ p := by
    exact cert_lt (x := (789419424/833316397 : ℝ)) (y := (823564145/833316397 : ℝ)) (X := (12815773317223/50000000000000 : ℝ)) (Y := (74368454330187/100000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (231069687/250000000 : ℝ)) (n' := (833316397/1000000000 : ℝ)) (Ab := (24669357/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (58106841/62500000 : ℝ) ^ p + (993099807/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (58106841/62500000 : ℝ)) (y := (993099807/1000000000 : ℝ)) (X := (7992919991729/50000000000000 : ℝ)) (Y := (42007088505677/50000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993099807/1000000000 : ℝ) ^ p + (58106841/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (993099807/1000000000 : ℝ)) (y := (58106841/62500000 : ℝ)) (X := (42007088505677/50000000000000 : ℝ)) (Y := (7992919991729/50000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1922809263/1000000000 : ℝ)) (τ := (58106841/62500000 : ℝ)) (σ := (993099807/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (61173435/64592018 : ℝ) ^ p + (414971991/419848117 : ℝ) ^ p := by
    exact cert_lt (x := (61173435/64592018 : ℝ)) (y := (414971991/419848117 : ℝ)) (X := (6365761655451/25000000000000 : ℝ)) (Y := (18634238739333/25000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (58106841/62500000 : ℝ)) (n' := (419848117/500000000 : ℝ)) (Ab := (159050931/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (929926767/1000000000 : ℝ) ^ p + (99305549/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (929926767/1000000000 : ℝ)) (y := (99305549/100000000 : ℝ)) (X := (8040051614141/50000000000000 : ℝ)) (Y := (83919913877369/100000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99305549/100000000 : ℝ) ^ p + (929926767/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99305549/100000000 : ℝ)) (y := (929926767/1000000000 : ℝ)) (X := (83919913877369/100000000000000 : ℝ)) (Y := (8040051614141/50000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1922982257/1000000000 : ℝ)) (τ := (929926767/1000000000 : ℝ)) (σ := (99305549/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795487419/839950763 : ℝ) ^ p + (830198511/839950763 : ℝ) ^ p := by
    exact cert_lt (x := (795487419/839950763 : ℝ)) (y := (830198511/839950763 : ℝ)) (X := (25456369026187/100000000000000 : ℝ)) (Y := (37271815935829/50000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (929926767/1000000000 : ℝ)) (n' := (839950763/1000000000 : ℝ)) (Ab := (795487419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (7439483/8000000 : ℝ) ^ p + (993053729/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7439483/8000000 : ℝ)) (y := (993053729/1000000000 : ℝ)) (X := (16083848098749/100000000000000 : ℝ)) (Y := (83916170294347/100000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993053729/1000000000 : ℝ) ^ p + (7439483/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (993053729/1000000000 : ℝ)) (y := (7439483/8000000 : ℝ)) (X := (83916170294347/100000000000000 : ℝ)) (Y := (16083848098749/100000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (120186819/62500000 : ℝ)) (τ := (7439483/8000000 : ℝ)) (σ := (993053729/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (132582773/139993474 : ℝ) ^ p + (207552148/209990211 : ℝ) ^ p := by
    exact cert_lt (x := (132582773/139993474 : ℝ)) (y := (207552148/209990211 : ℝ)) (X := (25456104696359/100000000000000 : ℝ)) (Y := (37271948124651/50000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (7439483/8000000 : ℝ)) (n' := (209990211/250000000 : ℝ)) (Ab := (397748319/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (232483929/250000000 : ℝ) ^ p + (993053659/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232483929/250000000 : ℝ)) (y := (993053659/1000000000 : ℝ)) (X := (16083996466461/100000000000000 : ℝ)) (Y := (10489502686213/12500000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993053659/1000000000 : ℝ) ^ p + (232483929/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993053659/1000000000 : ℝ)) (y := (232483929/250000000 : ℝ)) (X := (10489502686213/12500000000000 : ℝ)) (Y := (16083996466461/100000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (3076783/1600000 : ℝ)) (τ := (232483929/250000000 : ℝ)) (σ := (993053659/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (198874251/209990311 : ℝ) ^ p + (207552248/209990311 : ℝ) ^ p := by
    exact cert_lt (x := (198874251/209990311 : ℝ)) (y := (207552248/209990311 : ℝ)) (X := (12728047185843/50000000000000 : ℝ)) (Y := (2981756269573/4000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (232483929/250000000 : ℝ)) (n' := (209990311/250000000 : ℝ)) (Ab := (198874251/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (92993573/100000000 : ℝ) ^ p + (124131707/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (92993573/100000000 : ℝ)) (y := (124131707/125000000 : ℝ)) (X := (2010500319729/12500000000000 : ℝ)) (Y := (5244750944523/6250000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124131707/125000000 : ℝ) ^ p + (92993573/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (124131707/125000000 : ℝ)) (y := (92993573/100000000 : ℝ)) (X := (5244750944523/6250000000000 : ℝ)) (Y := (2010500319729/12500000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (961494693/500000000 : ℝ)) (τ := (92993573/100000000 : ℝ)) (σ := (124131707/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795497019/839961260 : ℝ) ^ p + (207552252/209990315 : ℝ) ^ p := by
    exact cert_lt (x := (795497019/839961260 : ℝ)) (y := (207552252/209990315 : ℝ)) (X := (12728047124251/50000000000000 : ℝ)) (Y := (37271953579463/50000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (92993573/100000000 : ℝ)) (n' := (41998063/50000000 : ℝ)) (Ab := (795497019/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (961494693/500000000 : ℝ)) (τ := (92993573/100000000 : ℝ)) (σ := (124131707/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (92993573/100000000 : ℝ)) (n' := (41998063/50000000 : ℝ)) (Ab := (795497019/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (961494693/500000000 : ℝ)) (τ := (92993573/100000000 : ℝ)) (σ := (124131707/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (92993573/100000000 : ℝ)) (n' := (41998063/50000000 : ℝ)) (Ab := (795497019/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (961494693/500000000 : ℝ)) (τ := (92993573/100000000 : ℝ)) (σ := (124131707/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (92993573/100000000 : ℝ)) (n' := (41998063/50000000 : ℝ)) (Ab := (795497019/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (961494693/500000000 : ℝ)) (τ := (92993573/100000000 : ℝ)) (σ := (124131707/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (92993573/100000000 : ℝ)) (n' := (41998063/50000000 : ℝ)) (Ab := (795497019/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (961494693/500000000 : ℝ)) (τ := (92993573/100000000 : ℝ)) (σ := (124131707/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1663899528/1805949587 : ℝ) ^ p + (1796197335/1805949587 : ℝ) ^ p := by
    exact cert_lt (x := (1663899528/1805949587 : ℝ)) (y := (1796197335/1805949587 : ℝ)) (X := (12734378329901/100000000000000 : ℝ)) (Y := (21816405466103/25000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1116922610/1194050413 : ℝ) ^ p + (1184298161/1194050413 : ℝ) ^ p := by
    exact cert_lt (x := (1116922610/1194050413 : ℝ)) (y := (1184298161/1194050413 : ℝ)) (X := (18641433203013/100000000000000 : ℝ)) (Y := (16271713457803/20000000000000 : ℝ)) 805 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124131707/125000000 : ℝ)) (U := (1194050413/1000000000 : ℝ)) (Ab := (207987441/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (92993573/100000000 : ℝ)) (σ := (124131707/125000000 : ℝ)) (Ab := (111692261/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab132
