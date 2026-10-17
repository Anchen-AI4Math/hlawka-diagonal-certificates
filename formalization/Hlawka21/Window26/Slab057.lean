import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 57, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab057 (p : ℝ) (hpa : (473/16 : ℝ) ≤ p) (hpb : p ≤ (237/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (358092952309/26192375000000 : ℝ) (6997997/1000000000 : ℝ) (3200000628617/20953900000000 : ℝ) (591/500 : ℝ) (61054639/31250000 : ℝ) (488412951/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157572083/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2723/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(5589/10000 : ℝ)
      else (4123/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1437/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (358092952309/26192375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6997997/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (941624949/1000000000 : ℝ) ^ p + (993797989/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (941624949/1000000000 : ℝ)) (y := (993797989/1000000000 : ℝ)) (X := (16831951601639/100000000000000 : ℝ)) (Y := (3326722737663/4000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993797989/1000000000 : ℝ) ^ p + (941624949/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993797989/1000000000 : ℝ)) (y := (941624949/1000000000 : ℝ)) (X := (3326722737663/4000000000000 : ℝ)) (Y := (16831951601639/100000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (967711469/500000000 : ℝ)) (τ := (941624949/1000000000 : ℝ)) (σ := (993797989/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (412351567/434446606 : ℝ) ^ p + (861895215/868893212 : ℝ) ^ p := by
    exact cert_lt (x := (412351567/434446606 : ℝ)) (y := (861895215/868893212 : ℝ)) (X := (21302864287311/100000000000000 : ℝ)) (Y := (78697136801857/100000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (941624949/1000000000 : ℝ)) (n' := (217223303/250000000 : ℝ)) (Ab := (412351567/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (236212709/250000000 : ℝ) ^ p + (248266603/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (236212709/250000000 : ℝ)) (y := (248266603/250000000 : ℝ)) (X := (4656679404123/25000000000000 : ℝ)) (Y := (40686650717213/50000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248266603/250000000 : ℝ) ^ p + (236212709/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248266603/250000000 : ℝ)) (y := (236212709/250000000 : ℝ)) (X := (40686650717213/50000000000000 : ℝ)) (Y := (4656679404123/25000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (30279957/15625000 : ℝ)) (τ := (236212709/250000000 : ℝ)) (σ := (248266603/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (828095817/872578478 : ℝ) ^ p + (865580481/872578478 : ℝ) ^ p := by
    exact cert_lt (x := (828095817/872578478 : ℝ)) (y := (865580481/872578478 : ℝ)) (X := (2652859774571/12500000000000 : ℝ)) (Y := (19694280705159/25000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (236212709/250000000 : ℝ)) (n' := (436289239/500000000 : ℝ)) (Ab := (828095817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (944938387/1000000000 : ℝ) ^ p + (496522657/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (944938387/1000000000 : ℝ)) (y := (496522657/500000000 : ℝ)) (X := (18677917459053/100000000000000 : ℝ)) (Y := (81322101283821/100000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496522657/500000000 : ℝ) ^ p + (944938387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496522657/500000000 : ℝ)) (y := (944938387/1000000000 : ℝ)) (X := (81322101283821/100000000000000 : ℝ)) (Y := (18677917459053/100000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1937983701/1000000000 : ℝ)) (τ := (944938387/1000000000 : ℝ)) (σ := (496522657/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (828187728/872678323 : ℝ) ^ p + (865680326/872678323 : ℝ) ^ p := by
    exact cert_lt (x := (828187728/872678323 : ℝ)) (y := (865680326/872678323 : ℝ)) (X := (5305179802539/25000000000000 : ℝ)) (Y := (4923705098259/6250000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (944938387/1000000000 : ℝ)) (n' := (872678323/1000000000 : ℝ)) (Ab := (51761733/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (3779763/4000000 : ℝ) ^ p + (124130593/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (3779763/4000000 : ℝ)) (y := (124130593/125000000 : ℝ)) (X := (9339650612413/50000000000000 : ℝ)) (Y := (20330179613153/25000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124130593/125000000 : ℝ) ^ p + (3779763/4000000 : ℝ) ^ p := by
    exact cert_lt (x := (124130593/125000000 : ℝ)) (y := (3779763/4000000 : ℝ)) (X := (20330179613153/25000000000000 : ℝ)) (Y := (9339650612413/50000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (968992747/500000000 : ℝ)) (τ := (3779763/4000000 : ℝ)) (σ := (124130593/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (828190208/872681017 : ℝ) ^ p + (865683020/872681017 : ℝ) ^ p := by
    exact cert_lt (x := (828190208/872681017 : ℝ)) (y := (865683020/872681017 : ℝ)) (X := (10610330511277/50000000000000 : ℝ)) (Y := (78779339813141/100000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (3779763/4000000 : ℝ)) (n' := (872681017/1000000000 : ℝ)) (Ab := (1617559/1953125 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (944940813/1000000000 : ℝ) ^ p + (993044729/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944940813/1000000000 : ℝ)) (y := (993044729/1000000000 : ℝ)) (X := (3735867623759/20000000000000 : ℝ)) (Y := (2541271314457/3125000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993044729/1000000000 : ℝ) ^ p + (944940813/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993044729/1000000000 : ℝ)) (y := (944940813/1000000000 : ℝ)) (X := (2541271314457/3125000000000 : ℝ)) (Y := (3735867623759/20000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (968992771/500000000 : ℝ)) (τ := (944940813/1000000000 : ℝ)) (σ := (993044729/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (828190275/872681089 : ℝ) ^ p + (865683092/872681089 : ℝ) ^ p := by
    exact cert_lt (x := (828190275/872681089 : ℝ)) (y := (865683092/872681089 : ℝ)) (X := (42441320027/200000000000 : ℝ)) (Y := (78779341369689/100000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (944940813/1000000000 : ℝ)) (n' := (872681089/1000000000 : ℝ)) (Ab := (33127611/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (59058801/62500000 : ℝ) ^ p + (124130591/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (59058801/62500000 : ℝ)) (y := (124130591/125000000 : ℝ)) (X := (4669834968913/25000000000000 : ℝ)) (Y := (40660339818313/50000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124130591/125000000 : ℝ) ^ p + (59058801/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (124130591/125000000 : ℝ)) (y := (59058801/62500000 : ℝ)) (X := (40660339818313/50000000000000 : ℝ)) (Y := (4669834968913/25000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (242248193/125000000 : ℝ)) (τ := (59058801/62500000 : ℝ)) (σ := (124130591/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (828190278/872681093 : ℝ) ^ p + (865683096/872681093 : ℝ) ^ p := by
    exact cert_lt (x := (828190278/872681093 : ℝ)) (y := (865683096/872681093 : ℝ)) (X := (21220659409217/100000000000000 : ℝ)) (Y := (19694835364041/25000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (59058801/62500000 : ℝ)) (n' := (872681093/1000000000 : ℝ)) (Ab := (414095139/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (242248193/125000000 : ℝ)) (τ := (59058801/62500000 : ℝ)) (σ := (124130591/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (59058801/62500000 : ℝ)) (n' := (872681093/1000000000 : ℝ)) (Ab := (414095139/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (242248193/125000000 : ℝ)) (τ := (59058801/62500000 : ℝ)) (σ := (124130591/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (59058801/62500000 : ℝ)) (n' := (872681093/1000000000 : ℝ)) (Ab := (414095139/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (242248193/125000000 : ℝ)) (τ := (59058801/62500000 : ℝ)) (σ := (124130591/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (59058801/62500000 : ℝ)) (n' := (872681093/1000000000 : ℝ)) (Ab := (414095139/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (242248193/125000000 : ℝ)) (τ := (59058801/62500000 : ℝ)) (σ := (124130591/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (59058801/62500000 : ℝ)) (n' := (872681093/1000000000 : ℝ)) (Ab := (414095139/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (242248193/125000000 : ℝ)) (τ := (59058801/62500000 : ℝ)) (σ := (124130591/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1708339585/1842427917 : ℝ) ^ p + (1835429920/1842427917 : ℝ) ^ p := by
    exact cert_lt (x := (1708339585/1842427917 : ℝ)) (y := (1835429920/1842427917 : ℝ)) (X := (333170926959/3125000000000 : ℝ)) (Y := (89338530696791/100000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1089138461/1157572083 : ℝ) ^ p + (1150574086/1157572083 : ℝ) ^ p := by
    exact cert_lt (x := (1089138461/1157572083 : ℝ)) (y := (1150574086/1157572083 : ℝ)) (X := (16442803366027/100000000000000 : ℝ)) (Y := (16711439420911/20000000000000 : ℝ)) 237 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124130591/125000000 : ℝ)) (U := (1157572083/1000000000 : ℝ)) (Ab := (341667917/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (59058801/62500000 : ℝ)) (σ := (124130591/125000000 : ℝ)) (Ab := (1089138461/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab057
