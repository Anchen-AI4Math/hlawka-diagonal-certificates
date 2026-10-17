import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 5, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab005 (p : ℝ) (hpa : (421/16 : ℝ) ≤ p) (hpb : p ≤ (211/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1453362996103/93251500000000 : ℝ) (2000179/250000000 : ℝ) (3200000559509/18650300000000 : ℝ) (591/500 : ℝ) (194812373/100000000 : ℝ) (974001061/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (115555507/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10799/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2737/5000 : ℝ)
      else (508/625 : ℝ) ≤ X j i ∧ X j i ≤ (2867/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1453362996103/93251500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2000179/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (186810709/200000000 : ℝ) ^ p + (248292007/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (186810709/200000000 : ℝ)) (y := (248292007/250000000 : ℝ)) (X := (16540762056423/100000000000000 : ℝ)) (Y := (83459256680541/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248292007/250000000 : ℝ) ^ p + (186810709/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248292007/250000000 : ℝ)) (y := (186810709/200000000 : ℝ)) (X := (83459256680541/100000000000000 : ℝ)) (Y := (16540762056423/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1927221573/1000000000 : ℝ)) (τ := (186810709/200000000 : ℝ)) (σ := (248292007/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (81431065/86274476 : ℝ) ^ p + (213686011/215686190 : ℝ) ^ p := by
    exact cert_lt (x := (81431065/86274476 : ℝ)) (y := (213686011/215686190 : ℝ)) (X := (10893384217019/50000000000000 : ℝ)) (Y := (15642646518321/20000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (186810709/200000000 : ℝ)) (n' := (21568619/25000000 : ℝ)) (Ab := (16286213/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (187509951/200000000 : ℝ) ^ p + (992387451/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187509951/200000000 : ℝ)) (y := (992387451/1000000000 : ℝ)) (X := (18253674967549/100000000000000 : ℝ)) (Y := (81746343245099/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992387451/1000000000 : ℝ) ^ p + (187509951/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992387451/1000000000 : ℝ)) (y := (187509951/200000000 : ℝ)) (X := (81746343245099/100000000000000 : ℝ)) (Y := (18253674967549/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (964968603/500000000 : ℝ)) (τ := (187509951/200000000 : ℝ)) (σ := (992387451/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (817995314/866784683 : ℝ) ^ p + (858783967/866784683 : ℝ) ^ p := by
    exact cert_lt (x := (817995314/866784683 : ℝ)) (y := (858783967/866784683 : ℝ)) (X := (21696721779889/100000000000000 : ℝ)) (Y := (78303279279419/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (187509951/200000000 : ℝ)) (n' := (866784683/1000000000 : ℝ)) (Ab := (408997657/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37506403/40000000 : ℝ) ^ p + (62022583/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (37506403/40000000 : ℝ)) (y := (62022583/62500000 : ℝ)) (X := (9155204993743/50000000000000 : ℝ)) (Y := (3267584295879/4000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (62022583/62500000 : ℝ) ^ p + (37506403/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (62022583/62500000 : ℝ)) (y := (37506403/40000000 : ℝ)) (X := (3267584295879/4000000000000 : ℝ)) (Y := (9155204993743/50000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1930021403/1000000000 : ℝ)) (τ := (37506403/40000000 : ℝ)) (σ := (62022583/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (204527837/216727979 : ℝ) ^ p + (214727800/216727979 : ℝ) ^ p := by
    exact cert_lt (x := (204527837/216727979 : ℝ)) (y := (214727800/216727979 : ℝ)) (X := (10846948969939/50000000000000 : ℝ)) (Y := (78306103181767/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37506403/40000000 : ℝ)) (n' := (216727979/250000000 : ℝ)) (Ab := (204527837/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (187532707/200000000 : ℝ) ^ p + (992360507/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187532707/200000000 : ℝ)) (y := (992360507/1000000000 : ℝ)) (X := (9156096063181/50000000000000 : ℝ)) (Y := (81687824903109/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992360507/1000000000 : ℝ) ^ p + (187532707/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992360507/1000000000 : ℝ)) (y := (187532707/200000000 : ℝ)) (X := (81687824903109/100000000000000 : ℝ)) (Y := (9156096063181/50000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (965012021/500000000 : ℝ)) (τ := (187532707/200000000 : ℝ)) (σ := (992360507/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (272704996/288971969 : ℝ) ^ p + (858915191/866915907 : ℝ) ^ p := by
    exact cert_lt (x := (272704996/288971969 : ℝ)) (y := (858915191/866915907 : ℝ)) (X := (21693809582013/100000000000000 : ℝ)) (Y := (78306191749119/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (187532707/200000000 : ℝ)) (n' := (866915907/1000000000 : ℝ)) (Ab := (204528747/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (234415911/250000000 : ℝ) ^ p + (992360481/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (234415911/250000000 : ℝ)) (y := (992360481/1000000000 : ℝ)) (X := (18312248271599/100000000000000 : ℝ)) (Y := (40843884227231/50000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992360481/1000000000 : ℝ) ^ p + (234415911/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992360481/1000000000 : ℝ)) (y := (234415911/250000000 : ℝ)) (X := (40843884227231/50000000000000 : ℝ)) (Y := (18312248271599/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (15440193/8000000 : ℝ)) (τ := (234415911/250000000 : ℝ)) (σ := (992360481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (409057551/433458016 : ℝ) ^ p + (214728829/216729008 : ℝ) ^ p := by
    exact cert_lt (x := (409057551/433458016 : ℝ)) (y := (214728829/216729008 : ℝ)) (X := (4338761362013/20000000000000 : ℝ)) (Y := (78306194523079/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (234415911/250000000 : ℝ)) (n' := (13545563/15625000 : ℝ)) (Ab := (409057551/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (468831823/500000000 : ℝ) ^ p + (992360481/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468831823/500000000 : ℝ)) (y := (992360481/1000000000 : ℝ)) (X := (4578062325447/25000000000000 : ℝ)) (Y := (40843884227231/50000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992360481/1000000000 : ℝ) ^ p + (468831823/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992360481/1000000000 : ℝ)) (y := (468831823/500000000 : ℝ)) (X := (40843884227231/50000000000000 : ℝ)) (Y := (4578062325447/25000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1930024127/1000000000 : ℝ)) (τ := (468831823/500000000 : ℝ)) (σ := (992360481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (818115104/866916035 : ℝ) ^ p + (858915319/866916035 : ℝ) ^ p := by
    exact cert_lt (x := (818115104/866916035 : ℝ)) (y := (858915319/866916035 : ℝ)) (X := (10846903114397/50000000000000 : ℝ)) (Y := (39153097294827/50000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (468831823/500000000 : ℝ)) (n' := (173383207/200000000 : ℝ)) (Ab := (25566097/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1930024127/1000000000 : ℝ)) (τ := (468831823/500000000 : ℝ)) (σ := (992360481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (468831823/500000000 : ℝ)) (n' := (173383207/200000000 : ℝ)) (Ab := (25566097/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1930024127/1000000000 : ℝ)) (τ := (468831823/500000000 : ℝ)) (σ := (992360481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (468831823/500000000 : ℝ)) (n' := (173383207/200000000 : ℝ)) (Ab := (25566097/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1930024127/1000000000 : ℝ)) (τ := (468831823/500000000 : ℝ)) (σ := (992360481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (468831823/500000000 : ℝ)) (n' := (173383207/200000000 : ℝ)) (Ab := (25566097/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1930024127/1000000000 : ℝ)) (τ := (468831823/500000000 : ℝ)) (σ := (992360481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (468831823/500000000 : ℝ)) (n' := (173383207/200000000 : ℝ)) (Ab := (25566097/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1930024127/1000000000 : ℝ)) (τ := (468831823/500000000 : ℝ)) (σ := (992360481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (847692133/922222465 : ℝ) ^ p + (918222107/922222465 : ℝ) ^ p := by
    exact cert_lt (x := (847692133/922222465 : ℝ)) (y := (918222107/922222465 : ℝ)) (X := (2166555197101/20000000000000 : ℝ)) (Y := (89167224329797/100000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1079849721/1155555070 : ℝ) ^ p + (573777177/577777535 : ℝ) ^ p := by
    exact cert_lt (x := (1079849721/1155555070 : ℝ)) (y := (573777177/577777535 : ℝ)) (X := (8371904309807/50000000000000 : ℝ)) (Y := (41628095919031/50000000000000 : ℝ)) 211 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992360481/1000000000 : ℝ)) (U := (115555507/100000000 : ℝ)) (Ab := (847692133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (468831823/500000000 : ℝ)) (σ := (992360481/1000000000 : ℝ)) (Ab := (1079849721/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab005
