import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 101, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab101 (p : ℝ) (hpa : (773/32 : ℝ) ≤ p) (hpb : p ≤ (387/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2092157351759/105514500000000 : ℝ) (5101337/500000000 : ℝ) (4000000633087/21102900000000 : ℝ) (3033/2500 : ℝ) (971749477/500000000 : ℝ) (971713451/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193656793/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11139/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(461/1000 : ℝ)
      else (97/125 : ℝ) ≤ X j i ∧ X j i ≤ (2963/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2092157351759/105514500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5101337/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (115136313/125000000 : ℝ) ^ p + (496964653/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115136313/125000000 : ℝ)) (y := (496964653/500000000 : ℝ)) (X := (2738999776903/20000000000000 : ℝ)) (Y := (5394063762641/6250000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496964653/500000000 : ℝ) ^ p + (115136313/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496964653/500000000 : ℝ)) (y := (115136313/125000000 : ℝ)) (X := (5394063762641/6250000000000 : ℝ)) (Y := (2738999776903/20000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (191501981/100000000 : ℝ)) (τ := (115136313/125000000 : ℝ)) (σ := (496964653/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (785210602/830386075 : ℝ) ^ p + (820183401/830386075 : ℝ) ^ p := by
    exact cert_lt (x := (785210602/830386075 : ℝ)) (y := (820183401/830386075 : ℝ)) (X := (5169174813229/20000000000000 : ℝ)) (Y := (37077063676149/50000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115136313/125000000 : ℝ)) (n' := (33215443/40000000 : ℝ)) (Ab := (392605301/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (926654233/1000000000 : ℝ) ^ p + (496447219/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (926654233/1000000000 : ℝ)) (y := (496447219/500000000 : ℝ)) (X := (990152808633/6250000000000 : ℝ)) (Y := (525984823381/625000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496447219/500000000 : ℝ) ^ p + (926654233/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496447219/500000000 : ℝ)) (y := (926654233/1000000000 : ℝ)) (X := (525984823381/625000000000 : ℝ)) (Y := (990152808633/6250000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1919548671/1000000000 : ℝ)) (τ := (926654233/1000000000 : ℝ)) (σ := (496447219/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (791197076/836952351 : ℝ) ^ p + (826749677/836952351 : ℝ) ^ p := by
    exact cert_lt (x := (791197076/836952351 : ℝ)) (y := (826749677/836952351 : ℝ)) (X := (3208828900683/12500000000000 : ℝ)) (Y := (74329369761657/100000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (926654233/1000000000 : ℝ)) (n' := (836952351/1000000000 : ℝ)) (Ab := (197799269/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (92688911/100000000 : ℝ) ^ p + (992846897/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92688911/100000000 : ℝ)) (y := (992846897/1000000000 : ℝ)) (X := (1992482124529/12500000000000 : ℝ)) (Y := (10507520083003/12500000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992846897/1000000000 : ℝ) ^ p + (92688911/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992846897/1000000000 : ℝ)) (y := (92688911/100000000 : ℝ)) (X := (10507520083003/12500000000000 : ℝ)) (Y := (1992482124529/12500000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1919736007/1000000000 : ℝ)) (τ := (92688911/100000000 : ℝ)) (σ := (992846897/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (791448982/837228701 : ℝ) ^ p + (827026027/837228701 : ℝ) ^ p := by
    exact cert_lt (x := (791448982/837228701 : ℝ)) (y := (827026027/837228701 : ℝ)) (X := (5132661562383/20000000000000 : ℝ)) (Y := (74336693406581/100000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (92688911/100000000 : ℝ)) (n' := (837228701/1000000000 : ℝ)) (Ab := (395724491/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (926898923/1000000000 : ℝ) ^ p + (992844903/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926898923/1000000000 : ℝ)) (y := (992844903/1000000000 : ℝ)) (X := (637757571027/4000000000000 : ℝ)) (Y := (10507009667367/12500000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992844903/1000000000 : ℝ) ^ p + (926898923/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992844903/1000000000 : ℝ)) (y := (926898923/1000000000 : ℝ)) (X := (10507009667367/12500000000000 : ℝ)) (Y := (637757571027/4000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (959871913/500000000 : ℝ)) (τ := (926898923/1000000000 : ℝ)) (σ := (992844903/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (158291901/167448049 : ℝ) ^ p + (827037571/837240245 : ℝ) ^ p := by
    exact cert_lt (x := (158291901/167448049 : ℝ)) (y := (827037571/837240245 : ℝ)) (X := (12831501059859/50000000000000 : ℝ)) (Y := (37168499623941/50000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (926898923/1000000000 : ℝ)) (n' := (167448049/200000000 : ℝ)) (Ab := (158291901/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (926899333/1000000000 : ℝ) ^ p + (49642241/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (926899333/1000000000 : ℝ)) (y := (49642241/50000000 : ℝ)) (X := (15944109860471/100000000000000 : ℝ)) (Y := (21013976843791/25000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (49642241/50000000 : ℝ) ^ p + (926899333/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49642241/50000000 : ℝ)) (y := (926899333/1000000000 : ℝ)) (X := (21013976843791/25000000000000 : ℝ)) (Y := (15944109860471/100000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1919744153/1000000000 : ℝ)) (τ := (926899333/1000000000 : ℝ)) (σ := (49642241/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (791459944/837240727 : ℝ) ^ p + (827038053/837240727 : ℝ) ^ p := by
    exact cert_lt (x := (791459944/837240727 : ℝ)) (y := (827038053/837240727 : ℝ)) (X := (12831494533113/50000000000000 : ℝ)) (Y := (37168506008803/50000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (926899333/1000000000 : ℝ)) (n' := (837240727/1000000000 : ℝ)) (Ab := (98932493/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926899351/1000000000 : ℝ) ^ p + (62052801/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (926899351/1000000000 : ℝ)) (y := (62052801/62500000 : ℝ)) (X := (15944117349599/100000000000000 : ℝ)) (Y := (84055899184147/100000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (62052801/62500000 : ℝ) ^ p + (926899351/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62052801/62500000 : ℝ)) (y := (926899351/1000000000 : ℝ)) (X := (84055899184147/100000000000000 : ℝ)) (Y := (15944117349599/100000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1919744167/1000000000 : ℝ)) (τ := (926899351/1000000000 : ℝ)) (σ := (62052801/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (791459963/837240748 : ℝ) ^ p + (413519037/418620374 : ℝ) ^ p := by
    exact cert_lt (x := (791459963/837240748 : ℝ)) (y := (413519037/418620374 : ℝ)) (X := (25662988398251/100000000000000 : ℝ)) (Y := (74337012573963/100000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926899351/1000000000 : ℝ)) (n' := (209310187/250000000 : ℝ)) (Ab := (791459963/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1919744167/1000000000 : ℝ)) (τ := (926899351/1000000000 : ℝ)) (σ := (62052801/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (926899351/1000000000 : ℝ)) (n' := (209310187/250000000 : ℝ)) (Ab := (791459963/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1919744167/1000000000 : ℝ)) (τ := (926899351/1000000000 : ℝ)) (σ := (62052801/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (926899351/1000000000 : ℝ)) (n' := (209310187/250000000 : ℝ)) (Ab := (791459963/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1919744167/1000000000 : ℝ)) (τ := (926899351/1000000000 : ℝ)) (σ := (62052801/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (926899351/1000000000 : ℝ)) (n' := (209310187/250000000 : ℝ)) (Ab := (791459963/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1919744167/1000000000 : ℝ)) (τ := (926899351/1000000000 : ℝ)) (σ := (62052801/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (926899351/1000000000 : ℝ)) (n' := (209310187/250000000 : ℝ)) (Ab := (791459963/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1919744167/1000000000 : ℝ)) (τ := (926899351/1000000000 : ℝ)) (σ := (62052801/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1659180954/1806343207 : ℝ) ^ p + (1796140533/1806343207 : ℝ) ^ p := by
    exact cert_lt (x := (1659180954/1806343207 : ℝ)) (y := (1796140533/1806343207 : ℝ)) (X := (2560670090297/20000000000000 : ℝ)) (Y := (21799162453549/25000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1113837616/1193656793 : ℝ) ^ p + (1183454119/1193656793 : ℝ) ^ p := by
    exact cert_lt (x := (1113837616/1193656793 : ℝ)) (y := (1183454119/1193656793 : ℝ)) (X := (18749166309009/100000000000000 : ℝ)) (Y := (40625417244189/50000000000000 : ℝ)) 387 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (62052801/62500000 : ℝ)) (U := (1193656793/1000000000 : ℝ)) (Ab := (829590477/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (926899351/1000000000 : ℝ)) (σ := (62052801/62500000 : ℝ)) (Ab := (69614851/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab101
