import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 71, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab071 (p : ℝ) (hpa : (743/32 : ℝ) ≤ p) (hpb : p ≤ (93/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (420495501703/20283900000000 : ℝ) (10679351/1000000000 : ℝ) (4000000608517/20283900000000 : ℝ) (3033/2500 : ℝ) (242656809/125000000 : ℝ) (970588289/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193275293/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11107/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1139/2500 : ℝ)
      else (3853/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2369/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (420495501703/20283900000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10679351/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (917739577/1000000000 : ℝ) ^ p + (62108571/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (917739577/1000000000 : ℝ)) (y := (62108571/62500000 : ℝ)) (X := (2718050112597/20000000000000 : ℝ)) (Y := (43204883457437/50000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (62108571/62500000 : ℝ) ^ p + (917739577/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62108571/62500000 : ℝ)) (y := (917739577/1000000000 : ℝ)) (X := (43204883457437/50000000000000 : ℝ)) (Y := (2718050112597/20000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1911476713/1000000000 : ℝ)) (τ := (917739577/1000000000 : ℝ)) (σ := (62108571/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (780797709/827272637 : ℝ) ^ p + (816593286/827272637 : ℝ) ^ p := by
    exact cert_lt (x := (780797709/827272637 : ℝ)) (y := (816593286/827272637 : ℝ)) (X := (13036454571031/50000000000000 : ℝ)) (Y := (73927091985833/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (917739577/1000000000 : ℝ)) (n' := (827272637/1000000000 : ℝ)) (Ab := (780797709/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (184686457/200000000 : ℝ) ^ p + (992685437/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184686457/200000000 : ℝ)) (y := (992685437/1000000000 : ℝ)) (X := (3138322043787/20000000000000 : ℝ)) (Y := (16861681213163/20000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992685437/1000000000 : ℝ) ^ p + (184686457/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992685437/1000000000 : ℝ)) (y := (184686457/200000000 : ℝ)) (X := (16861681213163/20000000000000 : ℝ)) (Y := (3138322043787/20000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (958058861/500000000 : ℝ)) (τ := (184686457/200000000 : ℝ)) (σ := (992685437/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (786932211/834023755 : ℝ) ^ p + (823344404/834023755 : ℝ) ^ p := by
    exact cert_lt (x := (786932211/834023755 : ℝ)) (y := (823344404/834023755 : ℝ)) (X := (3236342527319/12500000000000 : ℝ)) (Y := (74109260982949/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (184686457/200000000 : ℝ)) (n' := (166804751/200000000 : ℝ)) (Ab := (786932211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (461843047/500000000 : ℝ) ^ p + (99263447/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (461843047/500000000 : ℝ)) (y := (99263447/100000000 : ℝ)) (X := (7896096188737/50000000000000 : ℝ)) (Y := (84207823383589/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99263447/100000000 : ℝ) ^ p + (461843047/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99263447/100000000 : ℝ)) (y := (461843047/500000000 : ℝ)) (X := (84207823383589/100000000000000 : ℝ)) (Y := (7896096188737/50000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (479080141/250000000 : ℝ)) (τ := (461843047/500000000 : ℝ)) (σ := (99263447/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (787204804/834323803 : ℝ) ^ p + (823644452/834323803 : ℝ) ^ p := by
    exact cert_lt (x := (787204804/834323803 : ℝ)) (y := (823644452/834323803 : ℝ)) (X := (25882702158849/100000000000000 : ℝ)) (Y := (18529324696693/25000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (461843047/500000000 : ℝ)) (n' := (834323803/1000000000 : ℝ)) (Ab := (196801201/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (923697289/1000000000 : ℝ) ^ p + (496316107/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (923697289/1000000000 : ℝ)) (y := (496316107/500000000 : ℝ)) (X := (15796643029439/100000000000000 : ℝ)) (Y := (84203373853363/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496316107/500000000 : ℝ) ^ p + (923697289/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496316107/500000000 : ℝ)) (y := (923697289/1000000000 : ℝ)) (X := (84203373853363/100000000000000 : ℝ)) (Y := (15796643029439/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1916329503/1000000000 : ℝ)) (τ := (923697289/1000000000 : ℝ)) (σ := (496316107/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (393608413/417168518 : ℝ) ^ p + (823657685/834337036 : ℝ) ^ p := by
    exact cert_lt (x := (393608413/417168518 : ℝ)) (y := (823657685/834337036 : ℝ)) (X := (6470586931839/25000000000000 : ℝ)) (Y := (37058826581837/50000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (923697289/1000000000 : ℝ)) (n' := (208584259/250000000 : ℝ)) (Ab := (393608413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (923697783/1000000000 : ℝ) ^ p + (496316057/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (923697783/1000000000 : ℝ)) (y := (496316057/500000000 : ℝ)) (X := (15796839450307/100000000000000 : ℝ)) (Y := (42101588313811/50000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496316057/500000000 : ℝ) ^ p + (923697783/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496316057/500000000 : ℝ)) (y := (923697783/1000000000 : ℝ)) (X := (42101588313811/50000000000000 : ℝ)) (Y := (15796839450307/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1916329897/1000000000 : ℝ)) (τ := (923697783/1000000000 : ℝ)) (σ := (496316057/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (787217357/834337620 : ℝ) ^ p + (823658269/834337620 : ℝ) ^ p := by
    exact cert_lt (x := (787217357/834337620 : ℝ)) (y := (823658269/834337620 : ℝ)) (X := (12941166212647/50000000000000 : ℝ)) (Y := (74117668802847/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (923697783/1000000000 : ℝ)) (n' := (41716881/50000000 : ℝ)) (Ab := (787217357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (184739561/200000000 : ℝ) ^ p + (99263211/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (184739561/200000000 : ℝ)) (y := (99263211/100000000 : ℝ)) (X := (15796848197849/100000000000000 : ℝ)) (Y := (84203168738601/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99263211/100000000 : ℝ) ^ p + (184739561/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (99263211/100000000 : ℝ)) (y := (184739561/200000000 : ℝ)) (X := (84203168738601/100000000000000 : ℝ)) (Y := (15796848197849/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383265983/200000000 : ℝ)) (τ := (184739561/200000000 : ℝ)) (σ := (99263211/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (787217381/834337646 : ℝ) ^ p + (823658295/834337646 : ℝ) ^ p := by
    exact cert_lt (x := (787217381/834337646 : ℝ)) (y := (823658295/834337646 : ℝ)) (X := (5176466403783/20000000000000 : ℝ)) (Y := (74117669499111/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (184739561/200000000 : ℝ)) (n' := (417168823/500000000 : ℝ)) (Ab := (787217381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (383265983/200000000 : ℝ)) (τ := (184739561/200000000 : ℝ)) (σ := (99263211/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (184739561/200000000 : ℝ)) (n' := (417168823/500000000 : ℝ)) (Ab := (787217381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (383265983/200000000 : ℝ)) (τ := (184739561/200000000 : ℝ)) (σ := (99263211/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (184739561/200000000 : ℝ)) (n' := (417168823/500000000 : ℝ)) (Ab := (787217381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (383265983/200000000 : ℝ)) (τ := (184739561/200000000 : ℝ)) (σ := (99263211/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (184739561/200000000 : ℝ)) (n' := (417168823/500000000 : ℝ)) (Ab := (787217381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (383265983/200000000 : ℝ)) (τ := (184739561/200000000 : ℝ)) (σ := (99263211/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (184739561/200000000 : ℝ)) (n' := (417168823/500000000 : ℝ)) (Ab := (787217381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (383265983/200000000 : ℝ)) (τ := (184739561/200000000 : ℝ)) (σ := (99263211/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1654256164/1806724707 : ℝ) ^ p + (1796045356/1806724707 : ℝ) ^ p := by
    exact cert_lt (x := (1654256164/1806724707 : ℝ)) (y := (1796045356/1806724707 : ℝ)) (X := (12875840493541/100000000000000 : ℝ)) (Y := (87124159713073/100000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (7555540/8117519 : ℝ) ^ p + (1182595942/1193275293 : ℝ) ^ p := by
    exact cert_lt (x := (7555540/8117519 : ℝ)) (y := (1182595942/1193275293 : ℝ)) (X := (3772341807091/20000000000000 : ℝ)) (Y := (20284572865473/25000000000000 : ℝ)) 93 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99263211/100000000 : ℝ)) (U := (1193275293/1000000000 : ℝ)) (Ab := (413564041/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (184739561/200000000 : ℝ)) (σ := (99263211/100000000 : ℝ)) (Ab := (55533219/50000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab071
