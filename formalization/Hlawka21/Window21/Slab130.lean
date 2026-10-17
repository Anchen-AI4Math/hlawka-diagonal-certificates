import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 130, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab130 (p : ℝ) (hpa : (401/16 : ℝ) ≤ p) (hpb : p ≤ (803/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (520727086157/27368250000000 : ℝ) (2445031/250000000 : ℝ) (2000000328419/10947300000000 : ℝ) (3033/2500 : ℝ) (121594463/62500000 : ℝ) (4863611/5000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194025097/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(698/625 : ℝ) ≤ X j i ∧ X j i ≤ -(4659/10000 : ℝ)
      else (7807/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5929/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (520727086157/27368250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2445031/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (92408083/100000000 : ℝ) ^ p + (248526177/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (92408083/100000000 : ℝ)) (y := (248526177/250000000 : ℝ)) (X := (13789049542453/100000000000000 : ℝ)) (Y := (43105484535879/50000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248526177/250000000 : ℝ) ^ p + (92408083/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248526177/250000000 : ℝ)) (y := (92408083/100000000 : ℝ)) (X := (43105484535879/50000000000000 : ℝ)) (Y := (13789049542453/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (959092769/500000000 : ℝ)) (τ := (92408083/100000000 : ℝ)) (σ := (248526177/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (71741623/75739582 : ℝ) ^ p + (411677639/416567701 : ℝ) ^ p := by
    exact cert_lt (x := (71741623/75739582 : ℝ)) (y := (411677639/416567701 : ℝ)) (X := (12822401413571/50000000000000 : ℝ)) (Y := (74355198646597/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (92408083/100000000 : ℝ)) (n' := (416567701/500000000 : ℝ)) (Ab := (789157853/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (929520081/1000000000 : ℝ) ^ p + (124135859/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (929520081/1000000000 : ℝ)) (y := (124135859/125000000 : ℝ)) (X := (1597694256161/10000000000000 : ℝ)) (Y := (21005768893281/25000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124135859/125000000 : ℝ) ^ p + (929520081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124135859/125000000 : ℝ)) (y := (929520081/1000000000 : ℝ)) (X := (21005768893281/25000000000000 : ℝ)) (Y := (1597694256161/10000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1922606953/1000000000 : ℝ)) (τ := (929520081/1000000000 : ℝ)) (σ := (124135859/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (795002759/839527102 : ℝ) ^ p + (414873489/419763551 : ℝ) ^ p := by
    exact cert_lt (x := (795002759/839527102 : ℝ)) (y := (414873489/419763551 : ℝ)) (X := (5095175839269/20000000000000 : ℝ)) (Y := (74524121681187/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (929520081/1000000000 : ℝ)) (n' := (419763551/500000000 : ℝ)) (Ab := (795002759/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (232434617/250000000 : ℝ) ^ p + (248260589/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (232434617/250000000 : ℝ)) (y := (248260589/250000000 : ℝ)) (X := (3214280903861/20000000000000 : ℝ)) (Y := (41964306635261/50000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248260589/250000000 : ℝ) ^ p + (232434617/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248260589/250000000 : ℝ)) (y := (232434617/250000000 : ℝ)) (X := (41964306635261/50000000000000 : ℝ)) (Y := (3214280903861/20000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (240347603/125000000 : ℝ)) (τ := (232434617/250000000 : ℝ)) (σ := (248260589/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795236695/839782963 : ℝ) ^ p + (830002839/839782963 : ℝ) ^ p := by
    exact cert_lt (x := (795236695/839782963 : ℝ)) (y := (830002839/839782963 : ℝ)) (X := (25469163264193/100000000000000 : ℝ)) (Y := (74530837777831/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (232434617/250000000 : ℝ)) (n' := (839782963/1000000000 : ℝ)) (Ab := (159047339/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (929747149/1000000000 : ℝ) ^ p + (49652029/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (929747149/1000000000 : ℝ)) (y := (49652029/50000000 : ℝ)) (X := (16075170492343/100000000000000 : ℝ)) (Y := (83924846740389/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49652029/50000000 : ℝ) ^ p + (929747149/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49652029/50000000 : ℝ)) (y := (929747149/1000000000 : ℝ)) (X := (83924846740389/100000000000000 : ℝ)) (Y := (16075170492343/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1922787729/1000000000 : ℝ)) (τ := (929747149/1000000000 : ℝ)) (σ := (49652029/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (795245993/839793132 : ℝ) ^ p + (207503252/209948283 : ℝ) ^ p := by
    exact cert_lt (x := (795245993/839793132 : ℝ)) (y := (207503252/209948283 : ℝ)) (X := (25468896779609/100000000000000 : ℝ)) (Y := (4658194039463/6250000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (929747149/1000000000 : ℝ)) (n' := (209948283/250000000 : ℝ)) (Ab := (795245993/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464873747/500000000 : ℝ) ^ p + (99304051/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (464873747/500000000 : ℝ)) (y := (99304051/100000000 : ℝ)) (X := (16075320177017/100000000000000 : ℝ)) (Y := (41962349144067/50000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99304051/100000000 : ℝ) ^ p + (464873747/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99304051/100000000 : ℝ)) (y := (464873747/500000000 : ℝ)) (X := (41962349144067/50000000000000 : ℝ)) (Y := (16075320177017/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (480697001/250000000 : ℝ)) (τ := (464873747/500000000 : ℝ)) (σ := (99304051/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (397623181/419896768 : ℝ) ^ p + (207503353/209948384 : ℝ) ^ p := by
    exact cert_lt (x := (397623181/419896768 : ℝ)) (y := (207503353/209948384 : ℝ)) (X := (25468885874169/100000000000000 : ℝ)) (Y := (74531115233009/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464873747/500000000 : ℝ)) (n' := (6560887/7812500 : ℝ)) (Ab := (397623181/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232436877/250000000 : ℝ) ^ p + (993040507/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232436877/250000000 : ℝ)) (y := (993040507/1000000000 : ℝ)) (X := (8037663125603/50000000000000 : ℝ)) (Y := (839246919259/1000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993040507/1000000000 : ℝ) ^ p + (232436877/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993040507/1000000000 : ℝ)) (y := (232436877/250000000 : ℝ)) (X := (839246919259/1000000000000 : ℝ)) (Y := (8037663125603/50000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (384557603/200000000 : ℝ)) (τ := (232436877/250000000 : ℝ)) (σ := (993040507/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795246378/839793553 : ℝ) ^ p + (830013429/839793553 : ℝ) ^ p := by
    exact cert_lt (x := (795246378/839793553 : ℝ)) (y := (830013429/839793553 : ℝ)) (X := (12734442897613/50000000000000 : ℝ)) (Y := (18632778919779/25000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232436877/250000000 : ℝ)) (n' := (839793553/1000000000 : ℝ)) (Ab := (397623189/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (384557603/200000000 : ℝ)) (τ := (232436877/250000000 : ℝ)) (σ := (993040507/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (232436877/250000000 : ℝ)) (n' := (839793553/1000000000 : ℝ)) (Ab := (397623189/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (384557603/200000000 : ℝ)) (τ := (232436877/250000000 : ℝ)) (σ := (993040507/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (232436877/250000000 : ℝ)) (n' := (839793553/1000000000 : ℝ)) (Ab := (397623189/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (384557603/200000000 : ℝ)) (τ := (232436877/250000000 : ℝ)) (σ := (993040507/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (232436877/250000000 : ℝ)) (n' := (839793553/1000000000 : ℝ)) (Ab := (397623189/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (384557603/200000000 : ℝ)) (τ := (232436877/250000000 : ℝ)) (σ := (993040507/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (232436877/250000000 : ℝ)) (n' := (839793553/1000000000 : ℝ)) (Ab := (397623189/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (384557603/200000000 : ℝ)) (τ := (232436877/250000000 : ℝ)) (σ := (993040507/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1663605660/1805974903 : ℝ) ^ p + (1796194779/1805974903 : ℝ) ^ p := by
    exact cert_lt (x := (1663605660/1805974903 : ℝ)) (y := (1796194779/1805974903 : ℝ)) (X := (1592332379501/12500000000000 : ℝ)) (Y := (17452268244753/20000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1116729196/1194025097 : ℝ) ^ p + (1184244973/1194025097 : ℝ) ^ p := by
    exact cert_lt (x := (1116729196/1194025097 : ℝ)) (y := (1184244973/1194025097 : ℝ)) (X := (745925537437/4000000000000 : ℝ)) (Y := (81351862330499/100000000000000 : ℝ)) 803 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993040507/1000000000 : ℝ)) (U := (1194025097/1000000000 : ℝ)) (Ab := (83180283/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (232436877/250000000 : ℝ)) (σ := (993040507/1000000000 : ℝ)) (Ab := (279182299/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab130
