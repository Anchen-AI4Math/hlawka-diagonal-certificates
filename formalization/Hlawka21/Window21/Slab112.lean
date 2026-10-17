import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 112, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab112 (p : ℝ) (hpa : (49/2 : ℝ) ≤ p) (hpb : p ≤ (785/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (130535601857/6688500000000 : ℝ) (1254779/125000000 : ℝ) (250000040131/1337700000000 : ℝ) (3033/2500 : ℝ) (486069889/250000000 : ℝ) (972104741/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193796719/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(223/200 : ℝ) ≤ X j i ∧ X j i ≤ -(4629/10000 : ℝ)
      else (3889/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5927/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (130535601857/6688500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1254779/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (184450399/200000000 : ℝ) ^ p + (496998497/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184450399/200000000 : ℝ)) (y := (496998497/500000000 : ℝ)) (X := (1373146367567/10000000000000 : ℝ)) (Y := (17253710997871/20000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496998497/500000000 : ℝ) ^ p + (184450399/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496998497/500000000 : ℝ)) (y := (184450399/200000000 : ℝ)) (X := (17253710997871/20000000000000 : ℝ)) (Y := (1373146367567/10000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1916248989/1000000000 : ℝ)) (τ := (184450399/200000000 : ℝ)) (σ := (496998497/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (786742726/831457215 : ℝ) ^ p + (821418983/831457215 : ℝ) ^ p := by
    exact cert_lt (x := (786742726/831457215 : ℝ)) (y := (821418983/831457215 : ℝ)) (X := (12883804154589/50000000000000 : ℝ)) (Y := (74232392709663/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184450399/200000000 : ℝ)) (n' := (166291443/200000000 : ℝ)) (Ab := (393371363/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (92776841/100000000 : ℝ) ^ p + (496484259/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (92776841/100000000 : ℝ)) (y := (496484259/500000000 : ℝ)) (X := (15894695782859/100000000000000 : ℝ)) (Y := (16821064479587/20000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496484259/500000000 : ℝ) ^ p + (92776841/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496484259/500000000 : ℝ)) (y := (92776841/100000000 : ℝ)) (X := (16821064479587/20000000000000 : ℝ)) (Y := (15894695782859/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60023029/31250000 : ℝ)) (τ := (92776841/100000000 : ℝ)) (σ := (496484259/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (792675257/837956736 : ℝ) ^ p + (103489813/104744592 : ℝ) ^ p := by
    exact cert_lt (x := (792675257/837956736 : ℝ)) (y := (103489813/104744592 : ℝ)) (X := (12797403000889/50000000000000 : ℝ)) (Y := (2976207804899/4000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (92776841/100000000 : ℝ)) (n' := (6546537/7812500 : ℝ)) (Ab := (792675257/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185599367/200000000 : ℝ) ^ p + (198584431/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (185599367/200000000 : ℝ)) (y := (198584431/200000000 : ℝ)) (X := (3997743859223/25000000000000 : ℝ)) (Y := (84009041385967/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198584431/200000000 : ℝ) ^ p + (185599367/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198584431/200000000 : ℝ)) (y := (185599367/200000000 : ℝ)) (X := (84009041385967/100000000000000 : ℝ)) (Y := (3997743859223/25000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192091899/100000000 : ℝ)) (τ := (185599367/200000000 : ℝ)) (σ := (198584431/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (396460063/419112526 : ℝ) ^ p + (10897195/11029277 : ℝ) ^ p := by
    exact cert_lt (x := (396460063/419112526 : ℝ)) (y := (10897195/11029277 : ℝ)) (X := (25587721761289/100000000000000 : ℝ)) (Y := (74412279445311/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185599367/200000000 : ℝ)) (n' := (209556263/250000000 : ℝ)) (Ab := (396460063/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (464003099/500000000 : ℝ) ^ p + (124115031/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (464003099/500000000 : ℝ)) (y := (124115031/125000000 : ℝ)) (X := (15994933791689/100000000000000 : ℝ)) (Y := (42002541713053/50000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124115031/125000000 : ℝ) ^ p + (464003099/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124115031/125000000 : ℝ)) (y := (464003099/500000000 : ℝ)) (X := (42002541713053/50000000000000 : ℝ)) (Y := (15994933791689/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (960463223/500000000 : ℝ)) (τ := (464003099/500000000 : ℝ)) (σ := (124115031/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (792930162/838236049 : ℝ) ^ p + (828197817/838236049 : ℝ) ^ p := by
    exact cert_lt (x := (792930162/838236049 : ℝ)) (y := (828197817/838236049 : ℝ)) (X := (25587431533939/100000000000000 : ℝ)) (Y := (14882513943029/20000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (464003099/500000000 : ℝ)) (n' := (838236049/1000000000 : ℝ)) (Ab := (396465081/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (928006581/1000000000 : ℝ) ^ p + (99292017/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (928006581/1000000000 : ℝ)) (y := (99292017/100000000 : ℝ)) (X := (7997547865471/50000000000000 : ℝ)) (Y := (21001230385419/25000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99292017/100000000 : ℝ) ^ p + (928006581/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99292017/100000000 : ℝ)) (y := (928006581/1000000000 : ℝ)) (X := (21001230385419/25000000000000 : ℝ)) (Y := (7997547865471/50000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1920926751/1000000000 : ℝ)) (τ := (928006581/1000000000 : ℝ)) (σ := (99292017/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (792930573/838236499 : ℝ) ^ p + (828198267/838236499 : ℝ) ^ p := by
    exact cert_lt (x := (792930573/838236499 : ℝ)) (y := (828198267/838236499 : ℝ)) (X := (25587419914759/100000000000000 : ℝ)) (Y := (1860314539823/2500000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (928006581/1000000000 : ℝ)) (n' := (838236499/1000000000 : ℝ)) (Ab := (792930573/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (928006597/1000000000 : ℝ) ^ p + (992920167/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (928006597/1000000000 : ℝ)) (y := (992920167/1000000000 : ℝ)) (X := (7997551248031/50000000000000 : ℝ)) (Y := (42002457657679/50000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992920167/1000000000 : ℝ) ^ p + (928006597/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992920167/1000000000 : ℝ)) (y := (928006597/1000000000 : ℝ)) (X := (42002457657679/50000000000000 : ℝ)) (Y := (7997551248031/50000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (480231691/250000000 : ℝ)) (τ := (928006597/1000000000 : ℝ)) (σ := (992920167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (792930589/838236517 : ℝ) ^ p + (828198285/838236517 : ℝ) ^ p := by
    exact cert_lt (x := (792930589/838236517 : ℝ)) (y := (828198285/838236517 : ℝ)) (X := (6396854775421/25000000000000 : ℝ)) (Y := (74412582068031/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (928006597/1000000000 : ℝ)) (n' := (838236517/1000000000 : ℝ)) (Ab := (792930589/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (480231691/250000000 : ℝ)) (τ := (928006597/1000000000 : ℝ)) (σ := (992920167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (928006597/1000000000 : ℝ)) (n' := (838236517/1000000000 : ℝ)) (Ab := (792930589/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (480231691/250000000 : ℝ)) (τ := (928006597/1000000000 : ℝ)) (σ := (992920167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (928006597/1000000000 : ℝ)) (n' := (838236517/1000000000 : ℝ)) (Ab := (792930589/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (480231691/250000000 : ℝ)) (τ := (928006597/1000000000 : ℝ)) (σ := (992920167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (928006597/1000000000 : ℝ)) (n' := (838236517/1000000000 : ℝ)) (Ab := (792930589/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (480231691/250000000 : ℝ)) (τ := (928006597/1000000000 : ℝ)) (σ := (992920167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (928006597/1000000000 : ℝ)) (n' := (838236517/1000000000 : ℝ)) (Ab := (792930589/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (480231691/250000000 : ℝ)) (τ := (928006597/1000000000 : ℝ)) (σ := (992920167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1660896220/1806203281 : ℝ) ^ p + (1796165049/1806203281 : ℝ) ^ p := by
    exact cert_lt (x := (1660896220/1806203281 : ℝ)) (y := (1796165049/1806203281 : ℝ)) (X := (3194556443521/25000000000000 : ℝ)) (Y := (87221774500213/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1114954002/1193796719 : ℝ) ^ p + (1183758487/1193796719 : ℝ) ^ p := by
    exact cert_lt (x := (1114954002/1193796719 : ℝ)) (y := (1183758487/1193796719 : ℝ)) (X := (18709994695929/100000000000000 : ℝ)) (Y := (81290005745443/100000000000000 : ℝ)) 785 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992920167/1000000000 : ℝ)) (U := (1193796719/1000000000 : ℝ)) (Ab := (83044811/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (928006597/1000000000 : ℝ)) (σ := (992920167/1000000000 : ℝ)) (Ab := (557477001/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab112
