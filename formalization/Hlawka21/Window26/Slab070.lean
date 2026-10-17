import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 70, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab070 (p : ℝ) (hpa : (243/8 : ℝ) ≤ p) (hpb : p ≤ (487/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (89238757321/6728062500000 : ℝ) (1696227/250000000 : ℝ) (1600000322947/10764900000000 : ℝ) (591/500 : ℝ) (977484541/500000000 : ℝ) (488719369/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158037429/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10913/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2807/5000 : ℝ)
      else (8271/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5751/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (89238757321/6728062500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1696227/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (37730177/40000000 : ℝ) ^ p + (496969083/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (37730177/40000000 : ℝ)) (y := (496969083/500000000 : ℝ)) (X := (27032464563/160000000000 : ℝ)) (Y := (8310472984169/10000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496969083/500000000 : ℝ) ^ p + (37730177/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496969083/500000000 : ℝ)) (y := (37730177/40000000 : ℝ)) (X := (8310472984169/10000000000000 : ℝ)) (Y := (27032464563/160000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1937192591/1000000000 : ℝ)) (τ := (37730177/40000000 : ℝ)) (σ := (496969083/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (275651021/290063142 : ℝ) ^ p + (143900753/145031571 : ℝ) ^ p := by
    exact cert_lt (x := (275651021/290063142 : ℝ)) (y := (143900753/145031571 : ℝ)) (X := (4239929025419/20000000000000 : ℝ)) (Y := (15760071243741/20000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (37730177/40000000 : ℝ)) (n' := (435094713/500000000 : ℝ)) (Ab := (826953063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (473208289/500000000 : ℝ) ^ p + (496609313/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (473208289/500000000 : ℝ)) (y := (496609313/500000000 : ℝ)) (X := (9353544120379/50000000000000 : ℝ)) (Y := (40646465755419/50000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496609313/500000000 : ℝ) ^ p + (473208289/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496609313/500000000 : ℝ)) (y := (473208289/500000000 : ℝ)) (X := (40646465755419/50000000000000 : ℝ)) (Y := (9353544120379/50000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (484908801/250000000 : ℝ)) (τ := (473208289/500000000 : ℝ)) (σ := (496609313/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (59305525/62413787 : ℝ) ^ p + (433504055/436896509 : ℝ) ^ p := by
    exact cert_lt (x := (59305525/62413787 : ℝ)) (y := (433504055/436896509 : ℝ)) (X := (5280469215911/25000000000000 : ℝ)) (Y := (78878124235991/100000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (473208289/500000000 : ℝ)) (n' := (436896509/500000000 : ℝ)) (Ab := (16605547/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (473249747/500000000 : ℝ) ^ p + (99319857/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (473249747/500000000 : ℝ)) (y := (99319857/100000000 : ℝ)) (X := (3751407551967/20000000000000 : ℝ)) (Y := (81242981894599/100000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99319857/100000000 : ℝ) ^ p + (473249747/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99319857/100000000 : ℝ)) (y := (473249747/500000000 : ℝ)) (X := (81242981894599/100000000000000 : ℝ)) (Y := (3751407551967/20000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (121231129/62500000 : ℝ)) (τ := (473249747/500000000 : ℝ)) (σ := (99319857/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (830364363/873887348 : ℝ) ^ p + (216775610/218471837 : ℝ) ^ p := by
    exact cert_lt (x := (830364363/873887348 : ℝ)) (y := (216775610/218471837 : ℝ)) (X := (21119849024273/100000000000000 : ℝ)) (Y := (19720038080231/25000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (473249747/500000000 : ℝ)) (n' := (218471837/250000000 : ℝ)) (Ab := (830364363/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (946501657/1000000000 : ℝ) ^ p + (496599023/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (946501657/1000000000 : ℝ)) (y := (496599023/500000000 : ℝ)) (X := (9379171249911/50000000000000 : ℝ)) (Y := (81241677266697/100000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496599023/500000000 : ℝ) ^ p + (946501657/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496599023/500000000 : ℝ)) (y := (946501657/1000000000 : ℝ)) (X := (81241677266697/100000000000000 : ℝ)) (Y := (9379171249911/50000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1939699703/1000000000 : ℝ)) (τ := (946501657/1000000000 : ℝ)) (σ := (496599023/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (830366633/873889809 : ℝ) ^ p + (22233459/22407431 : ℝ) ^ p := by
    exact cert_lt (x := (830366633/873889809 : ℝ)) (y := (22233459/22407431 : ℝ)) (X := (21119796046631/100000000000000 : ℝ)) (Y := (2465006413343/3125000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (946501657/1000000000 : ℝ)) (n' := (873889809/1000000000 : ℝ)) (Ab := (830366633/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (473250857/500000000 : ℝ) ^ p + (62074877/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (473250857/500000000 : ℝ)) (y := (62074877/62500000 : ℝ)) (X := (18758376883893/100000000000000 : ℝ)) (Y := (10155205301313/12500000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62074877/62500000 : ℝ) ^ p + (473250857/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62074877/62500000 : ℝ)) (y := (473250857/500000000 : ℝ)) (X := (10155205301313/12500000000000 : ℝ)) (Y := (18758376883893/100000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (969849873/500000000 : ℝ)) (τ := (473250857/500000000 : ℝ)) (σ := (62074877/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (63874361/67222298 : ℝ) ^ p + (33350191/33611149 : ℝ) ^ p := by
    exact cert_lt (x := (63874361/67222298 : ℝ)) (y := (33350191/33611149 : ℝ)) (X := (2639974335249/12500000000000 : ℝ)) (Y := (9860025828041/12500000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (473250857/500000000 : ℝ)) (n' := (436944937/500000000 : ℝ)) (Ab := (830366693/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (189300343/200000000 : ℝ) ^ p + (62074877/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (189300343/200000000 : ℝ)) (y := (62074877/62500000 : ℝ)) (X := (18758377487123/100000000000000 : ℝ)) (Y := (10155205301313/12500000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (62074877/62500000 : ℝ) ^ p + (189300343/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (62074877/62500000 : ℝ)) (y := (189300343/200000000 : ℝ)) (X := (10155205301313/12500000000000 : ℝ)) (Y := (18758377487123/100000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1939699747/1000000000 : ℝ)) (τ := (189300343/200000000 : ℝ)) (σ := (62074877/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (92262966/97098875 : ℝ) ^ p + (289034989/291296625 : ℝ) ^ p := by
    exact cert_lt (x := (92262966/97098875 : ℝ)) (y := (289034989/291296625 : ℝ)) (X := (5279948680137/25000000000000 : ℝ)) (Y := (39440103322913/50000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (189300343/200000000 : ℝ)) (n' := (6991119/8000000 : ℝ)) (Ab := (415183347/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1939699747/1000000000 : ℝ)) (τ := (189300343/200000000 : ℝ)) (σ := (62074877/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (189300343/200000000 : ℝ)) (n' := (6991119/8000000 : ℝ)) (Ab := (415183347/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1939699747/1000000000 : ℝ)) (τ := (189300343/200000000 : ℝ)) (σ := (62074877/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (189300343/200000000 : ℝ)) (n' := (6991119/8000000 : ℝ)) (Ab := (415183347/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1939699747/1000000000 : ℝ)) (τ := (189300343/200000000 : ℝ)) (σ := (62074877/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (189300343/200000000 : ℝ)) (n' := (6991119/8000000 : ℝ)) (Ab := (415183347/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1939699747/1000000000 : ℝ)) (τ := (189300343/200000000 : ℝ)) (σ := (62074877/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (189300343/200000000 : ℝ)) (n' := (6991119/8000000 : ℝ)) (Ab := (415183347/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1939699747/1000000000 : ℝ)) (τ := (189300343/200000000 : ℝ)) (σ := (62074877/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1711161527/1841962571 : ℝ) ^ p + (1835177663/1841962571 : ℝ) ^ p := by
    exact cert_lt (x := (1711161527/1841962571 : ℝ)) (y := (1835177663/1841962571 : ℝ)) (X := (1062455258889/10000000000000 : ℝ)) (Y := (89375447765241/100000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1091207333/1158037429 : ℝ) ^ p + (1151252521/1158037429 : ℝ) ^ p := by
    exact cert_lt (x := (1091207333/1158037429 : ℝ)) (y := (1151252521/1158037429 : ℝ)) (X := (4094361511477/25000000000000 : ℝ)) (Y := (83622554698841/100000000000000 : ℝ)) 487 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (62074877/62500000 : ℝ)) (U := (1158037429/1000000000 : ℝ)) (Ab := (1711161527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (189300343/200000000 : ℝ)) (σ := (62074877/62500000 : ℝ)) (Ab := (1091207333/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab070
