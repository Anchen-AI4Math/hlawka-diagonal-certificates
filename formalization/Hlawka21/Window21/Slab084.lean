import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 84, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab084 (p : ℝ) (hpa : (189/8 : ℝ) ≤ p) (hpb : p ≤ (757/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524476581179/25798500000000 : ℝ) (10467517/1000000000 : ℝ) (1000000154791/5159700000000 : ℝ) (3033/2500 : ℝ) (971124301/500000000 : ℝ) (971086663/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596720231/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11121/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(229/500 : ℝ)
      else (773/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524476581179/25798500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10467517/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (114903229/125000000 : ℝ) ^ p + (248455451/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (114903229/125000000 : ℝ)) (y := (248455451/250000000 : ℝ)) (X := (13636625078099/100000000000000 : ℝ)) (Y := (17272678495769/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248455451/250000000 : ℝ) ^ p + (114903229/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248455451/250000000 : ℝ)) (y := (114903229/125000000 : ℝ)) (X := (17272678495769/20000000000000 : ℝ)) (Y := (13636625078099/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (478261909/250000000 : ℝ)) (τ := (114903229/125000000 : ℝ)) (σ := (248455451/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782753664/828657793 : ℝ) ^ p + (818190276/828657793 : ℝ) ^ p := by
    exact cert_lt (x := (782753664/828657793 : ℝ)) (y := (818190276/828657793 : ℝ)) (X := (12985994650721/50000000000000 : ℝ)) (Y := (18507002913709/25000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (114903229/125000000 : ℝ)) (n' := (828657793/1000000000 : ℝ)) (Ab := (6115263/7812500 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (231215681/250000000 : ℝ) ^ p + (248194319/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (231215681/250000000 : ℝ)) (y := (248194319/250000000 : ℝ)) (X := (7879262345849/50000000000000 : ℝ)) (Y := (42120746356347/50000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248194319/250000000 : ℝ) ^ p + (231215681/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248194319/250000000 : ℝ)) (y := (231215681/250000000 : ℝ)) (X := (42120746356347/50000000000000 : ℝ)) (Y := (7879262345849/50000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (47941/25000 : ℝ)) (τ := (231215681/250000000 : ℝ)) (σ := (248194319/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394411959/417664184 : ℝ) ^ p + (824860851/835328368 : ℝ) ^ p := by
    exact cert_lt (x := (394411959/417664184 : ℝ)) (y := (824860851/835328368 : ℝ)) (X := (25792870845437/100000000000000 : ℝ)) (Y := (1484142600143/2000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (231215681/250000000 : ℝ)) (n' := (52208023/62500000 : ℝ)) (Ab := (394411959/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (11563851/12500000 : ℝ) ^ p + (124090979/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (11563851/12500000 : ℝ)) (y := (124090979/125000000 : ℝ)) (X := (495553717347/3125000000000 : ℝ)) (Y := (84142297954689/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124090979/125000000 : ℝ) ^ p + (11563851/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (124090979/125000000 : ℝ)) (y := (11563851/12500000 : ℝ)) (X := (84142297954689/100000000000000 : ℝ)) (Y := (495553717347/3125000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (239729489/125000000 : ℝ)) (τ := (11563851/12500000 : ℝ)) (σ := (124090979/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (789087267/835617812 : ℝ) ^ p + (825150295/835617812 : ℝ) ^ p := by
    exact cert_lt (x := (789087267/835617812 : ℝ)) (y := (825150295/835617812 : ℝ)) (X := (6446288546437/25000000000000 : ℝ)) (Y := (9276855841483/12500000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (11563851/12500000 : ℝ)) (n' := (208904453/250000000 : ℝ)) (Ab := (789087267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (115639831/125000000 : ℝ) ^ p + (496362847/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115639831/125000000 : ℝ)) (y := (496362847/500000000 : ℝ)) (X := (15862004866121/100000000000000 : ℝ)) (Y := (16827602242871/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496362847/500000000 : ℝ) ^ p + (115639831/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362847/500000000 : ℝ)) (y := (115639831/125000000 : ℝ)) (X := (16827602242871/20000000000000 : ℝ)) (Y := (15862004866121/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (958922171/500000000 : ℝ)) (τ := (115639831/125000000 : ℝ)) (σ := (496362847/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (789098608/835630277 : ℝ) ^ p + (825162760/835630277 : ℝ) ^ p := by
    exact cert_lt (x := (789098608/835630277 : ℝ)) (y := (825162760/835630277 : ℝ)) (X := (2578482187241/10000000000000 : ℝ)) (Y := (74215178952311/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (115639831/125000000 : ℝ)) (n' := (835630277/1000000000 : ℝ)) (Ab := (49318663/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925119103/1000000000 : ℝ) ^ p + (496362801/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925119103/1000000000 : ℝ)) (y := (496362801/500000000 : ℝ)) (X := (15862189418803/100000000000000 : ℝ)) (Y := (84137826756883/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496362801/500000000 : ℝ) ^ p + (925119103/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362801/500000000 : ℝ)) (y := (925119103/1000000000 : ℝ)) (X := (84137826756883/100000000000000 : ℝ)) (Y := (15862189418803/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383568941/200000000 : ℝ)) (τ := (925119103/1000000000 : ℝ)) (σ := (496362801/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789099097/835630814 : ℝ) ^ p + (825163297/835630814 : ℝ) ^ p := by
    exact cert_lt (x := (789099097/835630814 : ℝ)) (y := (825163297/835630814 : ℝ)) (X := (5156961576629/20000000000000 : ℝ)) (Y := (14843038652877/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925119103/1000000000 : ℝ)) (n' := (417815407/500000000 : ℝ)) (Ab := (789099097/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925119123/1000000000 : ℝ) ^ p + (496362799/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925119123/1000000000 : ℝ)) (y := (496362799/500000000 : ℝ)) (X := (991387345691/6250000000000 : ℝ)) (Y := (84137818737001/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496362799/500000000 : ℝ) ^ p + (925119123/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362799/500000000 : ℝ)) (y := (925119123/1000000000 : ℝ)) (X := (84137818737001/100000000000000 : ℝ)) (Y := (991387345691/6250000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917844721/1000000000 : ℝ)) (τ := (925119123/1000000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789099119/835630838 : ℝ) ^ p + (825163321/835630838 : ℝ) ^ p := by
    exact cert_lt (x := (789099119/835630838 : ℝ)) (y := (825163321/835630838 : ℝ)) (X := (12892403685103/50000000000000 : ℝ)) (Y := (74215193904031/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925119123/1000000000 : ℝ)) (n' := (417815419/500000000 : ℝ)) (Ab := (789099119/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (231279781/250000000 : ℝ) ^ p + (496362799/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (231279781/250000000 : ℝ)) (y := (496362799/500000000 : ℝ)) (X := (3965549484167/25000000000000 : ℝ)) (Y := (84137818737001/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496362799/500000000 : ℝ) ^ p + (231279781/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496362799/500000000 : ℝ)) (y := (231279781/250000000 : ℝ)) (X := (84137818737001/100000000000000 : ℝ)) (Y := (3965549484167/25000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (87677680/92847871 : ℝ) ^ p + (825163322/835630839 : ℝ) ^ p := by
    exact cert_lt (x := (87677680/92847871 : ℝ)) (y := (825163322/835630839 : ℝ)) (X := (103139229653/400000000000 : ℝ)) (Y := (74215193930683/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (n' := (835630839/1000000000 : ℝ)) (Ab := (9863739/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (958922361/500000000 : ℝ)) (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (828218082/903279769 : ℝ) ^ p + (1796092021/1806559538 : ℝ) ^ p := by
    exact cert_lt (x := (828218082/903279769 : ℝ)) (y := (1796092021/1806559538 : ℝ)) (X := (513747650937/4000000000000 : ℝ)) (Y := (87156308937621/100000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112063193/1193440462 : ℝ) ^ p + (1182972945/1193440462 : ℝ) ^ p := by
    exact cert_lt (x := (1112063193/1193440462 : ℝ)) (y := (1182972945/1193440462 : ℝ)) (X := (752475317671/4000000000000 : ℝ)) (Y := (16237623557879/20000000000000 : ℝ)) 757 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496362799/500000000 : ℝ)) (U := (596720231/500000000 : ℝ)) (Ab := (414109041/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231279781/250000000 : ℝ)) (σ := (496362799/500000000 : ℝ)) (Ab := (1112063193/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab084
