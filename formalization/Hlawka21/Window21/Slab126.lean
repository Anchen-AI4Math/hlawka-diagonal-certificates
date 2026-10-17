import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 126, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab126 (p : ℝ) (hpa : (399/16 : ℝ) ≤ p) (hpb : p ≤ (799/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1042072375627/54463500000000 : ℝ) (1967269/200000000 : ℝ) (2000000326781/10892700000000 : ℝ) (3033/2500 : ℝ) (972621197/500000000 : ℝ) (972587361/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238794887/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2791/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(1163/2500 : ℝ)
      else (7801/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11857/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1042072375627/54463500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1967269/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (92368187/100000000 : ℝ) ^ p + (248520273/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (92368187/100000000 : ℝ)) (y := (248520273/250000000 : ℝ)) (X := (13776468676153/100000000000000 : ℝ)) (Y := (86223550440801/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248520273/250000000 : ℝ) ^ p + (92368187/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248520273/250000000 : ℝ)) (y := (92368187/100000000 : ℝ)) (X := (86223550440801/100000000000000 : ℝ)) (Y := (13776468676153/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958881481/500000000 : ℝ)) (τ := (92368187/100000000 : ℝ)) (σ := (248520273/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (788630709/832770181 : ℝ) ^ p + (822933836/832770181 : ℝ) ^ p := by
    exact cert_lt (x := (788630709/832770181 : ℝ)) (y := (822933836/832770181 : ℝ)) (X := (25671548578807/100000000000000 : ℝ)) (Y := (74328452267837/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (92368187/100000000 : ℝ)) (n' := (832770181/1000000000 : ℝ)) (Ab := (788630709/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (929138231/1000000000 : ℝ) ^ p + (496530437/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (929138231/1000000000 : ℝ)) (y := (496530437/500000000 : ℝ)) (X := (15959002609017/100000000000000 : ℝ)) (Y := (84041014470817/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496530437/500000000 : ℝ) ^ p + (929138231/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496530437/500000000 : ℝ)) (y := (929138231/1000000000 : ℝ)) (X := (84041014470817/100000000000000 : ℝ)) (Y := (15959002609017/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (384439821/200000000 : ℝ)) (τ := (929138231/1000000000 : ℝ)) (σ := (496530437/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (397247505/419592841 : ℝ) ^ p + (829349337/839185682 : ℝ) ^ p := by
    exact cert_lt (x := (397247505/419592841 : ℝ)) (y := (829349337/839185682 : ℝ)) (X := (25501776005283/100000000000000 : ℝ)) (Y := (2979929015157/4000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (929138231/1000000000 : ℝ)) (n' := (419592841/500000000 : ℝ)) (Ab := (79449501/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185871759/200000000 : ℝ) ^ p + (993015957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185871759/200000000 : ℝ)) (y := (993015957/1000000000 : ℝ)) (X := (4013466184413/25000000000000 : ℝ)) (Y := (41973076750489/50000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993015957/1000000000 : ℝ) ^ p + (185871759/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993015957/1000000000 : ℝ)) (y := (185871759/200000000 : ℝ)) (X := (41973076750489/50000000000000 : ℝ)) (Y := (4013466184413/25000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (60074211/31250000 : ℝ)) (τ := (185871759/200000000 : ℝ)) (σ := (993015957/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (794731315/839444239 : ℝ) ^ p + (829607894/839444239 : ℝ) ^ p := by
    exact cert_lt (x := (794731315/839444239 : ℝ)) (y := (829607894/839444239 : ℝ)) (X := (398359071833/1562500000000 : ℝ)) (Y := (37252510447469/50000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185871759/200000000 : ℝ)) (n' := (839444239/1000000000 : ℝ)) (Ab := (158946263/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (929367621/1000000000 : ℝ) ^ p + (993014153/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (929367621/1000000000 : ℝ)) (y := (993014153/1000000000 : ℝ)) (X := (8028835971667/50000000000000 : ℝ)) (Y := (2623198304711/3125000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993014153/1000000000 : ℝ) ^ p + (929367621/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993014153/1000000000 : ℝ)) (y := (929367621/1000000000 : ℝ)) (X := (2623198304711/3125000000000 : ℝ)) (Y := (8028835971667/50000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (961190887/500000000 : ℝ)) (τ := (929367621/1000000000 : ℝ)) (σ := (993014153/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (794740769/839454584 : ℝ) ^ p + (829618239/839454584 : ℝ) ^ p := by
    exact cert_lt (x := (794740769/839454584 : ℝ)) (y := (829618239/839454584 : ℝ)) (X := (6373677070839/25000000000000 : ℝ)) (Y := (18626323178087/25000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (929367621/1000000000 : ℝ)) (n' := (104931823/125000000 : ℝ)) (Ab := (794740769/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464683987/500000000 : ℝ) ^ p + (993014081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464683987/500000000 : ℝ)) (y := (993014081/1000000000 : ℝ)) (X := (16057824232331/100000000000000 : ℝ)) (Y := (839421937819/1000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993014081/1000000000 : ℝ) ^ p + (464683987/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993014081/1000000000 : ℝ)) (y := (464683987/500000000 : ℝ)) (X := (839421937819/1000000000000 : ℝ)) (Y := (16057824232331/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (384476411/200000000 : ℝ)) (τ := (464683987/500000000 : ℝ)) (σ := (993014081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (397370574/419727499 : ℝ) ^ p + (829618653/839454998 : ℝ) ^ p := by
    exact cert_lt (x := (397370574/419727499 : ℝ)) (y := (829618653/839454998 : ℝ)) (X := (12747348956077/50000000000000 : ℝ)) (Y := (74505303590179/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464683987/500000000 : ℝ)) (n' := (419727499/500000000 : ℝ)) (Ab := (198685287/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232341997/250000000 : ℝ) ^ p + (496507039/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232341997/250000000 : ℝ)) (y := (496507039/500000000 : ℝ)) (X := (321156605443/2000000000000 : ℝ)) (Y := (8394218744987/10000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496507039/500000000 : ℝ) ^ p + (232341997/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496507039/500000000 : ℝ)) (y := (232341997/250000000 : ℝ)) (X := (8394218744987/10000000000000 : ℝ)) (Y := (321156605443/2000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (961191033/500000000 : ℝ)) (τ := (232341997/250000000 : ℝ)) (σ := (496507039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (397370581/419727507 : ℝ) ^ p + (829618669/839455014 : ℝ) ^ p := by
    exact cert_lt (x := (397370581/419727507 : ℝ)) (y := (829618669/839455014 : ℝ)) (X := (25494696992827/100000000000000 : ℝ)) (Y := (74505304010579/100000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232341997/250000000 : ℝ)) (n' := (419727507/500000000 : ℝ)) (Ab := (397370581/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (929367989/1000000000 : ℝ) ^ p + (496507039/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (929367989/1000000000 : ℝ)) (y := (496507039/500000000 : ℝ)) (X := (8028915351783/50000000000000 : ℝ)) (Y := (8394218744987/10000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496507039/500000000 : ℝ) ^ p + (929367989/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496507039/500000000 : ℝ)) (y := (929367989/1000000000 : ℝ)) (X := (8394218744987/10000000000000 : ℝ)) (Y := (8028915351783/50000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1922382067/1000000000 : ℝ)) (τ := (929367989/1000000000 : ℝ)) (σ := (496507039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (198685291/209863754 : ℝ) ^ p + (829618671/839455016 : ℝ) ^ p := by
    exact cert_lt (x := (198685291/209863754 : ℝ)) (y := (829618671/839455016 : ℝ)) (X := (6373674269539/25000000000000 : ℝ)) (Y := (9313163007891/12500000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (929367989/1000000000 : ℝ)) (n' := (104931877/125000000 : ℝ)) (Ab := (198685291/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1922382067/1000000000 : ℝ)) (τ := (929367989/1000000000 : ℝ)) (σ := (496507039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (929367989/1000000000 : ℝ)) (n' := (104931877/125000000 : ℝ)) (Ab := (198685291/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1922382067/1000000000 : ℝ)) (τ := (929367989/1000000000 : ℝ)) (σ := (496507039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (929367989/1000000000 : ℝ)) (n' := (104931877/125000000 : ℝ)) (Ab := (198685291/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1922382067/1000000000 : ℝ)) (τ := (929367989/1000000000 : ℝ)) (σ := (496507039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (929367989/1000000000 : ℝ)) (n' := (104931877/125000000 : ℝ)) (Ab := (198685291/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1922382067/1000000000 : ℝ)) (τ := (929367989/1000000000 : ℝ)) (σ := (496507039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1663013694/1806025565 : ℝ) ^ p + (359237844/361205113 : ℝ) ^ p := by
    exact cert_lt (x := (1663013694/1806025565 : ℝ)) (y := (359237844/361205113 : ℝ)) (X := (1593411453769/12500000000000 : ℝ)) (Y := (17450541743339/20000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1116340119/1193974435 : ℝ) ^ p + (236827618/238794887 : ℝ) ^ p := by
    exact cert_lt (x := (1116340119/1193974435 : ℝ)) (y := (236827618/238794887 : ℝ)) (X := (9330825691517/50000000000000 : ℝ)) (Y := (8133834919159/10000000000000 : ℝ)) 799 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496507039/500000000 : ℝ)) (U := (238794887/200000000 : ℝ)) (Ab := (831506847/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (929367989/1000000000 : ℝ)) (σ := (496507039/500000000 : ℝ)) (Ab := (1116340119/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab126
