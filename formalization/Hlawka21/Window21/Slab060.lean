import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 60, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab060 (p : ℝ) (hpa : (183/8 : ℝ) ≤ p) (hpb : p ≤ (733/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (263308941853/12489750000000 : ℝ) (10865299/1000000000 : ℝ) (1000000149877/4995900000000 : ℝ) (3033/2500 : ℝ) (970193079/500000000 : ℝ) (242538243/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149142001/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2219/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(907/2000 : ℝ)
      else (1537/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (263308941853/12489750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10865299/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (916438733/1000000000 : ℝ) ^ p + (124207971/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (916438733/1000000000 : ℝ)) (y := (124207971/125000000 : ℝ)) (X := (3387441819261/25000000000000 : ℝ)) (Y := (43225124911983/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124207971/125000000 : ℝ) ^ p + (916438733/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124207971/125000000 : ℝ)) (y := (916438733/1000000000 : ℝ)) (X := (43225124911983/50000000000000 : ℝ)) (Y := (3387441819261/25000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1910102501/1000000000 : ℝ)) (τ := (916438733/1000000000 : ℝ)) (σ := (124207971/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779087464/826054733 : ℝ) ^ p + (815189434/826054733 : ℝ) ^ p := by
    exact cert_lt (x := (779087464/826054733 : ℝ)) (y := (815189434/826054733 : ℝ)) (X := (6540386361883/25000000000000 : ℝ)) (Y := (9229806952781/12500000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916438733/1000000000 : ℝ)) (n' := (826054733/1000000000 : ℝ)) (Ab := (97385933/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (57636153/62500000 : ℝ) ^ p + (992606181/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57636153/62500000 : ℝ)) (y := (992606181/1000000000 : ℝ)) (X := (7816509679269/50000000000000 : ℝ)) (Y := (1687339932959/2000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992606181/1000000000 : ℝ) ^ p + (57636153/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992606181/1000000000 : ℝ)) (y := (57636153/62500000 : ℝ)) (X := (1687339932959/2000000000000 : ℝ)) (Y := (7816509679269/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1914784629/1000000000 : ℝ)) (τ := (57636153/62500000 : ℝ)) (σ := (992606181/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (52351755/55524961 : ℝ) ^ p + (822009116/832874415 : ℝ) ^ p := by
    exact cert_lt (x := (52351755/55524961 : ℝ)) (y := (822009116/832874415 : ℝ)) (X := (5195347193761/20000000000000 : ℝ)) (Y := (14804652963431/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (57636153/62500000 : ℝ)) (n' := (166574883/200000000 : ℝ)) (Ab := (31411053/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922439723/1000000000 : ℝ) ^ p + (496276939/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922439723/1000000000 : ℝ)) (y := (496276939/500000000 : ℝ)) (X := (3146958259889/20000000000000 : ℝ)) (Y := (84265225288153/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496276939/500000000 : ℝ) ^ p + (922439723/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496276939/500000000 : ℝ)) (y := (922439723/1000000000 : ℝ)) (X := (84265225288153/100000000000000 : ℝ)) (Y := (3146958259889/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914993601/1000000000 : ℝ)) (τ := (922439723/1000000000 : ℝ)) (σ := (496276939/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (392778548/416591931 : ℝ) ^ p + (822318563/833183862 : ℝ) ^ p := by
    exact cert_lt (x := (392778548/416591931 : ℝ)) (y := (822318563/833183862 : ℝ)) (X := (25968411825879/100000000000000 : ℝ)) (Y := (74031589276953/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922439723/1000000000 : ℝ)) (n' := (416591931/500000000 : ℝ)) (Ab := (98194637/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (28826609/31250000 : ℝ) ^ p + (496275757/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (28826609/31250000 : ℝ)) (y := (496275757/500000000 : ℝ)) (X := (3934847220641/25000000000000 : ℝ)) (Y := (42130314091517/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496275757/500000000 : ℝ) ^ p + (28826609/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (496275757/500000000 : ℝ)) (y := (28826609/31250000 : ℝ)) (X := (42130314091517/50000000000000 : ℝ)) (Y := (3934847220641/25000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957501501/500000000 : ℝ)) (τ := (28826609/31250000 : ℝ)) (σ := (496275757/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261856579/277732598 : ℝ) ^ p + (822332495/833197794 : ℝ) ^ p := by
    exact cert_lt (x := (261856579/277732598 : ℝ)) (y := (822332495/833197794 : ℝ)) (X := (3246004662953/12500000000000 : ℝ)) (Y := (74031963938449/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (28826609/31250000 : ℝ)) (n' := (416598897/500000000 : ℝ)) (Ab := (785569737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (461226009/500000000 : ℝ) ^ p + (992551407/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461226009/500000000 : ℝ)) (y := (992551407/1000000000 : ℝ)) (X := (1967449503593/12500000000000 : ℝ)) (Y := (84260420113307/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992551407/1000000000 : ℝ) ^ p + (461226009/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992551407/1000000000 : ℝ)) (y := (461226009/500000000 : ℝ)) (X := (84260420113307/100000000000000 : ℝ)) (Y := (1967449503593/12500000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (76600137/40000000 : ℝ)) (τ := (461226009/500000000 : ℝ)) (σ := (992551407/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785570307/833198422 : ℝ) ^ p + (822333123/833198422 : ℝ) ^ p := by
    exact cert_lt (x := (785570307/833198422 : ℝ)) (y := (822333123/833198422 : ℝ)) (X := (25968020568353/100000000000000 : ℝ)) (Y := (74031980826469/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (461226009/500000000 : ℝ)) (n' := (416599211/500000000 : ℝ)) (Ab := (785570307/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461226021/500000000 : ℝ) ^ p + (496275701/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461226021/500000000 : ℝ)) (y := (496275701/500000000 : ℝ)) (X := (1573960540901/10000000000000 : ℝ)) (Y := (42130205195217/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496275701/500000000 : ℝ) ^ p + (461226021/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496275701/500000000 : ℝ)) (y := (461226021/500000000 : ℝ)) (X := (42130205195217/50000000000000 : ℝ)) (Y := (1573960540901/10000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478750861/250000000 : ℝ)) (τ := (461226021/500000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392785166/416599225 : ℝ) ^ p + (822333151/833198450 : ℝ) ^ p := by
    exact cert_lt (x := (392785166/416599225 : ℝ)) (y := (822333151/833198450 : ℝ)) (X := (25968019508707/100000000000000 : ℝ)) (Y := (37015990789719/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461226021/500000000 : ℝ)) (n' := (16663969/20000000 : ℝ)) (Ab := (196392583/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (922452043/1000000000 : ℝ) ^ p + (496275701/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922452043/1000000000 : ℝ)) (y := (496275701/500000000 : ℝ)) (X := (3147921159971/20000000000000 : ℝ)) (Y := (42130205195217/50000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496275701/500000000 : ℝ) ^ p + (922452043/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496275701/500000000 : ℝ)) (y := (922452043/1000000000 : ℝ)) (X := (42130205195217/50000000000000 : ℝ)) (Y := (3147921159971/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785570333/833198451 : ℝ) ^ p + (822333152/833198451 : ℝ) ^ p := by
    exact cert_lt (x := (785570333/833198451 : ℝ)) (y := (822333152/833198451 : ℝ)) (X := (2596801955199/10000000000000 : ℝ)) (Y := (7403198160633/10000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (n' := (833198451/1000000000 : ℝ)) (Ab := (785570333/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (383000689/200000000 : ℝ)) (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652353773/1806863992 : ℝ) ^ p + (1795998693/1806863992 : ℝ) ^ p := by
    exact cert_lt (x := (1652353773/1806863992 : ℝ)) (y := (1795998693/1806863992 : ℝ)) (X := (806498948723/6250000000000 : ℝ)) (Y := (17419203411279/20000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109451307/1193136008 : ℝ) ^ p + (1182270709/1193136008 : ℝ) ^ p := by
    exact cert_lt (x := (1109451307/1193136008 : ℝ)) (y := (1182270709/1193136008 : ℝ)) (X := (9452605653227/50000000000000 : ℝ)) (Y := (81094789458841/100000000000000 : ℝ)) 733 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496275701/500000000 : ℝ)) (U := (149142001/125000000 : ℝ)) (Ab := (1652353773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (922452043/1000000000 : ℝ)) (σ := (496275701/500000000 : ℝ)) (Ab := (1109451307/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab060
