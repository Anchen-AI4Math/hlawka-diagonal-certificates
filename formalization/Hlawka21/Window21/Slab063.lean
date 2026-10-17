import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 63, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab063 (p : ℝ) (hpa : (735/32 : ℝ) ≤ p) (hpb : p ≤ (23 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (210537079391/10032750000000 : ℝ) (5406979/500000000 : ℝ) (800000120393/4013100000000 : ℝ) (3033/2500 : ℝ) (970312753/500000000 : ℝ) (121284121/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193173941/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5549/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4541/10000 : ℝ)
      else (7691/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2961/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (210537079391/10032750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5406979/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (916797553/1000000000 : ℝ) ^ p + (496841969/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (916797553/1000000000 : ℝ)) (y := (496841969/500000000 : ℝ)) (X := (847557678889/6250000000000 : ℝ)) (Y := (86439094292877/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496841969/500000000 : ℝ) ^ p + (916797553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496841969/500000000 : ℝ)) (y := (916797553/1000000000 : ℝ)) (X := (86439094292877/100000000000000 : ℝ)) (Y := (847557678889/6250000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1910481491/1000000000 : ℝ)) (τ := (916797553/1000000000 : ℝ)) (σ := (496841969/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779559057/826391189 : ℝ) ^ p + (815577231/826391189 : ℝ) ^ p := by
    exact cert_lt (x := (779559057/826391189 : ℝ)) (y := (815577231/826391189 : ℝ)) (X := (5227413996281/20000000000000 : ℝ)) (Y := (73862931215859/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916797553/1000000000 : ℝ)) (n' := (826391189/1000000000 : ℝ)) (Ab := (779559057/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (36900979/40000000 : ℝ) ^ p + (992627939/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (36900979/40000000 : ℝ)) (y := (992627939/1000000000 : ℝ)) (X := (7824590819209/50000000000000 : ℝ)) (Y := (84350834351443/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992627939/1000000000 : ℝ) ^ p + (36900979/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (992627939/1000000000 : ℝ)) (y := (36900979/40000000 : ℝ)) (X := (84350834351443/100000000000000 : ℝ)) (Y := (7824590819209/50000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957576207/500000000 : ℝ)) (τ := (36900979/40000000 : ℝ)) (σ := (992627939/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785733100/833192141 : ℝ) ^ p + (822378183/833192141 : ℝ) ^ p := by
    exact cert_lt (x := (785733100/833192141 : ℝ)) (y := (822378183/833192141 : ℝ)) (X := (25952985804243/100000000000000 : ℝ)) (Y := (74047015038967/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (36900979/40000000 : ℝ)) (n' := (833192141/1000000000 : ℝ)) (Ab := (7857331/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184556737/200000000 : ℝ) ^ p + (198515201/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (184556737/200000000 : ℝ)) (y := (198515201/200000000 : ℝ)) (X := (49220712293/312500000000 : ℝ)) (Y := (21062347225339/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198515201/200000000 : ℝ) ^ p + (184556737/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198515201/200000000 : ℝ)) (y := (184556737/200000000 : ℝ)) (X := (21062347225339/25000000000000 : ℝ)) (Y := (49220712293/312500000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (191535969/100000000 : ℝ)) (τ := (184556737/200000000 : ℝ)) (σ := (198515201/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (786011608/833498985 : ℝ) ^ p + (822685027/833498985 : ℝ) ^ p := by
    exact cert_lt (x := (786011608/833498985 : ℝ)) (y := (822685027/833498985 : ℝ)) (X := (25944741300011/100000000000000 : ℝ)) (Y := (14811051983177/20000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184556737/200000000 : ℝ)) (n' := (166699797/200000000 : ℝ)) (Ab := (98251451/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (230698823/250000000 : ℝ) ^ p + (99257367/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (230698823/250000000 : ℝ)) (y := (99257367/100000000 : ℝ)) (X := (3938796303869/25000000000000 : ℝ)) (Y := (84244830563933/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99257367/100000000 : ℝ) ^ p + (230698823/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (99257367/100000000 : ℝ)) (y := (230698823/250000000 : ℝ)) (X := (84244830563933/100000000000000 : ℝ)) (Y := (3938796303869/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957684481/500000000 : ℝ)) (τ := (230698823/250000000 : ℝ)) (σ := (99257367/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (786024077/833512723 : ℝ) ^ p + (13486865/13664143 : ℝ) ^ p := by
    exact cert_lt (x := (786024077/833512723 : ℝ)) (y := (13486865/13664143 : ℝ)) (X := (25944372118189/100000000000000 : ℝ)) (Y := (74055628933541/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (230698823/250000000 : ℝ)) (n' := (833512723/1000000000 : ℝ)) (Ab := (786024077/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922795811/1000000000 : ℝ) ^ p + (496286783/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922795811/1000000000 : ℝ)) (y := (496286783/500000000 : ℝ)) (X := (7877694510517/50000000000000 : ℝ)) (Y := (21061156885707/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496286783/500000000 : ℝ) ^ p + (922795811/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496286783/500000000 : ℝ)) (y := (922795811/1000000000 : ℝ)) (X := (21061156885707/25000000000000 : ℝ)) (Y := (7877694510517/50000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1915369377/1000000000 : ℝ)) (τ := (922795811/1000000000 : ℝ)) (σ := (496286783/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (786024634/833513337 : ℝ) ^ p + (822699379/833513337 : ℝ) ^ p := by
    exact cert_lt (x := (786024634/833513337 : ℝ)) (y := (822699379/833513337 : ℝ)) (X := (2594435540303/10000000000000 : ℝ)) (Y := (74055645426007/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922795811/1000000000 : ℝ)) (n' := (833513337/1000000000 : ℝ)) (Ab := (393012317/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461397917/500000000 : ℝ) ^ p + (992573561/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461397917/500000000 : ℝ)) (y := (992573561/1000000000 : ℝ)) (X := (15755398052937/100000000000000 : ℝ)) (Y := (8424461778221/10000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992573561/1000000000 : ℝ) ^ p + (461397917/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992573561/1000000000 : ℝ)) (y := (461397917/500000000 : ℝ)) (X := (8424461778221/10000000000000 : ℝ)) (Y := (15755398052937/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383073879/200000000 : ℝ)) (τ := (461397917/500000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (786024659/833513364 : ℝ) ^ p + (411349703/416756682 : ℝ) ^ p := by
    exact cert_lt (x := (786024659/833513364 : ℝ)) (y := (411349703/416756682 : ℝ)) (X := (12972177526263/50000000000000 : ℝ)) (Y := (37027823075623/50000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461397917/500000000 : ℝ)) (n' := (208378341/250000000 : ℝ)) (Ab := (786024659/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (184559167/200000000 : ℝ) ^ p + (992573561/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184559167/200000000 : ℝ)) (y := (992573561/1000000000 : ℝ)) (X := (15755398445629/100000000000000 : ℝ)) (Y := (8424461778221/10000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992573561/1000000000 : ℝ) ^ p + (184559167/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992573561/1000000000 : ℝ)) (y := (184559167/200000000 : ℝ)) (X := (8424461778221/10000000000000 : ℝ)) (Y := (15755398445629/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (786024661/833513366 : ℝ) ^ p + (411349704/416756683 : ℝ) ^ p := by
    exact cert_lt (x := (786024661/833513366 : ℝ)) (y := (411349704/416756683 : ℝ)) (X := (25944355139031/100000000000000 : ℝ)) (Y := (74055646204967/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (n' := (416756683/500000000 : ℝ)) (Ab := (786024661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478842349/250000000 : ℝ)) (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652878007/1806826059 : ℝ) ^ p + (1796012101/1806826059 : ℝ) ^ p := by
    exact cert_lt (x := (1652878007/1806826059 : ℝ)) (y := (1796012101/1806826059 : ℝ)) (X := (2579244253551/20000000000000 : ℝ)) (Y := (21775944755129/25000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109784886/1193173941 : ℝ) ^ p + (1182359983/1193173941 : ℝ) ^ p := by
    exact cert_lt (x := (1109784886/1193173941 : ℝ)) (y := (1182359983/1193173941 : ℝ)) (X := (9446611735843/50000000000000 : ℝ)) (Y := (81106777188273/100000000000000 : ℝ)) 23 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992573561/1000000000 : ℝ)) (U := (1193173941/1000000000 : ℝ)) (Ab := (1652878007/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (184559167/200000000 : ℝ)) (σ := (992573561/1000000000 : ℝ)) (Ab := (554892443/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab063
