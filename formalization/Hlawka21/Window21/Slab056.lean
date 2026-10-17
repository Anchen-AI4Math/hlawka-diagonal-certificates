import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 56, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab056 (p : ℝ) (hpa : (91/4 : ℝ) ≤ p) (hpb : p ≤ (729/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (263494193101/12421500000000 : ℝ) (2186901/200000000 : ℝ) (500000074529/2484300000000 : ℝ) (3033/2500 : ℝ) (194006401/100000000 : ℝ) (969991463/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149135689/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11091/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4527/10000 : ℝ)
      else (3839/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (263494193101/12421500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2186901/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (457977739/500000000 : ℝ) ^ p + (496818343/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (457977739/500000000 : ℝ)) (y := (496818343/500000000 : ℝ)) (X := (422961058913/3125000000000 : ℝ)) (Y := (86465262735641/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496818343/500000000 : ℝ) ^ p + (457977739/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496818343/500000000 : ℝ)) (y := (457977739/500000000 : ℝ)) (X := (86465262735641/100000000000000 : ℝ)) (Y := (422961058913/3125000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (477398041/250000000 : ℝ)) (τ := (457977739/500000000 : ℝ)) (σ := (496818343/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778452517/825600974 : ℝ) ^ p + (814666469/825600974 : ℝ) ^ p := by
    exact cert_lt (x := (778452517/825600974 : ℝ)) (y := (814666469/825600974 : ℝ)) (X := (818579524527/3125000000000 : ℝ)) (Y := (73805456606259/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457977739/500000000 : ℝ)) (n' := (412800487/500000000 : ℝ)) (Ab := (778452517/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921712211/1000000000 : ℝ) ^ p + (198515401/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (921712211/1000000000 : ℝ)) (y := (198515401/200000000 : ℝ)) (X := (390281193043/2500000000000 : ℝ)) (Y := (10548596131363/12500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198515401/200000000 : ℝ) ^ p + (921712211/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198515401/200000000 : ℝ)) (y := (921712211/1000000000 : ℝ)) (X := (10548596131363/12500000000000 : ℝ)) (Y := (390281193043/2500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (29910769/15625000 : ℝ)) (τ := (921712211/1000000000 : ℝ)) (σ := (198515401/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784661121/832445660 : ℝ) ^ p + (164302231/166489132 : ℝ) ^ p := by
    exact cert_lt (x := (784661121/832445660 : ℝ)) (y := (164302231/166489132 : ℝ)) (X := (13004380883189/50000000000000 : ℝ)) (Y := (369956195973/500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921712211/1000000000 : ℝ)) (n' := (41622283/50000000 : ℝ)) (Ab := (784661121/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (230494069/250000000 : ℝ) ^ p + (248131051/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (230494069/250000000 : ℝ)) (y := (248131051/250000000 : ℝ)) (X := (7856728024761/50000000000000 : ℝ)) (Y := (84286560187847/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248131051/250000000 : ℝ) ^ p + (230494069/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248131051/250000000 : ℝ)) (y := (230494069/250000000 : ℝ)) (X := (84286560187847/100000000000000 : ℝ)) (Y := (7856728024761/50000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (2991407/1562500 : ℝ)) (τ := (230494069/250000000 : ℝ)) (σ := (248131051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784944949/832758626 : ℝ) ^ p + (821824121/832758626 : ℝ) ^ p := by
    exact cert_lt (x := (784944949/832758626 : ℝ)) (y := (821824121/832758626 : ℝ)) (X := (26000329350827/100000000000000 : ℝ)) (Y := (73999671477959/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (230494069/250000000 : ℝ)) (n' := (416379313/500000000 : ℝ)) (Ab := (784944949/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921988257/1000000000 : ℝ) ^ p + (992521799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921988257/1000000000 : ℝ)) (y := (992521799/1000000000 : ℝ)) (X := (1964763565569/12500000000000 : ℝ)) (Y := (42140953779581/50000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992521799/1000000000 : ℝ) ^ p + (921988257/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992521799/1000000000 : ℝ)) (y := (921988257/1000000000 : ℝ)) (X := (42140953779581/50000000000000 : ℝ)) (Y := (1964763565569/12500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239313757/125000000 : ℝ)) (τ := (921988257/1000000000 : ℝ)) (σ := (992521799/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784957825/832772823 : ℝ) ^ p + (273946106/277590941 : ℝ) ^ p := by
    exact cert_lt (x := (784957825/832772823 : ℝ)) (y := (273946106/277590941 : ℝ)) (X := (25999947633997/100000000000000 : ℝ)) (Y := (14800010772213/20000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921988257/1000000000 : ℝ)) (n' := (832772823/1000000000 : ℝ)) (Ab := (31398313/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921988801/1000000000 : ℝ) ^ p + (99252169/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (921988801/1000000000 : ℝ)) (y := (99252169/100000000 : ℝ)) (X := (15718319802483/100000000000000 : ℝ)) (Y := (421408483487/500000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99252169/100000000 : ℝ) ^ p + (921988801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99252169/100000000 : ℝ)) (y := (921988801/1000000000 : ℝ)) (X := (421408483487/500000000000 : ℝ)) (Y := (15718319802483/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1914510491/1000000000 : ℝ)) (τ := (921988801/1000000000 : ℝ)) (σ := (99252169/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (261652803/277591156 : ℝ) ^ p + (273946321/277591156 : ℝ) ^ p := by
    exact cert_lt (x := (261652803/277591156 : ℝ)) (y := (273946321/277591156 : ℝ)) (X := (12999964774803/50000000000000 : ℝ)) (Y := (57812555651/78125000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921988801/1000000000 : ℝ)) (n' := (208193367/250000000 : ℝ)) (Ab := (784958409/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (36879553/40000000 : ℝ) ^ p + (198504337/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (36879553/40000000 : ℝ)) (y := (198504337/200000000 : ℝ)) (X := (1571832912363/10000000000000 : ℝ)) (Y := (16856337404971/20000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198504337/200000000 : ℝ) ^ p + (36879553/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (198504337/200000000 : ℝ)) (y := (36879553/40000000 : ℝ)) (X := (16856337404971/20000000000000 : ℝ)) (Y := (1571832912363/10000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (191451051/100000000 : ℝ)) (τ := (36879553/40000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784958435/832773496 : ℝ) ^ p + (821838991/832773496 : ℝ) ^ p := by
    exact cert_lt (x := (784958435/832773496 : ℝ)) (y := (821838991/832773496 : ℝ)) (X := (649998231339/2500000000000 : ℝ)) (Y := (74000071987423/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (36879553/40000000 : ℝ)) (n' := (104096687/125000000 : ℝ)) (Ab := (156991687/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (460994413/500000000 : ℝ) ^ p + (198504337/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (460994413/500000000 : ℝ)) (y := (198504337/200000000 : ℝ)) (X := (3929582378003/25000000000000 : ℝ)) (Y := (16856337404971/20000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198504337/200000000 : ℝ) ^ p + (460994413/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198504337/200000000 : ℝ)) (y := (460994413/500000000 : ℝ)) (X := (16856337404971/20000000000000 : ℝ)) (Y := (3929582378003/25000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (784958437/832773498 : ℝ) ^ p + (273946331/277591166 : ℝ) ^ p := by
    exact cert_lt (x := (784958437/832773498 : ℝ)) (y := (273946331/277591166 : ℝ)) (X := (25999929340211/100000000000000 : ℝ)) (Y := (7400007204129/10000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (n' := (416386749/500000000 : ℝ)) (Ab := (784958437/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914510511/1000000000 : ℝ)) (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1651648377/1806914488 : ℝ) ^ p + (1795979983/1806914488 : ℝ) ^ p := by
    exact cert_lt (x := (1651648377/1806914488 : ℝ)) (y := (1795979983/1806914488 : ℝ)) (X := (12914437859043/100000000000000 : ℝ)) (Y := (87085562406101/100000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (554501651/596542756 : ℝ) ^ p + (1182151007/1193085512 : ℝ) ^ p := by
    exact cert_lt (x := (554501651/596542756 : ℝ)) (y := (1182151007/1193085512 : ℝ)) (X := (9460672295579/50000000000000 : ℝ)) (Y := (8107865611121/10000000000000 : ℝ)) 729 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198504337/200000000 : ℝ)) (U := (149135689/125000000 : ℝ)) (Ab := (1651648377/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (460994413/500000000 : ℝ)) (σ := (198504337/200000000 : ℝ)) (Ab := (554501651/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab056
