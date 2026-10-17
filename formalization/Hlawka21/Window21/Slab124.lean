import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 124, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab124 (p : ℝ) (hpa : (199/8 : ℝ) ≤ p) (hpb : p ≤ (797/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (260595914263/13581750000000 : ℝ) (4932347/500000000 : ℝ) (1000000162981/5432700000000 : ℝ) (3033/2500 : ℝ) (243138361/125000000 : ℝ) (12156493/12500000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193949079/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5581/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4649/10000 : ℝ)
      else (3899/5000 : ℝ) ≤ X j i ∧ X j i ≤ (741/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (260595914263/13581750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4932347/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (461740411/500000000 : ℝ) ^ p + (198813843/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (461740411/500000000 : ℝ)) (y := (198813843/200000000 : ℝ)) (X := (13770133706001/100000000000000 : ℝ)) (Y := (86229884333839/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198813843/200000000 : ℝ) ^ p + (461740411/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198813843/200000000 : ℝ)) (y := (461740411/500000000 : ℝ)) (X := (86229884333839/100000000000000 : ℝ)) (Y := (13770133706001/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1917550037/1000000000 : ℝ)) (τ := (461740411/500000000 : ℝ)) (σ := (198813843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (197091281/208146488 : ℝ) ^ p + (411360629/416292976 : ℝ) ^ p := by
    exact cert_lt (x := (197091281/208146488 : ℝ)) (y := (411360629/416292976 : ℝ)) (X := (40132865977/156250000000 : ℝ)) (Y := (14862993341073/20000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (461740411/500000000 : ℝ)) (n' := (26018311/31250000 : ℝ)) (Ab := (197091281/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (928945747/1000000000 : ℝ) ^ p + (99304781/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (928945747/1000000000 : ℝ)) (y := (99304781/100000000 : ℝ)) (X := (3189992549137/20000000000000 : ℝ)) (Y := (1050625676013/1250000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99304781/100000000 : ℝ) ^ p + (928945747/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99304781/100000000 : ℝ)) (y := (928945747/1000000000 : ℝ)) (X := (1050625676013/1250000000000 : ℝ)) (Y := (3189992549137/20000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1921993557/1000000000 : ℝ)) (τ := (928945747/1000000000 : ℝ)) (σ := (99304781/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (794239139/839013388 : ℝ) ^ p + (414574347/419506694 : ℝ) ^ p := by
    exact cert_lt (x := (794239139/839013388 : ℝ)) (y := (414574347/419506694 : ℝ)) (X := (637870848899/2500000000000 : ℝ)) (Y := (74485167390741/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (928945747/1000000000 : ℝ)) (n' := (209753347/250000000 : ℝ)) (Ab := (794239139/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (92916741/100000000 : ℝ) ^ p + (99300269/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (92916741/100000000 : ℝ)) (y := (99300269/100000000 : ℝ)) (X := (3209005085821/20000000000000 : ℝ)) (Y := (20988747884643/25000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99300269/100000000 : ℝ) ^ p + (92916741/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (99300269/100000000 : ℝ)) (y := (92916741/100000000 : ℝ)) (X := (20988747884643/25000000000000 : ℝ)) (Y := (3209005085821/20000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (19221701/10000000 : ℝ)) (τ := (92916741/100000000 : ℝ)) (σ := (99300269/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (794476641/839273308 : ℝ) ^ p + (414704307/419636654 : ℝ) ^ p := by
    exact cert_lt (x := (794476641/839273308 : ℝ)) (y := (414704307/419636654 : ℝ)) (X := (6376999547497/25000000000000 : ℝ)) (Y := (74492003118417/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (92916741/100000000 : ℝ)) (n' := (209818327/250000000 : ℝ)) (Ab := (794476641/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (929176311/1000000000 : ℝ) ^ p + (124125109/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (929176311/1000000000 : ℝ)) (y := (124125109/125000000 : ℝ)) (X := (16048854058373/100000000000000 : ℝ)) (Y := (83951163389731/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124125109/125000000 : ℝ) ^ p + (929176311/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124125109/125000000 : ℝ)) (y := (929176311/1000000000 : ℝ)) (X := (83951163389731/100000000000000 : ℝ)) (Y := (16048854058373/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1922177183/1000000000 : ℝ)) (τ := (929176311/1000000000 : ℝ)) (σ := (124125109/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (46734481/49369632 : ℝ) ^ p + (414709525/419641872 : ℝ) ^ p := by
    exact cert_lt (x := (46734481/49369632 : ℝ)) (y := (414709525/419641872 : ℝ)) (X := (2550772393427/10000000000000 : ℝ)) (Y := (74492277502617/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (929176311/1000000000 : ℝ)) (n' := (26227617/31250000 : ℝ)) (Ab := (794486177/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (232294167/250000000 : ℝ) ^ p + (993000799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232294167/250000000 : ℝ)) (y := (993000799/1000000000 : ℝ)) (X := (8024503817381/50000000000000 : ℝ)) (Y := (41975504838841/50000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993000799/1000000000 : ℝ) ^ p + (232294167/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993000799/1000000000 : ℝ)) (y := (232294167/250000000 : ℝ)) (X := (41975504838841/50000000000000 : ℝ)) (Y := (8024503817381/50000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1922177467/1000000000 : ℝ)) (τ := (232294167/250000000 : ℝ)) (σ := (993000799/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (794486559/839284162 : ℝ) ^ p + (414709734/419642081 : ℝ) ^ p := by
    exact cert_lt (x := (794486559/839284162 : ℝ)) (y := (414709734/419642081 : ℝ)) (X := (25507712988143/100000000000000 : ℝ)) (Y := (74492288492587/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (232294167/250000000 : ℝ)) (n' := (419642081/500000000 : ℝ)) (Ab := (794486559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (464588341/500000000 : ℝ) ^ p + (248250199/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (464588341/500000000 : ℝ)) (y := (248250199/250000000 : ℝ)) (X := (8024506828697/50000000000000 : ℝ)) (Y := (41975501680377/50000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248250199/250000000 : ℝ) ^ p + (464588341/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248250199/250000000 : ℝ)) (y := (464588341/500000000 : ℝ)) (X := (41975501680377/50000000000000 : ℝ)) (Y := (8024506828697/50000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (961088739/500000000 : ℝ)) (τ := (464588341/500000000 : ℝ)) (σ := (248250199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (264828858/279761393 : ℝ) ^ p + (829419485/839284179 : ℝ) ^ p := by
    exact cert_lt (x := (264828858/279761393 : ℝ)) (y := (829419485/839284179 : ℝ)) (X := (6376928028613/25000000000000 : ℝ)) (Y := (74492288939547/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (464588341/500000000 : ℝ)) (n' := (839284179/1000000000 : ℝ)) (Ab := (397243287/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (929176683/1000000000 : ℝ) ^ p + (248250199/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (929176683/1000000000 : ℝ)) (y := (248250199/250000000 : ℝ)) (X := (8024507043791/50000000000000 : ℝ)) (Y := (41975501680377/50000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248250199/250000000 : ℝ) ^ p + (929176683/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248250199/250000000 : ℝ)) (y := (929176683/1000000000 : ℝ)) (X := (41975501680377/50000000000000 : ℝ)) (Y := (8024507043791/50000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1922177479/1000000000 : ℝ)) (τ := (929176683/1000000000 : ℝ)) (σ := (248250199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (158897315/167856836 : ℝ) ^ p + (59244249/59948870 : ℝ) ^ p := by
    exact cert_lt (x := (158897315/167856836 : ℝ)) (y := (59244249/59948870 : ℝ)) (X := (12753856078567/50000000000000 : ℝ)) (Y := (74492288965839/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (929176683/1000000000 : ℝ)) (n' := (41964209/50000000 : ℝ)) (Ab := (31779463/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1922177479/1000000000 : ℝ)) (τ := (929176683/1000000000 : ℝ)) (σ := (248250199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (929176683/1000000000 : ℝ)) (n' := (41964209/50000000 : ℝ)) (Ab := (31779463/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1922177479/1000000000 : ℝ)) (τ := (929176683/1000000000 : ℝ)) (σ := (248250199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (929176683/1000000000 : ℝ)) (n' := (41964209/50000000 : ℝ)) (Ab := (31779463/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1922177479/1000000000 : ℝ)) (τ := (929176683/1000000000 : ℝ)) (σ := (248250199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (929176683/1000000000 : ℝ)) (n' := (41964209/50000000 : ℝ)) (Ab := (31779463/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1922177479/1000000000 : ℝ)) (τ := (929176683/1000000000 : ℝ)) (σ := (248250199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1662715568/1806050921 : ℝ) ^ p + (1796186227/1806050921 : ℝ) ^ p := by
    exact cert_lt (x := (1662715568/1806050921 : ℝ)) (y := (1796186227/1806050921 : ℝ)) (X := (12751640392309/100000000000000 : ℝ)) (Y := (43624179905817/50000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1116144427/1193949079 : ℝ) ^ p + (1184084385/1193949079 : ℝ) ^ p := by
    exact cert_lt (x := (1116144427/1193949079 : ℝ)) (y := (1184084385/1193949079 : ℝ)) (X := (9334227747653/50000000000000 : ℝ)) (Y := (81331544955627/100000000000000 : ℝ)) 797 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248250199/250000000 : ℝ)) (U := (1193949079/1000000000 : ℝ)) (Ab := (103919723/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (929176683/1000000000 : ℝ)) (σ := (248250199/250000000 : ℝ)) (Ab := (1116144427/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab124
