import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 20, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab020 (p : ℝ) (hpa : (109/4 : ℝ) ≤ p) (hpb : p ≤ (437/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (90424879189/6035875000000 : ℝ) (7683599/1000000000 : ℝ) (800000144861/4828700000000 : ℝ) (591/500 : ℝ) (487470469/250000000 : ℝ) (97488419/100000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231232601/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2707/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(5511/10000 : ℝ)
      else (1633/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2869/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (90424879189/6035875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7683599/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (936431273/1000000000 : ℝ) ^ p + (993362123/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (936431273/1000000000 : ℝ)) (y := (993362123/1000000000 : ℝ)) (X := (16631666307741/100000000000000 : ℝ)) (Y := (10421044164599/12500000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993362123/1000000000 : ℝ) ^ p + (936431273/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993362123/1000000000 : ℝ)) (y := (936431273/1000000000 : ℝ)) (X := (10421044164599/12500000000000 : ℝ)) (Y := (16631666307741/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (482448349/250000000 : ℝ)) (τ := (936431273/1000000000 : ℝ)) (σ := (993362123/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817563590/864697781 : ℝ) ^ p + (857014182/864697781 : ℝ) ^ p := by
    exact cert_lt (x := (817563590/864697781 : ℝ)) (y := (857014182/864697781 : ℝ)) (X := (10817009522467/50000000000000 : ℝ)) (Y := (31346392819/40000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936431273/1000000000 : ℝ)) (n' := (864697781/1000000000 : ℝ)) (Ab := (81756359/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939847281/1000000000 : ℝ) ^ p + (198519139/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (939847281/1000000000 : ℝ)) (y := (198519139/200000000 : ℝ)) (X := (1837076387151/10000000000000 : ℝ)) (Y := (40814627005681/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198519139/200000000 : ℝ) ^ p + (939847281/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198519139/200000000 : ℝ)) (y := (939847281/1000000000 : ℝ)) (X := (40814627005681/50000000000000 : ℝ)) (Y := (1837076387151/10000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60388843/31250000 : ℝ)) (τ := (939847281/1000000000 : ℝ)) (σ := (198519139/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (410580629/434315456 : ℝ) ^ p + (860947313/868630912 : ℝ) ^ p := by
    exact cert_lt (x := (410580629/434315456 : ℝ)) (y := (860947313/868630912 : ℝ)) (X := (1077354133647/5000000000000 : ℝ)) (Y := (3922645914013/5000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939847281/1000000000 : ℝ)) (n' := (6786179/7812500 : ℝ)) (Ab := (410580629/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469975123/500000000 : ℝ) ^ p + (992571179/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469975123/500000000 : ℝ)) (y := (992571179/1000000000 : ℝ)) (X := (18425812574943/100000000000000 : ℝ)) (Y := (81574205777209/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992571179/1000000000 : ℝ) ^ p + (469975123/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992571179/1000000000 : ℝ)) (y := (469975123/500000000 : ℝ)) (X := (81574205777209/100000000000000 : ℝ)) (Y := (18425812574943/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (77300857/40000000 : ℝ)) (τ := (469975123/500000000 : ℝ)) (σ := (992571179/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (205317372/217187311 : ℝ) ^ p + (78278695/78977204 : ℝ) ^ p := by
    exact cert_lt (x := (205317372/217187311 : ℝ)) (y := (78278695/78977204 : ℝ)) (X := (10772238929237/50000000000000 : ℝ)) (Y := (7845552307427/10000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469975123/500000000 : ℝ)) (n' := (217187311/250000000 : ℝ)) (Ab := (51329343/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939953331/1000000000 : ℝ) ^ p + (992570443/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939953331/1000000000 : ℝ)) (y := (992570443/1000000000 : ℝ)) (X := (575858261681/3125000000000 : ℝ)) (Y := (20393138428913/25000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992570443/1000000000 : ℝ) ^ p + (939953331/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992570443/1000000000 : ℝ)) (y := (939953331/1000000000 : ℝ)) (X := (20393138428913/25000000000000 : ℝ)) (Y := (575858261681/3125000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966261887/500000000 : ℝ)) (τ := (939953331/1000000000 : ℝ)) (σ := (992570443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (273757577/289584263 : ℝ) ^ p + (861069190/868752789 : ℝ) ^ p := by
    exact cert_lt (x := (273757577/289584263 : ℝ)) (y := (861069190/868752789 : ℝ)) (X := (21544400294941/100000000000000 : ℝ)) (Y := (39227800549623/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939953331/1000000000 : ℝ)) (n' := (868752789/1000000000 : ℝ)) (Ab := (821272731/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (939953423/1000000000 : ℝ) ^ p + (992570421/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939953423/1000000000 : ℝ)) (y := (992570421/1000000000 : ℝ)) (X := (9213756817731/50000000000000 : ℝ)) (Y := (81572504333873/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992570421/1000000000 : ℝ) ^ p + (939953423/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992570421/1000000000 : ℝ)) (y := (939953423/1000000000 : ℝ)) (X := (81572504333873/100000000000000 : ℝ)) (Y := (9213756817731/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (483130961/250000000 : ℝ)) (τ := (939953423/1000000000 : ℝ)) (σ := (992570421/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (821272828/868752895 : ℝ) ^ p + (861069296/868752895 : ℝ) ^ p := by
    exact cert_lt (x := (821272828/868752895 : ℝ)) (y := (861069296/868752895 : ℝ)) (X := (21544397997333/100000000000000 : ℝ)) (Y := (78455603432283/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (939953423/1000000000 : ℝ)) (n' := (173750579/200000000 : ℝ)) (Ab := (205318207/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (939953427/1000000000 : ℝ) ^ p + (49628521/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (939953427/1000000000 : ℝ)) (y := (49628521/50000000 : ℝ)) (X := (4606878944319/25000000000000 : ℝ)) (Y := (2549140690289/3125000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (49628521/50000000 : ℝ) ^ p + (939953427/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49628521/50000000 : ℝ)) (y := (939953427/1000000000 : ℝ)) (X := (2549140690289/3125000000000 : ℝ)) (Y := (4606878944319/25000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (821272831/868752899 : ℝ) ^ p + (123009900/124107557 : ℝ) ^ p := by
    exact cert_lt (x := (821272831/868752899 : ℝ)) (y := (123009900/124107557 : ℝ)) (X := (21544397437479/100000000000000 : ℝ)) (Y := (39227801760161/50000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (n' := (868752899/1000000000 : ℝ)) (Ab := (821272831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932523847/1000000000 : ℝ)) (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1699425283/1843836995 : ℝ) ^ p + (23846148/23945935 : ℝ) ^ p := by
    exact cert_lt (x := (1699425283/1843836995 : ℝ)) (y := (23846148/23945935 : ℝ)) (X := (10779012544617/100000000000000 : ℝ)) (Y := (89220987678191/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (216542054/231232601 : ℝ) ^ p + (1148479406/1156163005 : ℝ) ^ p := by
    exact cert_lt (x := (216542054/231232601 : ℝ)) (y := (1148479406/1156163005 : ℝ)) (X := (16649748839167/100000000000000 : ℝ)) (Y := (83350251693151/100000000000000 : ℝ)) 437 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (49628521/50000000 : ℝ)) (U := (231232601/200000000 : ℝ)) (Ab := (1699425283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (939953427/1000000000 : ℝ)) (σ := (49628521/50000000 : ℝ)) (Ab := (108271027/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab020
