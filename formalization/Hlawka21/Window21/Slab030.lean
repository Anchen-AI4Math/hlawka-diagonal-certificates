import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 30, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab030 (p : ℝ) (hpa : (351/16 : ℝ) ≤ p) (hpb : p ≤ (703/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (211799372969/9582300000000 : ℝ) (11406361/1000000000 : ℝ) (2000000287469/9582300000000 : ℝ) (3033/2500 : ℝ) (121117631/62500000 : ℝ) (968897499/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298190083/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(553/500 : ℝ) ≤ X j i ∧ X j i ≤ -(4473/10000 : ℝ)
      else (61/80 : ℝ) ≤ X j i ∧ X j i ≤ (11837/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (211799372969/9582300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11406361/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (912673313/1000000000 : ℝ) ^ p + (993455227/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (912673313/1000000000 : ℝ)) (y := (993455227/1000000000 : ℝ)) (X := (6716575297563/50000000000000 : ℝ)) (Y := (86566866272821/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993455227/1000000000 : ℝ) ^ p + (912673313/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993455227/1000000000 : ℝ)) (y := (912673313/1000000000 : ℝ)) (X := (86566866272821/100000000000000 : ℝ)) (Y := (6716575297563/50000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (95306427/50000000 : ℝ)) (τ := (912673313/1000000000 : ℝ)) (σ := (993455227/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (129024279/137083385 : ℝ) ^ p + (811093949/822500310 : ℝ) ^ p := by
    exact cert_lt (x := (129024279/137083385 : ℝ)) (y := (811093949/822500310 : ℝ)) (X := (5283940877021/20000000000000 : ℝ)) (Y := (2299384265413/3125000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (912673313/1000000000 : ℝ)) (n' := (82250031/100000000 : ℝ)) (Ab := (387072837/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (459269591/500000000 : ℝ) ^ p + (992382649/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459269591/500000000 : ℝ)) (y := (992382649/1000000000 : ℝ)) (X := (7731652182121/50000000000000 : ℝ)) (Y := (1690734225843/2000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992382649/1000000000 : ℝ) ^ p + (459269591/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992382649/1000000000 : ℝ)) (y := (459269591/500000000 : ℝ)) (X := (1690734225843/2000000000000 : ℝ)) (Y := (7731652182121/50000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1910921831/1000000000 : ℝ)) (τ := (459269591/500000000 : ℝ)) (σ := (992382649/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (780481798/829507963 : ℝ) ^ p + (818101602/829507963 : ℝ) ^ p := by
    exact cert_lt (x := (780481798/829507963 : ℝ)) (y := (818101602/829507963 : ℝ)) (X := (26227424053737/100000000000000 : ℝ)) (Y := (73772577283469/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (459269591/500000000 : ℝ)) (n' := (829507963/1000000000 : ℝ)) (Ab := (390240899/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (918822389/1000000000 : ℝ) ^ p + (496163233/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (918822389/1000000000 : ℝ)) (y := (496163233/500000000 : ℝ)) (X := (15568383973671/100000000000000 : ℝ)) (Y := (8443163162293/10000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496163233/500000000 : ℝ) ^ p + (918822389/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496163233/500000000 : ℝ)) (y := (918822389/1000000000 : ℝ)) (X := (8443163162293/10000000000000 : ℝ)) (Y := (15568383973671/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (382229771/200000000 : ℝ)) (τ := (918822389/1000000000 : ℝ)) (σ := (496163233/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (780786646/829845189 : ℝ) ^ p + (818438828/829845189 : ℝ) ^ p := by
    exact cert_lt (x := (780786646/829845189 : ℝ)) (y := (818438828/829845189 : ℝ)) (X := (13109120206663/50000000000000 : ℝ)) (Y := (3689088019837/5000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (918822389/1000000000 : ℝ)) (n' := (829845189/1000000000 : ℝ)) (Ab := (390393323/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (91883591/100000000 : ℝ) ^ p + (992323773/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (91883591/100000000 : ℝ)) (y := (992323773/1000000000 : ℝ)) (X := (7786708870459/50000000000000 : ℝ)) (Y := (84426598008443/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992323773/1000000000 : ℝ) ^ p + (91883591/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992323773/1000000000 : ℝ)) (y := (91883591/100000000 : ℝ)) (X := (84426598008443/100000000000000 : ℝ)) (Y := (7786708870459/50000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1911159683/1000000000 : ℝ)) (τ := (91883591/100000000 : ℝ)) (σ := (992323773/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (390400599/414930643 : ℝ) ^ p + (818454925/829861286 : ℝ) ^ p := by
    exact cert_lt (x := (390400599/414930643 : ℝ)) (y := (818454925/829861286 : ℝ)) (X := (26217802690477/100000000000000 : ℝ)) (Y := (9222774822517/12500000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (91883591/100000000 : ℝ)) (n' := (414930643/500000000 : ℝ)) (Ab := (390400599/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (229709139/250000000 : ℝ) ^ p + (248080911/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (229709139/250000000 : ℝ)) (y := (248080911/250000000 : ℝ)) (X := (1557365828077/10000000000000 : ℝ)) (Y := (10553294611949/12500000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248080911/250000000 : ℝ) ^ p + (229709139/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248080911/250000000 : ℝ)) (y := (229709139/250000000 : ℝ)) (X := (10553294611949/12500000000000 : ℝ)) (Y := (1557365828077/10000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (9555801/5000000 : ℝ)) (τ := (229709139/250000000 : ℝ)) (σ := (248080911/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (780801893/829862055 : ℝ) ^ p + (818455694/829862055 : ℝ) ^ p := by
    exact cert_lt (x := (780801893/829862055 : ℝ)) (y := (818455694/829862055 : ℝ)) (X := (6554445409743/25000000000000 : ℝ)) (Y := (14756443902611/20000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (229709139/250000000 : ℝ)) (n' := (165972411/200000000 : ℝ)) (Ab := (780801893/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (918836587/1000000000 : ℝ) ^ p + (496161819/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (918836587/1000000000 : ℝ)) (y := (496161819/500000000 : ℝ)) (X := (15573669823793/100000000000000 : ℝ)) (Y := (84426345681057/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496161819/500000000 : ℝ) ^ p + (918836587/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496161819/500000000 : ℝ)) (y := (918836587/1000000000 : ℝ)) (X := (84426345681057/100000000000000 : ℝ)) (Y := (15573669823793/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (76446409/40000000 : ℝ)) (τ := (918836587/1000000000 : ℝ)) (σ := (496161819/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (390400963/414931046 : ℝ) ^ p + (818455731/829862092 : ℝ) ^ p := by
    exact cert_lt (x := (390400963/414931046 : ℝ)) (y := (818455731/829862092 : ℝ)) (X := (3277222537733/12500000000000 : ℝ)) (Y := (73782220520229/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (918836587/1000000000 : ℝ)) (n' := (207465523/250000000 : ℝ)) (Ab := (390400963/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (229709147/250000000 : ℝ) ^ p + (496161819/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (229709147/250000000 : ℝ)) (y := (496161819/500000000 : ℝ)) (X := (15573670196149/100000000000000 : ℝ)) (Y := (84426345681057/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496161819/500000000 : ℝ) ^ p + (229709147/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496161819/500000000 : ℝ)) (y := (229709147/250000000 : ℝ)) (X := (84426345681057/100000000000000 : ℝ)) (Y := (15573670196149/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (955580113/500000000 : ℝ)) (τ := (229709147/250000000 : ℝ)) (σ := (496161819/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (390400964/414931047 : ℝ) ^ p + (818455733/829862094 : ℝ) ^ p := by
    exact cert_lt (x := (390400964/414931047 : ℝ)) (y := (818455733/829862094 : ℝ)) (X := (6554445097271/25000000000000 : ℝ)) (Y := (73782220574671/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (229709147/250000000 : ℝ)) (n' := (414931047/500000000 : ℝ)) (Ab := (97600241/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (955580113/500000000 : ℝ)) (τ := (229709147/250000000 : ℝ)) (σ := (496161819/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (229709147/250000000 : ℝ)) (n' := (414931047/500000000 : ℝ)) (Ab := (97600241/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (955580113/500000000 : ℝ)) (τ := (229709147/250000000 : ℝ)) (σ := (496161819/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (229709147/250000000 : ℝ)) (n' := (414931047/500000000 : ℝ)) (Ab := (97600241/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (955580113/500000000 : ℝ)) (τ := (229709147/250000000 : ℝ)) (σ := (496161819/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (229709147/250000000 : ℝ)) (n' := (414931047/500000000 : ℝ)) (Ab := (97600241/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (955580113/500000000 : ℝ)) (τ := (229709147/250000000 : ℝ)) (σ := (496161819/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1646876425/1807239668 : ℝ) ^ p + (1795833307/1807239668 : ℝ) ^ p := by
    exact cert_lt (x := (1646876425/1807239668 : ℝ)) (y := (1795833307/1807239668 : ℝ)) (X := (519417817899/4000000000000 : ℝ)) (Y := (87014554783783/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (276499516/298190083 : ℝ) ^ p + (1181353971/1192760332 : ℝ) ^ p := by
    exact cert_lt (x := (276499516/298190083 : ℝ)) (y := (1181353971/1192760332 : ℝ)) (X := (19030531288791/100000000000000 : ℝ)) (Y := (80969469193963/100000000000000 : ℝ)) 703 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496161819/500000000 : ℝ)) (U := (298190083/250000000 : ℝ)) (Ab := (65875057/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (229709147/250000000 : ℝ)) (σ := (496161819/500000000 : ℝ)) (Ab := (69124879/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab030
