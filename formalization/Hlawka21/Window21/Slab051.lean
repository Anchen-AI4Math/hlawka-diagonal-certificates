import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 51, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab051 (p : ℝ) (hpa : (723/32 : ℝ) ≤ p) (hpb : p ≤ (181/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527457192449/24672375000000 : ℝ) (68889/6250000 : ℝ) (4000000592137/19737900000000 : ℝ) (3033/2500 : ℝ) (484914099/250000000 : ℝ) (484893551/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193022531/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2217/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(4517/10000 : ℝ)
      else (1917/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527457192449/24672375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (68889/6250000 : ℝ) := by norm_num
  have pc0 : 1 < (915343521/1000000000 : ℝ) ^ p + (993602527/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915343521/1000000000 : ℝ)) (y := (993602527/1000000000 : ℝ)) (X := (1689470230819/12500000000000 : ℝ)) (Y := (17296851117049/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993602527/1000000000 : ℝ) ^ p + (915343521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993602527/1000000000 : ℝ)) (y := (915343521/1000000000 : ℝ)) (X := (17296851117049/20000000000000 : ℝ)) (Y := (1689470230819/12500000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (14913641/7812500 : ℝ)) (τ := (915343521/1000000000 : ℝ)) (σ := (993602527/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (777648774/825025349 : ℝ) ^ p + (814003109/825025349 : ℝ) ^ p := by
    exact cert_lt (x := (777648774/825025349 : ℝ)) (y := (814003109/825025349 : ℝ)) (X := (6559096407611/25000000000000 : ℝ)) (Y := (147527231501/200000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915343521/1000000000 : ℝ)) (n' := (825025349/1000000000 : ℝ)) (Ab := (388824387/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46056073/50000000 : ℝ) ^ p + (124067533/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (46056073/50000000 : ℝ)) (y := (124067533/125000000 : ℝ)) (X := (15583674676603/100000000000000 : ℝ)) (Y := (8441634099341/10000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124067533/125000000 : ℝ) ^ p + (46056073/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (124067533/125000000 : ℝ)) (y := (46056073/50000000 : ℝ)) (X := (8441634099341/10000000000000 : ℝ)) (Y := (15583674676603/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (478415431/250000000 : ℝ)) (τ := (46056073/50000000 : ℝ)) (σ := (124067533/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (783882028/831901333 : ℝ) ^ p + (820879093/831901333 : ℝ) ^ p := by
    exact cert_lt (x := (783882028/831901333 : ℝ)) (y := (820879093/831901333 : ℝ)) (X := (26049376090589/100000000000000 : ℝ)) (Y := (14790125015027/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46056073/50000000 : ℝ)) (n' := (831901333/1000000000 : ℝ)) (Ab := (195970507/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (921389067/1000000000 : ℝ) ^ p + (496243417/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (921389067/1000000000 : ℝ)) (y := (496243417/500000000 : ℝ)) (X := (1568642988699/10000000000000 : ℝ)) (Y := (84313586839053/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496243417/500000000 : ℝ) ^ p + (921389067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496243417/500000000 : ℝ)) (y := (921389067/1000000000 : ℝ)) (X := (84313586839053/100000000000000 : ℝ)) (Y := (1568642988699/10000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1913875901/1000000000 : ℝ)) (τ := (921389067/1000000000 : ℝ)) (σ := (496243417/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784169740/832218773 : ℝ) ^ p + (821196533/832218773 : ℝ) ^ p := by
    exact cert_lt (x := (784169740/832218773 : ℝ)) (y := (821196533/832218773 : ℝ)) (X := (13020403034991/50000000000000 : ℝ)) (Y := (14791838969549/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (921389067/1000000000 : ℝ)) (n' := (832218773/1000000000 : ℝ)) (Ab := (39208487/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921401327/1000000000 : ℝ) ^ p + (124060547/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (921401327/1000000000 : ℝ)) (y := (124060547/125000000 : ℝ)) (X := (3922788234401/25000000000000 : ℝ)) (Y := (42154431301183/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124060547/125000000 : ℝ) ^ p + (921401327/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124060547/125000000 : ℝ)) (y := (921401327/1000000000 : ℝ)) (X := (42154431301183/50000000000000 : ℝ)) (Y := (3922788234401/25000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1913885703/1000000000 : ℝ)) (τ := (921401327/1000000000 : ℝ)) (σ := (124060547/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784182919/832233314 : ℝ) ^ p + (410605537/416116657 : ℝ) ^ p := by
    exact cert_lt (x := (784182919/832233314 : ℝ)) (y := (410605537/416116657 : ℝ)) (X := (26040413537843/100000000000000 : ℝ)) (Y := (73959587270153/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921401327/1000000000 : ℝ)) (n' := (416116657/500000000 : ℝ)) (Ab := (784182919/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (28793809/31250000 : ℝ) ^ p + (124060533/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (28793809/31250000 : ℝ)) (y := (124060533/125000000 : ℝ)) (X := (7845684545069/50000000000000 : ℝ)) (Y := (16861729469237/20000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124060533/125000000 : ℝ) ^ p + (28793809/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (124060533/125000000 : ℝ)) (y := (28793809/31250000 : ℝ)) (X := (16861729469237/20000000000000 : ℝ)) (Y := (7845684545069/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239235769/125000000 : ℝ)) (τ := (28793809/31250000 : ℝ)) (σ := (124060533/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784183522/832233979 : ℝ) ^ p + (821211739/832233979 : ℝ) ^ p := by
    exact cert_lt (x := (784183522/832233979 : ℝ)) (y := (821211739/832233979 : ℝ)) (X := (26040395803117/100000000000000 : ℝ)) (Y := (73959605216431/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (28793809/31250000 : ℝ)) (n' := (832233979/1000000000 : ℝ)) (Ab := (392091761/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (921401913/1000000000 : ℝ) ^ p + (992484259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921401913/1000000000 : ℝ)) (y := (992484259/1000000000 : ℝ)) (X := (1569137872267/10000000000000 : ℝ)) (Y := (42154318868273/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992484259/1000000000 : ℝ) ^ p + (921401913/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992484259/1000000000 : ℝ)) (y := (921401913/1000000000 : ℝ)) (X := (42154318868273/50000000000000 : ℝ)) (Y := (1569137872267/10000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478471543/250000000 : ℝ)) (τ := (921401913/1000000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784183549/832234009 : ℝ) ^ p + (821211769/832234009 : ℝ) ^ p := by
    exact cert_lt (x := (784183549/832234009 : ℝ)) (y := (821211769/832234009 : ℝ)) (X := (13020197425267/50000000000000 : ℝ)) (Y := (73959606026037/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (921401913/1000000000 : ℝ)) (n' := (832234009/1000000000 : ℝ)) (Ab := (784183549/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (460700957/500000000 : ℝ) ^ p + (992484259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460700957/500000000 : ℝ)) (y := (992484259/1000000000 : ℝ)) (X := (15691379107971/100000000000000 : ℝ)) (Y := (42154318868273/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992484259/1000000000 : ℝ) ^ p + (460700957/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992484259/1000000000 : ℝ)) (y := (460700957/500000000 : ℝ)) (X := (42154318868273/50000000000000 : ℝ)) (Y := (15691379107971/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (78418355/83223401 : ℝ) ^ p + (82121177/83223401 : ℝ) ^ p := by
    exact cert_lt (x := (78418355/83223401 : ℝ)) (y := (82121177/83223401 : ℝ)) (X := (3255049361739/12500000000000 : ℝ)) (Y := (73959606053023/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (n' := (83223401/100000000 : ℝ)) (Ab := (15683671/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1913886173/1000000000 : ℝ)) (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1650756146/1806977469 : ℝ) ^ p + (598651743/602325823 : ℝ) ^ p := by
    exact cert_lt (x := (1650756146/1806977469 : ℝ)) (y := (598651743/602325823 : ℝ)) (X := (12927675614201/100000000000000 : ℝ)) (Y := (87072324702549/100000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108438021/1193022531 : ℝ) ^ p + (394000097/397674177 : ℝ) ^ p := by
    exact cert_lt (x := (1108438021/1193022531 : ℝ)) (y := (394000097/397674177 : ℝ)) (X := (378835034317/2000000000000 : ℝ)) (Y := (40529124446547/50000000000000 : ℝ)) 181 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992484259/1000000000 : ℝ)) (U := (1193022531/1000000000 : ℝ)) (Ab := (825378073/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (460700957/500000000 : ℝ)) (σ := (992484259/1000000000 : ℝ)) (Ab := (1108438021/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab051
