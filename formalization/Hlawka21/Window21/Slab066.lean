import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 66, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab066 (p : ℝ) (hpa : (369/16 : ℝ) ≤ p) (hpb : p ≤ (739/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1052139431899/50368500000000 : ℝ) (10763093/1000000000 : ℝ) (2000000302211/10073700000000 : ℝ) (3033/2500 : ℝ) (97043147/50000000 : ℝ) (970392003/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193211923/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5551/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4547/10000 : ℝ)
      else (7697/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2961/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1052139431899/50368500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10763093/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (917153317/1000000000 : ℝ) ^ p + (993703987/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917153317/1000000000 : ℝ)) (y := (993703987/1000000000 : ℝ)) (X := (13571991432779/100000000000000 : ℝ)) (Y := (86428025280029/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993703987/1000000000 : ℝ) ^ p + (917153317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993703987/1000000000 : ℝ)) (y := (917153317/1000000000 : ℝ)) (X := (86428025280029/100000000000000 : ℝ)) (Y := (13571991432779/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (238857163/125000000 : ℝ)) (τ := (917153317/1000000000 : ℝ)) (σ := (993703987/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (780026752/826724391 : ℝ) ^ p + (815961298/826724391 : ℝ) ^ p := by
    exact cert_lt (x := (780026752/826724391 : ℝ)) (y := (815961298/826724391 : ℝ)) (X := (5222565140643/20000000000000 : ℝ)) (Y := (7388717530421/10000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (917153317/1000000000 : ℝ)) (n' := (826724391/1000000000 : ℝ)) (Ab := (6093959/7812500 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (28839607/31250000 : ℝ) ^ p + (99264959/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (28839607/31250000 : ℝ)) (y := (99264959/100000000 : ℝ)) (X := (1958150632937/12500000000000 : ℝ)) (Y := (84334810891659/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99264959/100000000 : ℝ) ^ p + (28839607/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (99264959/100000000 : ℝ)) (y := (28839607/31250000 : ℝ)) (X := (84334810891659/100000000000000 : ℝ)) (Y := (1958150632937/12500000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957758507/500000000 : ℝ)) (τ := (28839607/31250000 : ℝ)) (σ := (99264959/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (393092985/416753317 : ℝ) ^ p + (822743541/833506634 : ℝ) ^ p := by
    exact cert_lt (x := (393092985/416753317 : ℝ)) (y := (822743541/833506634 : ℝ)) (X := (3241182906363/12500000000000 : ℝ)) (Y := (74070537737651/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (28839607/31250000 : ℝ)) (n' := (416753317/500000000 : ℝ)) (Ab := (78618597/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (923124591/1000000000 : ℝ) ^ p + (992598021/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (923124591/1000000000 : ℝ)) (y := (992598021/1000000000 : ℝ)) (X := (1576632666303/10000000000000 : ℝ)) (Y := (84233689076179/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992598021/1000000000 : ℝ) ^ p + (923124591/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992598021/1000000000 : ℝ)) (y := (923124591/1000000000 : ℝ)) (X := (84233689076179/100000000000000 : ℝ)) (Y := (1576632666303/10000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478930653/250000000 : ℝ)) (τ := (923124591/1000000000 : ℝ)) (σ := (992598021/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (157292448/166762181 : ℝ) ^ p + (823047812/833810905 : ℝ) ^ p := by
    exact cert_lt (x := (157292448/166762181 : ℝ)) (y := (823047812/833810905 : ℝ)) (X := (12960648695989/50000000000000 : ℝ)) (Y := (74078704096559/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (923124591/1000000000 : ℝ)) (n' := (166762181/200000000 : ℝ)) (Ab := (4915389/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (23078401/25000000 : ℝ) ^ p + (992595717/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23078401/25000000 : ℝ)) (y := (992595717/1000000000 : ℝ)) (X := (15770843055959/100000000000000 : ℝ)) (Y := (84229173863463/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992595717/1000000000 : ℝ) ^ p + (23078401/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (992595717/1000000000 : ℝ)) (y := (23078401/25000000 : ℝ)) (X := (84229173863463/100000000000000 : ℝ)) (Y := (15770843055959/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1915731757/1000000000 : ℝ)) (τ := (23078401/25000000 : ℝ)) (σ := (992595717/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (262158179/277941483 : ℝ) ^ p + (823061356/833824449 : ℝ) ^ p := by
    exact cert_lt (x := (262158179/277941483 : ℝ)) (y := (823061356/833824449 : ℝ)) (X := (6480233412493/25000000000000 : ℝ)) (Y := (74079067486753/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (23078401/25000000 : ℝ)) (n' := (833824449/1000000000 : ℝ)) (Ab := (786474537/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (18462731/20000000 : ℝ) ^ p + (496297807/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (18462731/20000000 : ℝ)) (y := (496297807/500000000 : ℝ)) (X := (15771044269169/100000000000000 : ℝ)) (Y := (84228972016913/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496297807/500000000 : ℝ) ^ p + (18462731/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (496297807/500000000 : ℝ)) (y := (18462731/20000000 : ℝ)) (X := (84228972016913/100000000000000 : ℝ)) (Y := (15771044269169/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (478933041/250000000 : ℝ)) (τ := (18462731/20000000 : ℝ)) (σ := (496297807/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (786475085/833825053 : ℝ) ^ p + (823061960/833825053 : ℝ) ^ p := by
    exact cert_lt (x := (786475085/833825053 : ℝ)) (y := (823061960/833825053 : ℝ)) (X := (3240114641581/12500000000000 : ℝ)) (Y := (37039541846023/50000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (18462731/20000000 : ℝ)) (n' := (833825053/1000000000 : ℝ)) (Ab := (157295017/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (230784143/250000000 : ℝ) ^ p + (99259561/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (230784143/250000000 : ℝ)) (y := (99259561/100000000 : ℝ)) (X := (1577105294901/10000000000000 : ℝ)) (Y := (42114482089111/50000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99259561/100000000 : ℝ) ^ p + (230784143/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (99259561/100000000 : ℝ)) (y := (230784143/250000000 : ℝ)) (X := (42114482089111/50000000000000 : ℝ)) (Y := (1577105294901/10000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (957866091/500000000 : ℝ)) (τ := (230784143/250000000 : ℝ)) (σ := (99259561/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (786475109/833825079 : ℝ) ^ p + (823061986/833825079 : ℝ) ^ p := by
    exact cert_lt (x := (786475109/833825079 : ℝ)) (y := (823061986/833825079 : ℝ)) (X := (6480229183539/25000000000000 : ℝ)) (Y := (592632675117/800000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (230784143/250000000 : ℝ)) (n' := (833825079/1000000000 : ℝ)) (Ab := (786475109/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (461568287/500000000 : ℝ) ^ p + (992595609/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461568287/500000000 : ℝ)) (y := (992595609/1000000000 : ℝ)) (X := (7885526869043/50000000000000 : ℝ)) (Y := (84228962218549/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992595609/1000000000 : ℝ) ^ p + (461568287/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992595609/1000000000 : ℝ)) (y := (461568287/500000000 : ℝ)) (X := (84228962218549/100000000000000 : ℝ)) (Y := (7885526869043/50000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1915732183/1000000000 : ℝ)) (τ := (461568287/500000000 : ℝ)) (σ := (992595609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (786475111/833825081 : ℝ) ^ p + (823061988/833825081 : ℝ) ^ p := by
    exact cert_lt (x := (786475111/833825081 : ℝ)) (y := (823061988/833825081 : ℝ)) (X := (129604584103/500000000000 : ℝ)) (Y := (14815816888657/20000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (461568287/500000000 : ℝ)) (n' := (833825081/1000000000 : ℝ)) (Ab := (786475111/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1915732183/1000000000 : ℝ)) (τ := (461568287/500000000 : ℝ)) (σ := (992595609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (461568287/500000000 : ℝ)) (n' := (833825081/1000000000 : ℝ)) (Ab := (786475111/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1915732183/1000000000 : ℝ)) (τ := (461568287/500000000 : ℝ)) (σ := (992595609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (461568287/500000000 : ℝ)) (n' := (833825081/1000000000 : ℝ)) (Ab := (786475111/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1915732183/1000000000 : ℝ)) (τ := (461568287/500000000 : ℝ)) (σ := (992595609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (461568287/500000000 : ℝ)) (n' := (833825081/1000000000 : ℝ)) (Ab := (786475111/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1915732183/1000000000 : ℝ)) (τ := (461568287/500000000 : ℝ)) (σ := (992595609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1653398169/1806788077 : ℝ) ^ p + (1796024984/1806788077 : ℝ) ^ p := by
    exact cert_lt (x := (1653398169/1806788077 : ℝ)) (y := (1796024984/1806788077 : ℝ)) (X := (6444263280999/50000000000000 : ℝ)) (Y := (87111473796247/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1110116411/1193211923 : ℝ) ^ p + (1182448830/1193211923 : ℝ) ^ p := by
    exact cert_lt (x := (1110116411/1193211923 : ℝ)) (y := (1182448830/1193211923 : ℝ)) (X := (2360166415771/12500000000000 : ℝ)) (Y := (81118669387877/100000000000000 : ℝ)) 739 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992595609/1000000000 : ℝ)) (U := (1193211923/1000000000 : ℝ)) (Ab := (1653398169/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (461568287/500000000 : ℝ)) (σ := (992595609/1000000000 : ℝ)) (Ab := (1110116411/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab066
