import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 69, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab069 (p : ℝ) (hpa : (741/32 : ℝ) ≤ p) (hpb : p ≤ (371/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1051597668313/50573250000000 : ℝ) (2142539/200000000 : ℝ) (4000000606879/20229300000000 : ℝ) (3033/2500 : ℝ) (485274621/250000000 : ℝ) (121313761/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596624969/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2221/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(569/1250 : ℝ)
      else (7703/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2369/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1051597668313/50573250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2142539/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (183501213/200000000 : ℝ) ^ p + (993723917/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183501213/200000000 : ℝ)) (y := (993723917/1000000000 : ℝ)) (X := (13582974435849/100000000000000 : ℝ)) (Y := (43208521915363/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993723917/1000000000 : ℝ) ^ p + (183501213/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993723917/1000000000 : ℝ)) (y := (183501213/200000000 : ℝ)) (X := (43208521915363/50000000000000 : ℝ)) (Y := (13582974435849/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (955614991/500000000 : ℝ)) (τ := (183501213/200000000 : ℝ)) (σ := (993723917/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (780490595/827054389 : ℝ) ^ p + (116620242/118150627 : ℝ) ^ p := by
    exact cert_lt (x := (780490595/827054389 : ℝ)) (y := (116620242/118150627 : ℝ)) (X := (26088804580317/100000000000000 : ℝ)) (Y := (36955598244941/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (183501213/200000000 : ℝ)) (n' := (827054389/1000000000 : ℝ)) (Ab := (156098119/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (923207339/1000000000 : ℝ) ^ p + (496335567/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (923207339/1000000000 : ℝ)) (y := (496335567/500000000 : ℝ)) (X := (15681092562457/100000000000000 : ℝ)) (Y := (84318923636823/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496335567/500000000 : ℝ) ^ p + (923207339/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496335567/500000000 : ℝ)) (y := (923207339/1000000000 : ℝ)) (X := (84318923636823/100000000000000 : ℝ)) (Y := (15681092562457/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1915878473/1000000000 : ℝ)) (τ := (923207339/1000000000 : ℝ)) (σ := (496335567/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (786634985/833817949 : ℝ) ^ p + (823105254/833817949 : ℝ) ^ p := by
    exact cert_lt (x := (786634985/833817949 : ℝ)) (y := (823105254/833817949 : ℝ)) (X := (25906159641799/100000000000000 : ℝ)) (Y := (74093841564739/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (923207339/1000000000 : ℝ)) (n' := (833817949/1000000000 : ℝ)) (Ab := (157326997/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (923462483/1000000000 : ℝ) ^ p + (124077491/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (923462483/1000000000 : ℝ)) (y := (124077491/125000000 : ℝ)) (X := (7890944877713/50000000000000 : ℝ)) (Y := (84218127026049/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124077491/125000000 : ℝ) ^ p + (923462483/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124077491/125000000 : ℝ)) (y := (923462483/1000000000 : ℝ)) (X := (84218127026049/100000000000000 : ℝ)) (Y := (7890944877713/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1916082411/1000000000 : ℝ)) (τ := (923462483/1000000000 : ℝ)) (σ := (124077491/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (196727260/208529919 : ℝ) ^ p + (823406981/834119676 : ℝ) ^ p := by
    exact cert_lt (x := (196727260/208529919 : ℝ)) (y := (823406981/834119676 : ℝ)) (X := (25898070599929/100000000000000 : ℝ)) (Y := (37050965217757/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (923462483/1000000000 : ℝ)) (n' := (208529919/250000000 : ℝ)) (Ab := (9836363/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (46173689/50000000 : ℝ) ^ p + (248154413/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (46173689/50000000 : ℝ)) (y := (248154413/250000000 : ℝ)) (X := (15786367050789/100000000000000 : ℝ)) (Y := (84213649504071/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248154413/250000000 : ℝ) ^ p + (46173689/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (248154413/250000000 : ℝ)) (y := (46173689/50000000 : ℝ)) (X := (84213649504071/100000000000000 : ℝ)) (Y := (15786367050789/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239511429/125000000 : ℝ)) (τ := (46173689/50000000 : ℝ)) (σ := (248154413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (786921172/834133033 : ℝ) ^ p + (823420338/834133033 : ℝ) ^ p := by
    exact cert_lt (x := (786921172/834133033 : ℝ)) (y := (823420338/834133033 : ℝ)) (X := (12948856349819/50000000000000 : ℝ)) (Y := (37051144200953/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (46173689/50000000 : ℝ)) (n' := (834133033/1000000000 : ℝ)) (Ab := (196730293/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (23086857/25000000 : ℝ) ^ p + (992617551/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23086857/25000000 : ℝ)) (y := (992617551/1000000000 : ℝ)) (X := (7893282620949/50000000000000 : ℝ)) (Y := (42106725407197/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992617551/1000000000 : ℝ) ^ p + (23086857/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (992617551/1000000000 : ℝ)) (y := (23086857/25000000 : ℝ)) (X := (42106725407197/50000000000000 : ℝ)) (Y := (7893282620949/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1916091831/1000000000 : ℝ)) (τ := (23086857/25000000 : ℝ)) (σ := (992617551/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (786921709/834133624 : ℝ) ^ p + (823420929/834133624 : ℝ) ^ p := by
    exact cert_lt (x := (786921709/834133624 : ℝ)) (y := (823420929/834133624 : ℝ)) (X := (12948848509137/50000000000000 : ℝ)) (Y := (37051152120213/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (23086857/25000000 : ℝ)) (n' := (104266703/125000000 : ℝ)) (Ab := (786921709/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461737151/500000000 : ℝ) ^ p + (992617547/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461737151/500000000 : ℝ)) (y := (992617547/1000000000 : ℝ)) (X := (15786573962361/100000000000000 : ℝ)) (Y := (16842688589101/20000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992617547/1000000000 : ℝ) ^ p + (461737151/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992617547/1000000000 : ℝ)) (y := (461737151/500000000 : ℝ)) (X := (16842688589101/20000000000000 : ℝ)) (Y := (15786573962361/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1916091849/1000000000 : ℝ)) (τ := (461737151/500000000 : ℝ)) (σ := (992617547/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (131153622/139022275 : ℝ) ^ p + (23526313/23832390 : ℝ) ^ p := by
    exact cert_lt (x := (131153622/139022275 : ℝ)) (y := (23526313/23832390 : ℝ)) (X := (5179539170389/20000000000000 : ℝ)) (Y := (74102304937213/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461737151/500000000 : ℝ)) (n' := (16682673/20000000 : ℝ)) (Ab := (196730433/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (7214643/7812500 : ℝ) ^ p + (496308773/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (7214643/7812500 : ℝ)) (y := (496308773/500000000 : ℝ)) (X := (15786574755131/100000000000000 : ℝ)) (Y := (84213440978283/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496308773/500000000 : ℝ) ^ p + (7214643/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (496308773/500000000 : ℝ)) (y := (7214643/7812500 : ℝ)) (X := (84213440978283/100000000000000 : ℝ)) (Y := (15786574755131/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (38321837/20000000 : ℝ)) (τ := (7214643/7812500 : ℝ)) (σ := (496308773/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (262307245/278044551 : ℝ) ^ p + (823420958/834133653 : ℝ) ^ p := by
    exact cert_lt (x := (262307245/278044551 : ℝ)) (y := (823420958/834133653 : ℝ)) (X := (323721199769/1250000000000 : ℝ)) (Y := (74102305017611/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (7214643/7812500 : ℝ)) (n' := (834133653/1000000000 : ℝ)) (Ab := (157384347/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (38321837/20000000 : ℝ)) (τ := (7214643/7812500 : ℝ)) (σ := (496308773/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (7214643/7812500 : ℝ)) (n' := (834133653/1000000000 : ℝ)) (Ab := (157384347/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (38321837/20000000 : ℝ)) (τ := (7214643/7812500 : ℝ)) (σ := (496308773/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (7214643/7812500 : ℝ)) (n' := (834133653/1000000000 : ℝ)) (Ab := (157384347/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (38321837/20000000 : ℝ)) (τ := (7214643/7812500 : ℝ)) (σ := (496308773/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (7214643/7812500 : ℝ)) (n' := (834133653/1000000000 : ℝ)) (Ab := (157384347/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (38321837/20000000 : ℝ)) (τ := (7214643/7812500 : ℝ)) (σ := (496308773/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (826957150/903375031 : ℝ) ^ p + (1796037367/1806750062 : ℝ) ^ p := by
    exact cert_lt (x := (826957150/903375031 : ℝ)) (y := (1796037367/1806750062 : ℝ)) (X := (1288089523353/10000000000000 : ℝ)) (Y := (43559552561423/50000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1110445879/1193249938 : ℝ) ^ p + (1182537243/1193249938 : ℝ) ^ p := by
    exact cert_lt (x := (1110445879/1193249938 : ℝ)) (y := (1182537243/1193249938 : ℝ)) (X := (9434764811287/50000000000000 : ℝ)) (Y := (81130470982087/100000000000000 : ℝ)) 371 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496308773/500000000 : ℝ)) (U := (596624969/500000000 : ℝ)) (Ab := (16539143/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (7214643/7812500 : ℝ)) (σ := (496308773/500000000 : ℝ)) (Ab := (1110445879/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab069
