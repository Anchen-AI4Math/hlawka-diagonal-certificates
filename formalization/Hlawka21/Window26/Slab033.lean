import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 33, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab033 (p : ℝ) (hpa : (449/16 : ℝ) ≤ p) (hpb : p ≤ (225/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (288292123127/19890700000000 : ℝ) (928517/125000000 : ℝ) (3200000596721/19890700000000 : ℝ) (591/500 : ℝ) (487827991/250000000 : ℝ) (975602429/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (115667263/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10851/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(277/500 : ℝ)
      else (1639/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11483/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (288292123127/19890700000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (928517/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (234589471/250000000 : ℝ) ^ p + (993521887/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (234589471/250000000 : ℝ)) (y := (993521887/1000000000 : ℝ)) (X := (2088210520753/12500000000000 : ℝ)) (Y := (83294335909987/100000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993521887/1000000000 : ℝ) ^ p + (234589471/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993521887/1000000000 : ℝ)) (y := (234589471/250000000 : ℝ)) (X := (83294335909987/100000000000000 : ℝ)) (Y := (2088210520753/12500000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1931879771/1000000000 : ℝ)) (τ := (234589471/250000000 : ℝ)) (σ := (993521887/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (820206483/866265418 : ℝ) ^ p + (429418641/433132709 : ℝ) ^ p := by
    exact cert_lt (x := (820206483/866265418 : ℝ)) (y := (429418641/433132709 : ℝ)) (X := (1075539093153/5000000000000 : ℝ)) (Y := (78489219416997/100000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (234589471/250000000 : ℝ)) (n' := (433132709/500000000 : ℝ)) (Ab := (820206483/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (23542643/25000000 : ℝ) ^ p + (992767759/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23542643/25000000 : ℝ)) (y := (992767759/1000000000 : ℝ)) (X := (3693135406201/20000000000000 : ℝ)) (Y := (16306868285029/20000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992767759/1000000000 : ℝ) ^ p + (23542643/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (992767759/1000000000 : ℝ)) (y := (23542643/25000000 : ℝ)) (X := (16306868285029/20000000000000 : ℝ)) (Y := (3693135406201/20000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1934473479/1000000000 : ℝ)) (τ := (23542643/25000000 : ℝ)) (σ := (992767759/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (411865233/435054440 : ℝ) ^ p + (107835093/108763610 : ℝ) ^ p := by
    exact cert_lt (x := (411865233/435054440 : ℝ)) (y := (107835093/108763610 : ℝ)) (X := (10713200351343/50000000000000 : ℝ)) (Y := (19643400146459/25000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (23542643/25000000 : ℝ)) (n' := (10876361/12500000 : ℝ)) (Ab := (411865233/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (470901429/500000000 : ℝ) ^ p + (992744527/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470901429/500000000 : ℝ)) (y := (992744527/1000000000 : ℝ)) (X := (144682213171/781250000000 : ℝ)) (Y := (40740347906629/50000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992744527/1000000000 : ℝ) ^ p + (470901429/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992744527/1000000000 : ℝ)) (y := (470901429/500000000 : ℝ)) (X := (40740347906629/50000000000000 : ℝ)) (Y := (144682213171/781250000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (386909477/200000000 : ℝ)) (τ := (470901429/500000000 : ℝ)) (σ := (992744527/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823832521/870220196 : ℝ) ^ p + (215698015/217555049 : ℝ) ^ p := by
    exact cert_lt (x := (823832521/870220196 : ℝ)) (y := (215698015/217555049 : ℝ)) (X := (10711983366777/50000000000000 : ℝ)) (Y := (39288017330121/50000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (470901429/500000000 : ℝ)) (n' := (217555049/250000000 : ℝ)) (Ab := (823832521/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (941805661/1000000000 : ℝ) ^ p + (198548771/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (941805661/1000000000 : ℝ)) (y := (198548771/200000000 : ℝ)) (X := (2315109190437/12500000000000 : ℝ)) (Y := (10184893073421/12500000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198548771/200000000 : ℝ) ^ p + (941805661/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198548771/200000000 : ℝ)) (y := (941805661/1000000000 : ℝ)) (X := (10184893073421/12500000000000 : ℝ)) (Y := (2315109190437/12500000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (483637379/250000000 : ℝ)) (τ := (941805661/1000000000 : ℝ)) (σ := (198548771/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (823835465/870223408 : ℝ) ^ p + (107849409/108777926 : ℝ) ^ p := by
    exact cert_lt (x := (823835465/870223408 : ℝ)) (y := (107849409/108777926 : ℝ)) (X := (2677986993461/12500000000000 : ℝ)) (Y := (19644026221697/25000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (941805661/1000000000 : ℝ)) (n' := (54388963/62500000 : ℝ)) (Ab := (164767093/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (941805741/1000000000 : ℝ) ^ p + (248185959/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (941805741/1000000000 : ℝ)) (y := (248185959/250000000 : ℝ)) (X := (1852091777043/10000000000000 : ℝ)) (Y := (81479100728717/100000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248185959/250000000 : ℝ) ^ p + (941805741/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248185959/250000000 : ℝ)) (y := (941805741/1000000000 : ℝ)) (X := (81479100728717/100000000000000 : ℝ)) (Y := (1852091777043/10000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1934549577/1000000000 : ℝ)) (τ := (941805741/1000000000 : ℝ)) (σ := (248185959/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (5492237/5801490 : ℝ) ^ p + (215698841/217555875 : ℝ) ^ p := by
    exact cert_lt (x := (5492237/5801490 : ℝ)) (y := (215698841/217555875 : ℝ)) (X := (10711947207393/50000000000000 : ℝ)) (Y := (19644026724563/25000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (941805741/1000000000 : ℝ)) (n' := (1740447/2000000 : ℝ)) (Ab := (16476711/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (58862859/62500000 : ℝ) ^ p + (198548767/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (58862859/62500000 : ℝ)) (y := (198548767/200000000 : ℝ)) (X := (4630229857423/25000000000000 : ℝ)) (Y := (81479098420367/100000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198548767/200000000 : ℝ) ^ p + (58862859/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (198548767/200000000 : ℝ)) (y := (58862859/62500000 : ℝ)) (X := (81479098420367/100000000000000 : ℝ)) (Y := (4630229857423/25000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1934549579/1000000000 : ℝ)) (τ := (58862859/62500000 : ℝ)) (σ := (198548767/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (823835552/870223503 : ℝ) ^ p + (862795367/870223503 : ℝ) ^ p := by
    exact cert_lt (x := (823835552/870223503 : ℝ)) (y := (862795367/870223503 : ℝ)) (X := (5355973450089/25000000000000 : ℝ)) (Y := (78576106963843/100000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (58862859/62500000 : ℝ)) (n' := (870223503/1000000000 : ℝ)) (Ab := (25744861/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1934549579/1000000000 : ℝ)) (τ := (58862859/62500000 : ℝ)) (σ := (198548767/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (58862859/62500000 : ℝ)) (n' := (870223503/1000000000 : ℝ)) (Ab := (25744861/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1934549579/1000000000 : ℝ)) (τ := (58862859/62500000 : ℝ)) (σ := (198548767/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (58862859/62500000 : ℝ)) (n' := (870223503/1000000000 : ℝ)) (Ab := (25744861/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1934549579/1000000000 : ℝ)) (τ := (58862859/62500000 : ℝ)) (σ := (198548767/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (58862859/62500000 : ℝ)) (n' := (870223503/1000000000 : ℝ)) (Ab := (25744861/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1934549579/1000000000 : ℝ)) (τ := (58862859/62500000 : ℝ)) (σ := (198548767/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (58862859/62500000 : ℝ)) (n' := (870223503/1000000000 : ℝ)) (Ab := (25744861/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1934549579/1000000000 : ℝ)) (τ := (58862859/62500000 : ℝ)) (σ := (198548767/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (851358977/921663685 : ℝ) ^ p + (917949617/921663685 : ℝ) ^ p := by
    exact cert_lt (x := (851358977/921663685 : ℝ)) (y := (917949617/921663685 : ℝ)) (X := (41935264947/390625000000 : ℝ)) (Y := (44632286203111/50000000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (542532854/578336315 : ℝ) ^ p + (574622247/578336315 : ℝ) ^ p := by
    exact cert_lt (x := (542532854/578336315 : ℝ)) (y := (574622247/578336315 : ℝ)) (X := (4143305213637/25000000000000 : ℝ)) (Y := (2085669491017/2500000000000 : ℝ)) 225 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198548767/200000000 : ℝ)) (U := (115667263/100000000 : ℝ)) (Ab := (851358977/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (58862859/62500000 : ℝ)) (σ := (198548767/200000000 : ℝ)) (Ab := (271266427/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab033
