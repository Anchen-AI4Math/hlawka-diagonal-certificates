import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 25, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab025 (p : ℝ) (hpa : (441/16 : ℝ) ≤ p) (hpb : p ≤ (221/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (144470825971/9768150000000 : ℝ) (1895831/250000000 : ℝ) (3200000586089/19536300000000 : ℝ) (591/500 : ℝ) (97522087/50000000 : ℝ) (121895673/125000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578180453/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10837/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2761/5000 : ℝ)
      else (8177/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11479/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (144470825971/9768150000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1895831/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (234296579/250000000 : ℝ) ^ p + (993424467/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (234296579/250000000 : ℝ)) (y := (993424467/1000000000 : ℝ)) (X := (16660635328527/100000000000000 : ℝ)) (Y := (16667876824613/20000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993424467/1000000000 : ℝ) ^ p + (234296579/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993424467/1000000000 : ℝ)) (y := (234296579/250000000 : ℝ)) (X := (16667876824613/20000000000000 : ℝ)) (Y := (16660635328527/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1930610783/1000000000 : ℝ)) (τ := (234296579/250000000 : ℝ)) (σ := (993424467/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (272866193/288437909 : ℝ) ^ p + (857730403/865313727 : ℝ) ^ p := by
    exact cert_lt (x := (272866193/288437909 : ℝ)) (y := (857730403/865313727 : ℝ)) (X := (5396416916981/25000000000000 : ℝ)) (Y := (19603583364603/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (234296579/250000000 : ℝ)) (n' := (865313727/1000000000 : ℝ)) (Ab := (818598579/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940575943/1000000000 : ℝ) ^ p + (992662771/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940575943/1000000000 : ℝ)) (y := (992662771/1000000000 : ℝ)) (X := (9203977972839/50000000000000 : ℝ)) (Y := (81592062379907/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992662771/1000000000 : ℝ) ^ p + (940575943/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992662771/1000000000 : ℝ)) (y := (940575943/1000000000 : ℝ)) (X := (81592062379907/100000000000000 : ℝ)) (Y := (9203977972839/50000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (966619357/500000000 : ℝ)) (τ := (940575943/1000000000 : ℝ)) (σ := (992662771/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822167705/869212044 : ℝ) ^ p + (215407180/217303011 : ℝ) ^ p := by
    exact cert_lt (x := (822167705/869212044 : ℝ)) (y := (215407180/217303011 : ℝ)) (X := (21499728956359/100000000000000 : ℝ)) (Y := (19625067962943/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940575943/1000000000 : ℝ)) (n' := (217303011/250000000 : ℝ)) (Ab := (164433541/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (94067661/100000000 : ℝ) ^ p + (24815969/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (94067661/100000000 : ℝ)) (y := (24815969/25000000 : ℝ)) (X := (4615614724217/25000000000000 : ℝ)) (Y := (81537559572823/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24815969/25000000 : ℝ) ^ p + (94067661/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (24815969/25000000 : ℝ)) (y := (94067661/100000000 : ℝ)) (X := (81537559572823/100000000000000 : ℝ)) (Y := (4615614724217/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (193331537/100000000 : ℝ)) (τ := (94067661/100000000 : ℝ)) (σ := (24815969/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (411136750/434663803 : ℝ) ^ p + (61553163/62094829 : ℝ) ^ p := by
    exact cert_lt (x := (411136750/434663803 : ℝ)) (y := (61553163/62094829 : ℝ)) (X := (5374298016819/25000000000000 : ℝ)) (Y := (39251404515757/50000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (94067661/100000000 : ℝ)) (n' := (434663803/500000000 : ℝ)) (Ab := (1644547/2000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (470339791/500000000 : ℝ) ^ p + (19852761/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (470339791/500000000 : ℝ)) (y := (19852761/20000000 : ℝ)) (X := (577002198539/3125000000000 : ℝ)) (Y := (16307189694207/20000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (19852761/20000000 : ℝ) ^ p + (470339791/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (19852761/20000000 : ℝ)) (y := (470339791/500000000 : ℝ)) (X := (16307189694207/20000000000000 : ℝ)) (Y := (577002198539/3125000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (3776011/1953125 : ℝ)) (τ := (470339791/500000000 : ℝ)) (σ := (19852761/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822276623/869331017 : ℝ) ^ p + (861747693/869331017 : ℝ) ^ p := by
    exact cert_lt (x := (822276623/869331017 : ℝ)) (y := (861747693/869331017 : ℝ)) (X := (171976939281/800000000000 : ℝ)) (Y := (19625720977861/25000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (470339791/500000000 : ℝ)) (n' := (869331017/1000000000 : ℝ)) (Ab := (822276623/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (94067967/100000000 : ℝ) ^ p + (992638029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94067967/100000000 : ℝ)) (y := (992638029/1000000000 : ℝ)) (X := (18464118070039/100000000000000 : ℝ)) (Y := (16307180163839/20000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992638029/1000000000 : ℝ) ^ p + (94067967/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992638029/1000000000 : ℝ)) (y := (94067967/100000000 : ℝ)) (X := (16307180163839/20000000000000 : ℝ)) (Y := (18464118070039/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1933317699/1000000000 : ℝ)) (τ := (94067967/100000000 : ℝ)) (σ := (992638029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (822276715/869331118 : ℝ) ^ p + (430873897/434665559 : ℝ) ^ p := by
    exact cert_lt (x := (822276715/869331118 : ℝ)) (y := (430873897/434665559 : ℝ)) (X := (5374278714609/25000000000000 : ℝ)) (Y := (78502886128637/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (94067967/100000000 : ℝ)) (n' := (434665559/500000000 : ℝ)) (Ab := (164455343/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (940679673/1000000000 : ℝ) ^ p + (248159507/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (940679673/1000000000 : ℝ)) (y := (248159507/250000000 : ℝ)) (X := (73856478787/400000000000 : ℝ)) (Y := (81535898550061/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248159507/250000000 : ℝ) ^ p + (940679673/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248159507/250000000 : ℝ)) (y := (940679673/1000000000 : ℝ)) (X := (81535898550061/100000000000000 : ℝ)) (Y := (73856478787/400000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (74752429/79030102 : ℝ) ^ p + (430873899/434665561 : ℝ) ^ p := by
    exact cert_lt (x := (74752429/79030102 : ℝ)) (y := (430873899/434665561 : ℝ)) (X := (21497115014801/100000000000000 : ℝ)) (Y := (78502886216447/100000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (n' := (434665561/500000000 : ℝ)) (Ab := (822276719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933317701/1000000000 : ℝ)) (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1700713723/1843639094 : ℝ) ^ p + (918027885/921819547 : ℝ) ^ p := by
    exact cert_lt (x := (1700713723/1843639094 : ℝ)) (y := (918027885/921819547 : ℝ)) (X := (10761935024339/100000000000000 : ℝ)) (Y := (11154758159611/12500000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083629333/1156360906 : ℝ) ^ p + (574388791/578180453 : ℝ) ^ p := by
    exact cert_lt (x := (1083629333/1156360906 : ℝ)) (y := (574388791/578180453 : ℝ)) (X := (8309896188101/50000000000000 : ℝ)) (Y := (8338020831289/10000000000000 : ℝ)) 221 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248159507/250000000 : ℝ)) (U := (578180453/500000000 : ℝ)) (Ab := (1700713723/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (940679673/1000000000 : ℝ)) (σ := (248159507/250000000 : ℝ)) (Ab := (1083629333/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab025
