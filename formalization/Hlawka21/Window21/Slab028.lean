import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 28, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab028 (p : ℝ) (hpa : (175/8 : ℝ) ≤ p) (hpb : p ≤ (701/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (21187965053/955500000000 : ℝ) (11444319/1000000000 : ℝ) (40000005733/191100000000 : ℝ) (3033/2500 : ℝ) (968853829/500000000 : ℝ) (193762007/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192735599/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5529/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4469/10000 : ℝ)
      else (381/500 : ℝ) ≤ X j i ∧ X j i ≤ (2959/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (21187965053/955500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11444319/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (912410233/1000000000 : ℝ) ^ p + (993440867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (912410233/1000000000 : ℝ)) (y := (993440867/1000000000 : ℝ)) (X := (1678129335569/12500000000000 : ℝ)) (Y := (43287490903059/50000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993440867/1000000000 : ℝ) ^ p + (912410233/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993440867/1000000000 : ℝ)) (y := (912410233/1000000000 : ℝ)) (X := (43287490903059/50000000000000 : ℝ)) (Y := (1678129335569/12500000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (19058511/10000000 : ℝ)) (τ := (912410233/1000000000 : ℝ)) (σ := (993440867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (773800874/822250361 : ℝ) ^ p + (810806042/822250361 : ℝ) ^ p := by
    exact cert_lt (x := (773800874/822250361 : ℝ)) (y := (810806042/822250361 : ℝ)) (X := (26437829095449/100000000000000 : ℝ)) (Y := (73562171755907/100000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (912410233/1000000000 : ℝ)) (n' := (822250361/1000000000 : ℝ)) (Ab := (386900437/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (918284357/1000000000 : ℝ) ^ p + (248091839/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (918284357/1000000000 : ℝ)) (y := (248091839/250000000 : ℝ)) (X := (7725720436499/50000000000000 : ℝ)) (Y := (84548574364227/100000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248091839/250000000 : ℝ) ^ p + (918284357/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248091839/250000000 : ℝ)) (y := (918284357/1000000000 : ℝ)) (X := (84548574364227/100000000000000 : ℝ)) (Y := (7725720436499/50000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1910651713/1000000000 : ℝ)) (τ := (918284357/1000000000 : ℝ)) (σ := (248091839/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (780146716/829270549 : ℝ) ^ p + (817826230/829270549 : ℝ) ^ p := by
    exact cert_lt (x := (780146716/829270549 : ℝ)) (y := (817826230/829270549 : ℝ)) (X := (26245036779531/100000000000000 : ℝ)) (Y := (9219370557667/12500000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (918284357/1000000000 : ℝ)) (n' := (829270549/1000000000 : ℝ)) (Ab := (195036679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (918569111/1000000000 : ℝ) ^ p + (496155451/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (918569111/1000000000 : ℝ)) (y := (496155451/500000000 : ℝ)) (X := (622269728579/4000000000000 : ℝ)) (Y := (42221635973417/50000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496155451/500000000 : ℝ) ^ p + (918569111/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496155451/500000000 : ℝ)) (y := (918569111/1000000000 : ℝ)) (X := (42221635973417/50000000000000 : ℝ)) (Y := (622269728579/4000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1910880013/1000000000 : ℝ)) (τ := (918569111/1000000000 : ℝ)) (σ := (496155451/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (390226633/414804872 : ℝ) ^ p + (818165425/829609744 : ℝ) ^ p := by
    exact cert_lt (x := (390226633/414804872 : ℝ)) (y := (818165425/829609744 : ℝ)) (X := (6558947980621/25000000000000 : ℝ)) (Y := (14752841819351/20000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (918569111/1000000000 : ℝ)) (n' := (51850609/62500000 : ℝ)) (Ab := (390226633/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (918582761/1000000000 : ℝ) ^ p + (198461637/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (918582761/1000000000 : ℝ)) (y := (198461637/200000000 : ℝ)) (X := (15561808162571/100000000000000 : ℝ)) (Y := (659673493313/781250000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198461637/200000000 : ℝ) ^ p + (918582761/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198461637/200000000 : ℝ)) (y := (918582761/1000000000 : ℝ)) (X := (659673493313/781250000000 : ℝ)) (Y := (15561808162571/100000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (955445473/500000000 : ℝ)) (τ := (918582761/1000000000 : ℝ)) (σ := (198461637/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (780467958/829626001 : ℝ) ^ p + (818181682/829626001 : ℝ) ^ p := by
    exact cert_lt (x := (780467958/829626001 : ℝ)) (y := (818181682/829626001 : ℝ)) (X := (1639709301127/6250000000000 : ℝ)) (Y := (73764652013253/100000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (918582761/1000000000 : ℝ)) (n' := (829626001/1000000000 : ℝ)) (Ab := (390233979/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (183716683/200000000 : ℝ) ^ p + (198461611/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (183716683/200000000 : ℝ)) (y := (198461611/200000000 : ℝ)) (X := (1945256359289/12500000000000 : ℝ)) (Y := (84437964816271/100000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198461611/200000000 : ℝ) ^ p + (183716683/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198461611/200000000 : ℝ)) (y := (183716683/200000000 : ℝ)) (X := (84437964816271/100000000000000 : ℝ)) (Y := (1945256359289/12500000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (191089147/100000000 : ℝ)) (τ := (183716683/200000000 : ℝ)) (σ := (198461611/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (390234331/414813390 : ℝ) ^ p + (686971/696580 : ℝ) ^ p := by
    exact cert_lt (x := (390234331/414813390 : ℝ)) (y := (686971/696580 : ℝ)) (X := (26235327579707/100000000000000 : ℝ)) (Y := (36882336618237/50000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (183716683/200000000 : ℝ)) (n' := (41481339/50000000 : ℝ)) (Ab := (390234331/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (459291723/500000000 : ℝ) ^ p + (992308049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459291723/500000000 : ℝ)) (y := (992308049/1000000000 : ℝ)) (X := (15562062379087/100000000000000 : ℝ)) (Y := (10554744203991/12500000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992308049/1000000000 : ℝ) ^ p + (459291723/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992308049/1000000000 : ℝ)) (y := (459291723/500000000 : ℝ)) (X := (10554744203991/12500000000000 : ℝ)) (Y := (15562062379087/100000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (382178299/200000000 : ℝ)) (τ := (459291723/500000000 : ℝ)) (σ := (992308049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (780468696/829626817 : ℝ) ^ p + (818182498/829626817 : ℝ) ^ p := by
    exact cert_lt (x := (780468696/829626817 : ℝ)) (y := (818182498/829626817 : ℝ)) (X := (2623532698499/10000000000000 : ℝ)) (Y := (18441168561127/25000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (459291723/500000000 : ℝ)) (n' := (829626817/1000000000 : ℝ)) (Ab := (97558587/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (918583447/1000000000 : ℝ) ^ p + (992308049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918583447/1000000000 : ℝ)) (y := (992308049/1000000000 : ℝ)) (X := (15562062750209/100000000000000 : ℝ)) (Y := (10554744203991/12500000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992308049/1000000000 : ℝ) ^ p + (918583447/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992308049/1000000000 : ℝ)) (y := (918583447/1000000000 : ℝ)) (X := (10554744203991/12500000000000 : ℝ)) (Y := (15562062750209/100000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (238861437/125000000 : ℝ)) (τ := (918583447/1000000000 : ℝ)) (σ := (992308049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (780468697/829626818 : ℝ) ^ p + (818182499/829626818 : ℝ) ^ p := by
    exact cert_lt (x := (780468697/829626818 : ℝ)) (y := (818182499/829626818 : ℝ)) (X := (13117663514311/50000000000000 : ℝ)) (Y := (9220584283969/12500000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (918583447/1000000000 : ℝ)) (n' := (414813409/500000000 : ℝ)) (Ab := (780468697/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (238861437/125000000 : ℝ)) (τ := (918583447/1000000000 : ℝ)) (σ := (992308049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (918583447/1000000000 : ℝ)) (n' := (414813409/500000000 : ℝ)) (Ab := (780468697/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (238861437/125000000 : ℝ)) (τ := (918583447/1000000000 : ℝ)) (σ := (992308049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (918583447/1000000000 : ℝ)) (n' := (414813409/500000000 : ℝ)) (Ab := (780468697/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (238861437/125000000 : ℝ)) (τ := (918583447/1000000000 : ℝ)) (σ := (992308049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (918583447/1000000000 : ℝ)) (n' := (414813409/500000000 : ℝ)) (Ab := (780468697/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (238861437/125000000 : ℝ)) (τ := (918583447/1000000000 : ℝ)) (σ := (992308049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1646495347/1807264401 : ℝ) ^ p + (598606694/602421467 : ℝ) ^ p := by
    exact cert_lt (x := (1646495347/1807264401 : ℝ)) (y := (598606694/602421467 : ℝ)) (X := (3247784057191/25000000000000 : ℝ)) (Y := (43504431997057/50000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1105759979/1192735599 : ℝ) ^ p + (393763760/397578533 : ℝ) ^ p := by
    exact cert_lt (x := (1105759979/1192735599 : ℝ)) (y := (393763760/397578533 : ℝ)) (X := (9519626331853/50000000000000 : ℝ)) (Y := (809607478903/1000000000000 : ℝ)) 701 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992308049/1000000000 : ℝ)) (U := (1192735599/1000000000 : ℝ)) (Ab := (1646495347/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (918583447/1000000000 : ℝ)) (σ := (992308049/1000000000 : ℝ)) (Ab := (1105759979/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab028
