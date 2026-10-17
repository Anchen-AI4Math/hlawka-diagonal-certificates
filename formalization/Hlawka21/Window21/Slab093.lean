import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 93, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab093 (p : ℝ) (hpa : (765/32 : ℝ) ≤ p) (hpb : p ≤ (383/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (209483139413/10442250000000 : ℝ) (10325643/1000000000 : ℝ) (800000125307/4176900000000 : ℝ) (3033/2500 : ℝ) (971458683/500000000 : ℝ) (121427739/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193554979/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11131/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1149/2500 : ℝ)
      else (3873/5000 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (209483139413/10442250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10325643/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (460111907/500000000 : ℝ) ^ p + (496939581/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460111907/500000000 : ℝ)) (y := (496939581/500000000 : ℝ)) (X := (6833920048499/50000000000000 : ℝ)) (Y := (17266435467961/20000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496939581/500000000 : ℝ) ^ p + (460111907/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496939581/500000000 : ℝ)) (y := (460111907/500000000 : ℝ)) (X := (17266435467961/20000000000000 : ℝ)) (Y := (6833920048499/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (29907859/15625000 : ℝ)) (τ := (460111907/500000000 : ℝ)) (σ := (496939581/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784068213/829584101 : ℝ) ^ p + (819258458/829584101 : ℝ) ^ p := by
    exact cert_lt (x := (784068213/829584101 : ℝ)) (y := (819258458/829584101 : ℝ)) (X := (12952211238899/50000000000000 : ℝ)) (Y := (4630973649517/6250000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (460111907/500000000 : ℝ)) (n' := (829584101/1000000000 : ℝ)) (Ab := (784068213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46291099/50000000 : ℝ) ^ p + (992839713/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46291099/50000000 : ℝ)) (y := (992839713/1000000000 : ℝ)) (X := (7901721683371/50000000000000 : ℝ)) (Y := (84196574419371/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992839713/1000000000 : ℝ) ^ p + (46291099/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992839713/1000000000 : ℝ)) (y := (46291099/50000000 : ℝ)) (X := (84196574419371/100000000000000 : ℝ)) (Y := (7901721683371/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918661693/1000000000 : ℝ)) (τ := (46291099/50000000 : ℝ)) (σ := (992839713/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (158018813/167239860 : ℝ) ^ p + (275291219/278733100 : ℝ) ^ p := by
    exact cert_lt (x := (158018813/167239860 : ℝ)) (y := (275291219/278733100 : ℝ)) (X := (25727372436011/100000000000000 : ℝ)) (Y := (18568157214523/25000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46291099/50000000 : ℝ)) (n' := (8361993/10000000 : ℝ)) (Ab := (158018813/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (92606171/100000000 : ℝ) ^ p + (124098911/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (92606171/100000000 : ℝ)) (y := (124098911/125000000 : ℝ)) (X := (993855596491/6250000000000 : ℝ)) (Y := (84098327082747/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124098911/125000000 : ℝ) ^ p + (92606171/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (124098911/125000000 : ℝ)) (y := (92606171/100000000 : ℝ)) (X := (84098327082747/100000000000000 : ℝ)) (Y := (993855596491/6250000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (959426499/500000000 : ℝ)) (τ := (92606171/100000000 : ℝ)) (σ := (124098911/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (790351268/836481707 : ℝ) ^ p + (826156064/836481707 : ℝ) ^ p := by
    exact cert_lt (x := (790351268/836481707 : ℝ)) (y := (826156064/836481707 : ℝ)) (X := (12859933718727/50000000000000 : ℝ)) (Y := (74280133865293/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (92606171/100000000 : ℝ)) (n' := (836481707/1000000000 : ℝ)) (Ab := (197587817/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (92607187/100000000 : ℝ) ^ p + (248197307/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (92607187/100000000 : ℝ)) (y := (248197307/250000000 : ℝ)) (X := (1988233277123/12500000000000 : ℝ)) (Y := (84094150076969/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248197307/250000000 : ℝ) ^ p + (92607187/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248197307/250000000 : ℝ)) (y := (92607187/100000000 : ℝ)) (X := (84094150076969/100000000000000 : ℝ)) (Y := (1988233277123/12500000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (959430549/500000000 : ℝ)) (τ := (92607187/100000000 : ℝ)) (σ := (248197307/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (790362167/836493674 : ℝ) ^ p + (826168031/836493674 : ℝ) ^ p := by
    exact cert_lt (x := (790362167/836493674 : ℝ)) (y := (826168031/836493674 : ℝ)) (X := (3214943698339/12500000000000 : ℝ)) (Y := (18570112948547/25000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (92607187/100000000 : ℝ)) (n' := (418246837/500000000 : ℝ)) (Ab := (790362167/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (9260723/10000000 : ℝ) ^ p + (992789141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (9260723/10000000 : ℝ)) (y := (992789141/1000000000 : ℝ)) (X := (3181208601763/20000000000000 : ℝ)) (Y := (84093973673819/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992789141/1000000000 : ℝ) ^ p + (9260723/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (992789141/1000000000 : ℝ)) (y := (9260723/10000000 : ℝ)) (X := (84093973673819/100000000000000 : ℝ)) (Y := (3181208601763/20000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1918861441/1000000000 : ℝ)) (τ := (9260723/10000000 : ℝ)) (σ := (992789141/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (197590657/209123545 : ℝ) ^ p + (826168537/836494180 : ℝ) ^ p := by
    exact cert_lt (x := (197590657/209123545 : ℝ)) (y := (826168537/836494180 : ℝ)) (X := (514390725411/2000000000000 : ℝ)) (Y := (37140232618493/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (9260723/10000000 : ℝ)) (n' := (41824709/50000000 : ℝ)) (Ab := (197590657/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926072317/1000000000 : ℝ) ^ p + (496394569/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (926072317/1000000000 : ℝ)) (y := (496394569/500000000 : ℝ)) (X := (7953024999149/50000000000000 : ℝ)) (Y := (42046983795479/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496394569/500000000 : ℝ) ^ p + (926072317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496394569/500000000 : ℝ)) (y := (926072317/1000000000 : ℝ)) (X := (42046983795479/50000000000000 : ℝ)) (Y := (7953024999149/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383772291/200000000 : ℝ)) (τ := (926072317/1000000000 : ℝ)) (σ := (496394569/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (395181323/418247100 : ℝ) ^ p + (275389519/278831400 : ℝ) ^ p := by
    exact cert_lt (x := (395181323/418247100 : ℝ)) (y := (275389519/278831400 : ℝ)) (X := (25719535571801/100000000000000 : ℝ)) (Y := (74280465768321/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926072317/1000000000 : ℝ)) (n' := (4182471/5000000 : ℝ)) (Ab := (395181323/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (926072319/1000000000 : ℝ) ^ p + (992789137/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926072319/1000000000 : ℝ)) (y := (992789137/1000000000 : ℝ)) (X := (1590605082059/10000000000000 : ℝ)) (Y := (42046982781669/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992789137/1000000000 : ℝ) ^ p + (926072319/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992789137/1000000000 : ℝ)) (y := (926072319/1000000000 : ℝ)) (X := (42046982781669/50000000000000 : ℝ)) (Y := (1590605082059/10000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (395181324/418247101 : ℝ) ^ p + (826168559/836494202 : ℝ) ^ p := by
    exact cert_lt (x := (395181324/418247101 : ℝ)) (y := (826168559/836494202 : ℝ)) (X := (25719535657719/100000000000000 : ℝ)) (Y := (14856093164291/20000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (n' := (418247101/500000000 : ℝ)) (Ab := (98795331/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (119928841/62500000 : ℝ)) (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657903837/1806445021 : ℝ) ^ p + (1796119378/1806445021 : ℝ) ^ p := by
    exact cert_lt (x := (1657903837/1806445021 : ℝ)) (y := (1796119378/1806445021 : ℝ)) (X := (2564420278821/20000000000000 : ℝ)) (Y := (87177898838901/100000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1113010165/1193554979 : ℝ) ^ p + (1183229336/1193554979 : ℝ) ^ p := by
    exact cert_lt (x := (1113010165/1193554979 : ℝ)) (y := (1183229336/1193554979 : ℝ)) (X := (9389172243059/50000000000000 : ℝ)) (Y := (40610828013071/50000000000000 : ℝ)) 383 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992789137/1000000000 : ℝ)) (U := (1193554979/1000000000 : ℝ)) (Ab := (1657903837/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (926072319/1000000000 : ℝ)) (σ := (992789137/1000000000 : ℝ)) (Ab := (222602033/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab093
