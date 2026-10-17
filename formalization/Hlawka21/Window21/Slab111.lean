import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 111, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab111 (p : ℝ) (hpa : (783/32 : ℝ) ≤ p) (hpb : p ≤ (49/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2088891628571/106879500000000 : ℝ) (2010593/200000000 : ℝ) (4000000641277/21375900000000 : ℝ) (3033/2500 : ℝ) (486052371/250000000 : ℝ) (972069617/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238756801/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11149/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1157/2500 : ℝ)
      else (7777/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5927/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2088891628571/106879500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2010593/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (184429563/200000000 : ℝ) ^ p + (9939909/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (184429563/200000000 : ℝ)) (y := (9939909/10000000 : ℝ)) (X := (1372818957719/10000000000000 : ℝ)) (Y := (43135914649497/50000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (9939909/10000000 : ℝ) ^ p + (184429563/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (9939909/10000000 : ℝ)) (y := (184429563/200000000 : ℝ)) (X := (43135914649497/50000000000000 : ℝ)) (Y := (1372818957719/10000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (383227743/200000000 : ℝ)) (τ := (184429563/200000000 : ℝ)) (σ := (9939909/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (196651312/207840327 : ℝ) ^ p + (821308343/831361308 : ℝ) ^ p := by
    exact cert_lt (x := (196651312/207840327 : ℝ)) (y := (821308343/831361308 : ℝ)) (X := (12887309819569/50000000000000 : ℝ)) (Y := (74225381879101/100000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184429563/200000000 : ℝ)) (n' := (207840327/250000000 : ℝ)) (Ab := (12290707/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (927668529/1000000000 : ℝ) ^ p + (496480919/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (927668529/1000000000 : ℝ)) (y := (496480919/500000000 : ℝ)) (X := (1986251271629/12500000000000 : ℝ)) (Y := (84110006396201/100000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496480919/500000000 : ℝ) ^ p + (927668529/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496480919/500000000 : ℝ)) (y := (927668529/1000000000 : ℝ)) (X := (84110006396201/100000000000000 : ℝ)) (Y := (1986251271629/12500000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1920630367/1000000000 : ℝ)) (τ := (927668529/1000000000 : ℝ)) (σ := (496480919/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (20321607/21483766 : ℝ) ^ p + (63677993/64451298 : ℝ) ^ p := by
    exact cert_lt (x := (20321607/21483766 : ℝ)) (y := (63677993/64451298 : ℝ)) (X := (25601596830713/100000000000000 : ℝ)) (Y := (9299800497379/12500000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (927668529/1000000000 : ℝ)) (n' := (418933437/500000000 : ℝ)) (Ab := (792542673/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (927897529/1000000000 : ℝ) ^ p + (992915371/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927897529/1000000000 : ℝ)) (y := (992915371/1000000000 : ℝ)) (X := (1998298943483/12500000000000 : ℝ)) (Y := (2100340659221/2500000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992915371/1000000000 : ℝ) ^ p + (927897529/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992915371/1000000000 : ℝ)) (y := (927897529/1000000000 : ℝ)) (X := (2100340659221/2500000000000 : ℝ)) (Y := (1998298943483/12500000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (19208129/10000000 : ℝ)) (τ := (927897529/1000000000 : ℝ)) (σ := (992915371/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (264262723/279378635 : ℝ) ^ p + (165616588/167627181 : ℝ) ^ p := by
    exact cert_lt (x := (264262723/279378635 : ℝ)) (y := (165616588/167627181 : ℝ)) (X := (5118898319609/20000000000000 : ℝ)) (Y := (4650344346819/6250000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (927897529/1000000000 : ℝ)) (n' := (167627181/200000000 : ℝ)) (Ab := (792788169/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (231976733/250000000 : ℝ) ^ p + (62057091/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (231976733/250000000 : ℝ)) (y := (62057091/62500000 : ℝ)) (X := (999397564837/6250000000000 : ℝ)) (Y := (16801931324937/20000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (62057091/62500000 : ℝ) ^ p + (231976733/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (62057091/62500000 : ℝ)) (y := (231976733/250000000 : ℝ)) (X := (16801931324937/20000000000000 : ℝ)) (Y := (999397564837/6250000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (480205097/250000000 : ℝ)) (τ := (231976733/250000000 : ℝ)) (σ := (62057091/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (396399124/419073475 : ℝ) ^ p + (165618797/167629390 : ℝ) ^ p := by
    exact cert_lt (x := (396399124/419073475 : ℝ)) (y := (165618797/167629390 : ℝ)) (X := (2559420020917/10000000000000 : ℝ)) (Y := (1860145029573/2500000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (231976733/250000000 : ℝ)) (n' := (16762939/20000000 : ℝ)) (Ab := (99099781/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (463953659/500000000 : ℝ) ^ p + (992913377/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (463953659/500000000 : ℝ)) (y := (992913377/1000000000 : ℝ)) (X := (3997631002007/25000000000000 : ℝ)) (Y := (84009492863647/100000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992913377/1000000000 : ℝ) ^ p + (463953659/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992913377/1000000000 : ℝ)) (y := (463953659/500000000 : ℝ)) (X := (84009492863647/100000000000000 : ℝ)) (Y := (3997631002007/25000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (384164139/200000000 : ℝ)) (τ := (463953659/500000000 : ℝ)) (σ := (992913377/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (792798661/838147403 : ℝ) ^ p + (828094438/838147403 : ℝ) ^ p := by
    exact cert_lt (x := (792798661/838147403 : ℝ)) (y := (828094438/838147403 : ℝ)) (X := (1279709397873/5000000000000 : ℝ)) (Y := (37202906571929/50000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (463953659/500000000 : ℝ)) (n' := (838147403/1000000000 : ℝ)) (Ab := (792798661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (463953667/500000000 : ℝ) ^ p + (496456687/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (463953667/500000000 : ℝ)) (y := (496456687/500000000 : ℝ)) (X := (7995265381661/50000000000000 : ℝ)) (Y := (84009486644879/100000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496456687/500000000 : ℝ) ^ p + (463953667/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496456687/500000000 : ℝ)) (y := (463953667/500000000 : ℝ)) (X := (84009486644879/100000000000000 : ℝ)) (Y := (7995265381661/50000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (480205177/250000000 : ℝ)) (τ := (463953667/500000000 : ℝ)) (σ := (496456687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (18876159/19955891 : ℝ) ^ p + (828094457/838147422 : ℝ) ^ p := by
    exact cert_lt (x := (18876159/19955891 : ℝ)) (y := (828094457/838147422 : ℝ)) (X := (12797093594337/50000000000000 : ℝ)) (Y := (74405813645531/100000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (463953667/500000000 : ℝ)) (n' := (419073711/500000000 : ℝ)) (Ab := (396399339/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (480205177/250000000 : ℝ)) (τ := (463953667/500000000 : ℝ)) (σ := (496456687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (463953667/500000000 : ℝ)) (n' := (419073711/500000000 : ℝ)) (Ab := (396399339/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (480205177/250000000 : ℝ)) (τ := (463953667/500000000 : ℝ)) (σ := (496456687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (463953667/500000000 : ℝ)) (n' := (419073711/500000000 : ℝ)) (Ab := (396399339/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (480205177/250000000 : ℝ)) (τ := (463953667/500000000 : ℝ)) (σ := (496456687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (463953667/500000000 : ℝ)) (n' := (419073711/500000000 : ℝ)) (Ab := (396399339/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (480205177/250000000 : ℝ)) (τ := (463953667/500000000 : ℝ)) (σ := (496456687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (463953667/500000000 : ℝ)) (n' := (419073711/500000000 : ℝ)) (Ab := (396399339/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (480205177/250000000 : ℝ)) (τ := (463953667/500000000 : ℝ)) (σ := (496456687/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (332148439/361243199 : ℝ) ^ p + (359232606/361243199 : ℝ) ^ p := by
    exact cert_lt (x := (332148439/361243199 : ℝ)) (y := (359232606/361243199 : ℝ)) (X := (12780479168481/100000000000000 : ℝ)) (Y := (1362805017347/1562500000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1114853517/1193784005 : ℝ) ^ p + (236746208/238756801 : ℝ) ^ p := by
    exact cert_lt (x := (1114853517/1193784005 : ℝ)) (y := (236746208/238756801 : ℝ)) (X := (9356755744717/50000000000000 : ℝ)) (Y := (40643244527697/50000000000000 : ℝ)) 49 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496456687/500000000 : ℝ)) (U := (238756801/200000000 : ℝ)) (Ab := (332148439/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (463953667/500000000 : ℝ)) (σ := (496456687/500000000 : ℝ)) (Ab := (1114853517/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab111
