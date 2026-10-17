import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 13, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab013 (p : ℝ) (hpa : (429/16 : ℝ) ≤ p) (hpb : p ≤ (215/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (289960996271/19004700000000 : ℝ) (7828451/1000000000 : ℝ) (3200000570141/19004700000000 : ℝ) (591/500 : ℝ) (487269119/250000000 : ℝ) (974479649/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1155881967/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5407/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2747/5000 : ℝ)
      else (2037/2500 : ℝ) ≤ X j i ∧ X j i ≤ (717/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (289960996271/19004700000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7828451/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (935343299/1000000000 : ℝ) ^ p + (993272891/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (935343299/1000000000 : ℝ)) (y := (993272891/1000000000 : ℝ)) (X := (16590011184647/100000000000000 : ℝ)) (Y := (41705003494403/50000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993272891/1000000000 : ℝ) ^ p + (935343299/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993272891/1000000000 : ℝ)) (y := (935343299/1000000000 : ℝ)) (X := (41705003494403/50000000000000 : ℝ)) (Y := (16590011184647/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (192861619/100000000 : ℝ)) (τ := (935343299/1000000000 : ℝ)) (σ := (993272891/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (408036977/431903323 : ℝ) ^ p + (855978195/863806646 : ℝ) ^ p := by
    exact cert_lt (x := (408036977/431903323 : ℝ)) (y := (855978195/863806646 : ℝ)) (X := (10851911218371/50000000000000 : ℝ)) (Y := (15659235700793/20000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (935343299/1000000000 : ℝ)) (n' := (431903323/500000000 : ℝ)) (Ab := (408036977/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (18775931/20000000 : ℝ) ^ p + (992499847/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18775931/20000000 : ℝ)) (y := (992499847/1000000000 : ℝ)) (X := (2289647734059/12500000000000 : ℝ)) (Y := (81682835090571/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992499847/1000000000 : ℝ) ^ p + (18775931/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (992499847/1000000000 : ℝ)) (y := (18775931/20000000 : ℝ)) (X := (81682835090571/100000000000000 : ℝ)) (Y := (2289647734059/12500000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1931296397/1000000000 : ℝ)) (τ := (18775931/20000000 : ℝ)) (σ := (992499847/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (409855988/433894591 : ℝ) ^ p + (859960731/867789182 : ℝ) ^ p := by
    exact cert_lt (x := (409855988/433894591 : ℝ)) (y := (859960731/867789182 : ℝ)) (X := (21615457106323/100000000000000 : ℝ)) (Y := (1959613603957/2500000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (18775931/20000000 : ℝ)) (n' := (433894591/500000000 : ℝ)) (Ab := (102463997/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469451429/500000000 : ℝ) ^ p + (992474599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469451429/500000000 : ℝ)) (y := (992474599/1000000000 : ℝ)) (X := (18373008060833/100000000000000 : ℝ)) (Y := (81627009556947/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992474599/1000000000 : ℝ) ^ p + (469451429/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992474599/1000000000 : ℝ)) (y := (469451429/500000000 : ℝ)) (X := (81627009556947/100000000000000 : ℝ)) (Y := (18373008060833/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1931377457/1000000000 : ℝ)) (τ := (469451429/500000000 : ℝ)) (σ := (992474599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (819823751/867911553 : ℝ) ^ p + (860083102/867911553 : ℝ) ^ p := by
    exact cert_lt (x := (819823751/867911553 : ℝ)) (y := (860083102/867911553 : ℝ)) (X := (10806376514429/50000000000000 : ℝ)) (Y := (39193624015919/50000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469451429/500000000 : ℝ)) (n' := (867911553/1000000000 : ℝ)) (Ab := (819823751/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (938906111/1000000000 : ℝ) ^ p + (39698953/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (938906111/1000000000 : ℝ)) (y := (39698953/40000000 : ℝ)) (X := (4593679727387/25000000000000 : ℝ)) (Y := (81625298755781/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (39698953/40000000 : ℝ) ^ p + (938906111/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39698953/40000000 : ℝ)) (y := (938906111/1000000000 : ℝ)) (X := (81625298755781/100000000000000 : ℝ)) (Y := (4593679727387/25000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (60355623/31250000 : ℝ)) (τ := (938906111/1000000000 : ℝ)) (σ := (39698953/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (409913586/433957649 : ℝ) ^ p + (860086847/867915298 : ℝ) ^ p := by
    exact cert_lt (x := (409913586/433957649 : ℝ)) (y := (860086847/867915298 : ℝ)) (X := (21612670487147/100000000000000 : ℝ)) (Y := (39193665384823/50000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (938906111/1000000000 : ℝ)) (n' := (433957649/500000000 : ℝ)) (Ab := (204956793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (938906211/1000000000 : ℝ) ^ p + (992473801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (938906211/1000000000 : ℝ)) (y := (992473801/1000000000 : ℝ)) (X := (18374771504929/100000000000000 : ℝ)) (Y := (16325049141647/20000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992473801/1000000000 : ℝ) ^ p + (938906211/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992473801/1000000000 : ℝ)) (y := (938906211/1000000000 : ℝ)) (X := (16325049141647/20000000000000 : ℝ)) (Y := (18374771504929/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (482845003/250000000 : ℝ)) (τ := (938906211/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (819827277/867915413 : ℝ) ^ p + (860086962/867915413 : ℝ) ^ p := by
    exact cert_lt (x := (819827277/867915413 : ℝ)) (y := (860086962/867915413 : ℝ)) (X := (21612667916559/100000000000000 : ℝ)) (Y := (78387333310317/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (938906211/1000000000 : ℝ)) (n' := (867915413/1000000000 : ℝ)) (Ab := (819827277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (938906213/1000000000 : ℝ) ^ p + (992473801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (938906213/1000000000 : ℝ)) (y := (992473801/1000000000 : ℝ)) (X := (18374772556839/100000000000000 : ℝ)) (Y := (16325049141647/20000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992473801/1000000000 : ℝ) ^ p + (938906213/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992473801/1000000000 : ℝ)) (y := (938906213/1000000000 : ℝ)) (X := (16325049141647/20000000000000 : ℝ)) (Y := (18374772556839/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (965690007/500000000 : ℝ)) (τ := (938906213/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (819827279/867915415 : ℝ) ^ p + (860086964/867915415 : ℝ) ^ p := by
    exact cert_lt (x := (819827279/867915415 : ℝ)) (y := (860086964/867915415 : ℝ)) (X := (21612667995069/100000000000000 : ℝ)) (Y := (39193666677251/50000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (938906213/1000000000 : ℝ)) (n' := (173583083/200000000 : ℝ)) (Ab := (819827279/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (965690007/500000000 : ℝ)) (τ := (938906213/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (938906213/1000000000 : ℝ)) (n' := (173583083/200000000 : ℝ)) (Ab := (819827279/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (965690007/500000000 : ℝ)) (τ := (938906213/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (938906213/1000000000 : ℝ)) (n' := (173583083/200000000 : ℝ)) (Ab := (819827279/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (965690007/500000000 : ℝ)) (τ := (938906213/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (938906213/1000000000 : ℝ)) (n' := (173583083/200000000 : ℝ)) (Ab := (819827279/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (965690007/500000000 : ℝ)) (τ := (938906213/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (938906213/1000000000 : ℝ)) (n' := (173583083/200000000 : ℝ)) (Ab := (819827279/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (965690007/500000000 : ℝ)) (τ := (938906213/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1697573152/1844118033 : ℝ) ^ p + (1836289582/1844118033 : ℝ) ^ p := by
    exact cert_lt (x := (1697573152/1844118033 : ℝ)) (y := (1836289582/1844118033 : ℝ)) (X := (10803616942771/100000000000000 : ℝ)) (Y := (89196383241579/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1081395062/1155881967 : ℝ) ^ p + (1148053516/1155881967 : ℝ) ^ p := by
    exact cert_lt (x := (1081395062/1155881967 : ℝ)) (y := (1148053516/1155881967 : ℝ)) (X := (4173210383277/25000000000000 : ℝ)) (Y := (83307159172227/100000000000000 : ℝ)) 215 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992473801/1000000000 : ℝ)) (U := (1155881967/1000000000 : ℝ)) (Ab := (53049161/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (938906213/1000000000 : ℝ)) (σ := (992473801/1000000000 : ℝ)) (Ab := (540697531/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab013
