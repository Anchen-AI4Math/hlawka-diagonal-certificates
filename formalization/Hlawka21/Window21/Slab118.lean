import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 118, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab118 (p : ℝ) (hpa : (395/16 : ℝ) ≤ p) (hpb : p ≤ (791/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (208665403949/10783500000000 : ℝ) (9950717/1000000000 : ℝ) (400000064701/2156700000000 : ℝ) (3033/2500 : ℝ) (486174079/250000000 : ℝ) (972313643/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (74617059/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(2789/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(4639/10000 : ℝ)
      else (1947/2500 : ℝ) ≤ X j i ∧ X j i ≤ (2371/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (208665403949/10783500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9950717/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (922871289/1000000000 : ℝ) ^ p + (31063541/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (922871289/1000000000 : ℝ)) (y := (31063541/31250000 : ℝ)) (X := (13750941439843/100000000000000 : ℝ)) (Y := (107811345583/125000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31063541/31250000 : ℝ) ^ p + (922871289/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31063541/31250000 : ℝ)) (y := (922871289/1000000000 : ℝ)) (X := (107811345583/125000000000 : ℝ)) (Y := (13750941439843/100000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1916904601/1000000000 : ℝ)) (τ := (922871289/1000000000 : ℝ)) (σ := (31063541/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (787560179/832026647 : ℝ) ^ p + (822075930/832026647 : ℝ) ^ p := by
    exact cert_lt (x := (787560179/832026647 : ℝ)) (y := (822075930/832026647 : ℝ)) (X := (25725962424319/100000000000000 : ℝ)) (Y := (18568509706161/25000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (922871289/1000000000 : ℝ)) (n' := (832026647/1000000000 : ℝ)) (Ab := (787560179/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (928361937/1000000000 : ℝ) ^ p + (24825209/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (928361937/1000000000 : ℝ)) (y := (24825209/25000000 : ℝ)) (X := (15922551126703/100000000000000 : ℝ)) (Y := (84077466166197/100000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (24825209/25000000 : ℝ) ^ p + (928361937/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24825209/25000000 : ℝ)) (y := (928361937/1000000000 : ℝ)) (X := (84077466166197/100000000000000 : ℝ)) (Y := (15922551126703/100000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1921370297/1000000000 : ℝ)) (τ := (928361937/1000000000 : ℝ)) (σ := (24825209/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (793463404/838490025 : ℝ) ^ p + (828539308/838490025 : ℝ) ^ p := by
    exact cert_lt (x := (793463404/838490025 : ℝ)) (y := (828539308/838490025 : ℝ)) (X := (25554468922513/100000000000000 : ℝ)) (Y := (37222766283927/50000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (928361937/1000000000 : ℝ)) (n' := (33539601/40000000 : ℝ)) (Ab := (198365851/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185717389/200000000 : ℝ) ^ p + (7943701/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (185717389/200000000 : ℝ)) (y := (7943701/8000000 : ℝ)) (X := (1601821954859/10000000000000 : ℝ)) (Y := (10497724825653/12500000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (7943701/8000000 : ℝ) ^ p + (185717389/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (7943701/8000000 : ℝ)) (y := (185717389/200000000 : ℝ)) (X := (10497724825653/12500000000000 : ℝ)) (Y := (1601821954859/10000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192154957/100000000 : ℝ)) (τ := (185717389/200000000 : ℝ)) (σ := (7943701/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (793704549/838754095 : ℝ) ^ p + (828803378/838754095 : ℝ) ^ p := by
    exact cert_lt (x := (793704549/838754095 : ℝ)) (y := (828803378/838754095 : ℝ)) (X := (1021900420761/4000000000000 : ℝ)) (Y := (37226245491141/50000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185717389/200000000 : ℝ)) (n' := (167750819/200000000 : ℝ)) (Ab := (793704549/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (928596073/1000000000 : ℝ) ^ p + (992960763/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (928596073/1000000000 : ℝ)) (y := (992960763/1000000000 : ℝ)) (X := (640884487613/4000000000000 : ℝ)) (Y := (41988952962211/50000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992960763/1000000000 : ℝ) ^ p + (928596073/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992960763/1000000000 : ℝ)) (y := (928596073/1000000000 : ℝ)) (X := (41988952962211/50000000000000 : ℝ)) (Y := (640884487613/4000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (480389209/250000000 : ℝ)) (τ := (928596073/1000000000 : ℝ)) (σ := (992960763/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (396857165/419382403 : ℝ) ^ p + (828814089/838764806 : ℝ) ^ p := by
    exact cert_lt (x := (396857165/419382403 : ℝ)) (y := (828814089/838764806 : ℝ)) (X := (5109445660363/20000000000000 : ℝ)) (Y := (74452773144727/100000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (928596073/1000000000 : ℝ)) (n' := (419382403/500000000 : ℝ)) (Ab := (79371433/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (232149111/250000000 : ℝ) ^ p + (992960687/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232149111/250000000 : ℝ)) (y := (992960687/1000000000 : ℝ)) (X := (16022270422719/100000000000000 : ℝ)) (Y := (83977747043169/100000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992960687/1000000000 : ℝ) ^ p + (232149111/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992960687/1000000000 : ℝ)) (y := (232149111/250000000 : ℝ)) (X := (83977747043169/100000000000000 : ℝ)) (Y := (16022270422719/100000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1921557131/1000000000 : ℝ)) (τ := (232149111/250000000 : ℝ)) (σ := (992960687/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (5751556/6078009 : ℝ) ^ p + (118402075/119823606 : ℝ) ^ p := by
    exact cert_lt (x := (5751556/6078009 : ℝ)) (y := (118402075/119823606 : ℝ)) (X := (5109443339981/20000000000000 : ℝ)) (Y := (74452784630249/100000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (232149111/250000000 : ℝ)) (n' := (419382621/500000000 : ℝ)) (Ab := (99214341/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (928596459/1000000000 : ℝ) ^ p + (248240171/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (928596459/1000000000 : ℝ)) (y := (248240171/250000000 : ℝ)) (X := (8011138410143/50000000000000 : ℝ)) (Y := (41988870385773/50000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248240171/250000000 : ℝ) ^ p + (928596459/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248240171/250000000 : ℝ)) (y := (928596459/1000000000 : ℝ)) (X := (41988870385773/50000000000000 : ℝ)) (Y := (8011138410143/50000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921557143/1000000000 : ℝ)) (τ := (928596459/1000000000 : ℝ)) (σ := (248240171/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (793714743/838765259 : ℝ) ^ p + (828814542/838765259 : ℝ) ^ p := by
    exact cert_lt (x := (793714743/838765259 : ℝ)) (y := (828814542/838765259 : ℝ)) (X := (25547215835129/100000000000000 : ℝ)) (Y := (37226392539039/50000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (928596459/1000000000 : ℝ)) (n' := (838765259/1000000000 : ℝ)) (Ab := (793714743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1921557143/1000000000 : ℝ)) (τ := (928596459/1000000000 : ℝ)) (σ := (248240171/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (928596459/1000000000 : ℝ)) (n' := (838765259/1000000000 : ℝ)) (Ab := (793714743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1921557143/1000000000 : ℝ)) (τ := (928596459/1000000000 : ℝ)) (σ := (248240171/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (928596459/1000000000 : ℝ)) (n' := (838765259/1000000000 : ℝ)) (Ab := (793714743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1921557143/1000000000 : ℝ)) (τ := (928596459/1000000000 : ℝ)) (σ := (248240171/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (928596459/1000000000 : ℝ)) (n' := (838765259/1000000000 : ℝ)) (Ab := (793714743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1921557143/1000000000 : ℝ)) (τ := (928596459/1000000000 : ℝ)) (σ := (248240171/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (928596459/1000000000 : ℝ)) (n' := (838765259/1000000000 : ℝ)) (Ab := (793714743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1921557143/1000000000 : ℝ)) (τ := (928596459/1000000000 : ℝ)) (σ := (248240171/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (184645835/200680784 : ℝ) ^ p + (1796176339/1806127056 : ℝ) ^ p := by
    exact cert_lt (x := (184645835/200680784 : ℝ)) (y := (1796176339/1806127056 : ℝ)) (X := (797801690901/6250000000000 : ℝ)) (Y := (21808793306567/25000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (278888183/298468236 : ℝ) ^ p + (1183922227/1193872944 : ℝ) ^ p := by
    exact cert_lt (x := (278888183/298468236 : ℝ)) (y := (1183922227/1193872944 : ℝ)) (X := (2336133940003/12500000000000 : ℝ)) (Y := (16262185841053/20000000000000 : ℝ)) 791 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248240171/250000000 : ℝ)) (U := (74617059/62500000 : ℝ)) (Ab := (332362503/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (928596459/1000000000 : ℝ)) (σ := (248240171/250000000 : ℝ)) (Ab := (278888183/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab118
