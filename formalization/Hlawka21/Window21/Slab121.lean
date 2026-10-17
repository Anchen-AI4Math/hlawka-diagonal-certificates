import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 121, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab121 (p : ℝ) (hpa : (793/32 : ℝ) ≤ p) (hpb : p ≤ (397/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (521426893811/27061125000000 : ℝ) (9907523/1000000000 : ℝ) (4000000649467/21648900000000 : ℝ) (3033/2500 : ℝ) (972451183/500000000 : ℝ) (486208463/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (119391103/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11159/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1161/2500 : ℝ)
      else (7793/10000 : ℝ) ≤ X j i ∧ X j i ≤ (741/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (521426893811/27061125000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9907523/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (461588627/500000000 : ℝ) ^ p + (994051317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461588627/500000000 : ℝ)) (y := (994051317/1000000000 : ℝ)) (X := (13760570210969/100000000000000 : ℝ)) (Y := (86239449374909/100000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994051317/1000000000 : ℝ) ^ p + (461588627/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (994051317/1000000000 : ℝ)) (y := (461588627/500000000 : ℝ)) (X := (86239449374909/100000000000000 : ℝ)) (Y := (13760570210969/100000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1917228571/1000000000 : ℝ)) (τ := (461588627/500000000 : ℝ)) (σ := (994051317/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (393982096/416153769 : ℝ) ^ p + (822400015/832307538 : ℝ) ^ p := by
    exact cert_lt (x := (393982096/416153769 : ℝ)) (y := (822400015/832307538 : ℝ)) (X := (12852707022117/50000000000000 : ℝ)) (Y := (74294587430599/100000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (461588627/500000000 : ℝ)) (n' := (416153769/500000000 : ℝ)) (Ab := (24623881/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (928655037/1000000000 : ℝ) ^ p + (198605627/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (928655037/1000000000 : ℝ)) (y := (198605627/200000000 : ℝ)) (X := (7968154892977/50000000000000 : ℝ)) (Y := (10507963487239/12500000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198605627/200000000 : ℝ) ^ p + (928655037/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198605627/200000000 : ℝ)) (y := (928655037/1000000000 : ℝ)) (X := (10507963487239/12500000000000 : ℝ)) (Y := (7968154892977/50000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (480420793/250000000 : ℝ)) (τ := (928655037/1000000000 : ℝ)) (σ := (198605627/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (113407543/119821846 : ℝ) ^ p + (828845399/838752922 : ℝ) ^ p := by
    exact cert_lt (x := (113407543/119821846 : ℝ)) (y := (828845399/838752922 : ℝ)) (X := (6383642078891/25000000000000 : ℝ)) (Y := (7446543279309/10000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (928655037/1000000000 : ℝ)) (n' := (419376461/500000000 : ℝ)) (Ab := (793852801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185775673/200000000 : ℝ) ^ p + (248245677/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (185775673/200000000 : ℝ)) (y := (248245677/250000000 : ℝ)) (X := (2003959404033/12500000000000 : ℝ)) (Y := (10496042696709/12500000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248245677/250000000 : ℝ) ^ p + (185775673/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248245677/250000000 : ℝ)) (y := (185775673/200000000 : ℝ)) (X := (10496042696709/12500000000000 : ℝ)) (Y := (2003959404033/12500000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1921861073/1000000000 : ℝ)) (τ := (185775673/200000000 : ℝ)) (σ := (248245677/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (794092116/839014907 : ℝ) ^ p + (829107384/839014907 : ℝ) ^ p := by
    exact cert_lt (x := (794092116/839014907 : ℝ)) (y := (829107384/839014907 : ℝ)) (X := (6381917856827/25000000000000 : ℝ)) (Y := (9309041189643/12500000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185775673/200000000 : ℝ)) (n' := (839014907/1000000000 : ℝ)) (Ab := (198523029/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (928887377/1000000000 : ℝ) ^ p + (992980869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (928887377/1000000000 : ℝ)) (y := (992980869/1000000000 : ℝ)) (X := (8017767503389/50000000000000 : ℝ)) (Y := (41982241545443/50000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992980869/1000000000 : ℝ) ^ p + (928887377/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992980869/1000000000 : ℝ)) (y := (928887377/1000000000 : ℝ)) (X := (41982241545443/50000000000000 : ℝ)) (Y := (8017767503389/50000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (960934123/500000000 : ℝ)) (τ := (928887377/1000000000 : ℝ)) (σ := (992980869/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (794101773/839025478 : ℝ) ^ p + (829117955/839025478 : ℝ) ^ p := by
    exact cert_lt (x := (794101773/839025478 : ℝ)) (y := (829117955/839025478 : ℝ)) (X := (5105478769519/20000000000000 : ℝ)) (Y := (9309075964991/12500000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (928887377/1000000000 : ℝ)) (n' := (419512739/500000000 : ℝ)) (Ab := (794101773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (46444387/50000000 : ℝ) ^ p + (198596159/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (46444387/50000000 : ℝ)) (y := (198596159/200000000 : ℝ)) (X := (16035690495739/100000000000000 : ℝ)) (Y := (83964327831953/100000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198596159/200000000 : ℝ) ^ p + (46444387/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (198596159/200000000 : ℝ)) (y := (46444387/50000000 : ℝ)) (X := (83964327831953/100000000000000 : ℝ)) (Y := (16035690495739/100000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (384373707/200000000 : ℝ)) (τ := (46444387/50000000 : ℝ)) (σ := (198596159/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (794102161/839025903 : ℝ) ^ p + (829118380/839025903 : ℝ) ^ p := by
    exact cert_lt (x := (794102161/839025903 : ℝ)) (y := (829118380/839025903 : ℝ)) (X := (25527382485903/100000000000000 : ℝ)) (Y := (1861815472619/2500000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (46444387/50000000 : ℝ)) (n' := (839025903/1000000000 : ℝ)) (Ab := (794102161/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232221939/250000000 : ℝ) ^ p + (992980791/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232221939/250000000 : ℝ)) (y := (992980791/1000000000 : ℝ)) (X := (16035697349281/100000000000000 : ℝ)) (Y := (41982159719793/50000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992980791/1000000000 : ℝ) ^ p + (232221939/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992980791/1000000000 : ℝ)) (y := (232221939/250000000 : ℝ)) (X := (41982159719793/50000000000000 : ℝ)) (Y := (16035697349281/100000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921868547/1000000000 : ℝ)) (τ := (232221939/250000000 : ℝ)) (σ := (992980791/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (397051089/419512961 : ℝ) ^ p + (829118399/839025922 : ℝ) ^ p := by
    exact cert_lt (x := (397051089/419512961 : ℝ)) (y := (829118399/839025922 : ℝ)) (X := (6381845425521/25000000000000 : ℝ)) (Y := (74472619404787/100000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232221939/250000000 : ℝ)) (n' := (419512961/500000000 : ℝ)) (Ab := (397051089/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1921868547/1000000000 : ℝ)) (τ := (232221939/250000000 : ℝ)) (σ := (992980791/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (232221939/250000000 : ℝ)) (n' := (419512961/500000000 : ℝ)) (Ab := (397051089/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1921868547/1000000000 : ℝ)) (τ := (232221939/250000000 : ℝ)) (σ := (992980791/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (232221939/250000000 : ℝ)) (n' := (419512961/500000000 : ℝ)) (Ab := (397051089/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1921868547/1000000000 : ℝ)) (τ := (232221939/250000000 : ℝ)) (σ := (992980791/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (232221939/250000000 : ℝ)) (n' := (419512961/500000000 : ℝ)) (Ab := (397051089/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1921868547/1000000000 : ℝ)) (τ := (232221939/250000000 : ℝ)) (σ := (992980791/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (232221939/250000000 : ℝ)) (n' := (419512961/500000000 : ℝ)) (Ab := (397051089/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1921868547/1000000000 : ℝ)) (τ := (232221939/250000000 : ℝ)) (σ := (992980791/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (831132842/903044485 : ℝ) ^ p + (1796181447/1806088970 : ℝ) ^ p := by
    exact cert_lt (x := (831132842/903044485 : ℝ)) (y := (1796181447/1806088970 : ℝ)) (X := (12758209563623/100000000000000 : ℝ)) (Y := (17448358142909/20000000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1115849463/1193911030 : ℝ) ^ p + (1184003507/1193911030 : ℝ) ^ p := by
    exact cert_lt (x := (1115849463/1193911030 : ℝ)) (y := (1184003507/1193911030 : ℝ)) (X := (9339364024533/50000000000000 : ℝ)) (Y := (10165159052961/12500000000000 : ℝ)) 397 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992980791/1000000000 : ℝ)) (U := (119391103/100000000 : ℝ)) (Ab := (415566421/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (232221939/250000000 : ℝ)) (σ := (992980791/1000000000 : ℝ)) (Ab := (1115849463/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab121
