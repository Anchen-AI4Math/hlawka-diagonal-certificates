import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 86, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab086 (p : ℝ) (hpa : (379/16 : ℝ) ≤ p) (hpb : p ≤ (759/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524304080123/25866750000000 : ℝ) (10435657/1000000000 : ℝ) (2000000310401/10346700000000 : ℝ) (3033/2500 : ℝ) (242799821/125000000 : ℝ) (12139523/12500000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193465897/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11123/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(573/1250 : ℝ)
      else (3867/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524304080123/25866750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10435657/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (183889951/200000000 : ℝ) ^ p + (993834637/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183889951/200000000 : ℝ)) (y := (993834637/1000000000 : ℝ)) (X := (13643625293691/100000000000000 : ℝ)) (Y := (86356391970357/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993834637/1000000000 : ℝ) ^ p + (183889951/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993834637/1000000000 : ℝ)) (y := (183889951/200000000 : ℝ)) (X := (86356391970357/100000000000000 : ℝ)) (Y := (13643625293691/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (239160549/125000000 : ℝ)) (τ := (183889951/200000000 : ℝ)) (σ := (993834637/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783048530/828865903 : ℝ) ^ p + (818430246/828865903 : ℝ) ^ p := by
    exact cert_lt (x := (783048530/828865903 : ℝ)) (y := (818430246/828865903 : ℝ)) (X := (12978405528459/50000000000000 : ℝ)) (Y := (3702159492279/5000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (183889951/200000000 : ℝ)) (n' := (828865903/1000000000 : ℝ)) (Ab := (78304853/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185015609/200000000 : ℝ) ^ p + (99279123/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (185015609/200000000 : ℝ)) (y := (99279123/100000000 : ℝ)) (X := (15768606156211/100000000000000 : ℝ)) (Y := (42115705588821/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99279123/100000000 : ℝ) ^ p + (185015609/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (99279123/100000000 : ℝ)) (y := (185015609/200000000 : ℝ)) (X := (42115705588821/50000000000000 : ℝ)) (Y := (15768606156211/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (76714771/40000000 : ℝ)) (τ := (185015609/200000000 : ℝ)) (σ := (99279123/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394554455/417762072 : ℝ) ^ p + (825088487/835524144 : ℝ) ^ p := by
    exact cert_lt (x := (394554455/417762072 : ℝ)) (y := (825088487/835524144 : ℝ)) (X := (3222269406941/12500000000000 : ℝ)) (Y := (74221845557471/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185015609/200000000 : ℝ)) (n' := (52220259/62500000 : ℝ)) (Ab := (78910891/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185064427/200000000 : ℝ) ^ p + (198548403/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (185064427/200000000 : ℝ)) (y := (198548403/200000000 : ℝ)) (X := (7933794388803/50000000000000 : ℝ)) (Y := (2103310702833/2500000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198548403/200000000 : ℝ) ^ p + (185064427/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198548403/200000000 : ℝ)) (y := (185064427/200000000 : ℝ)) (X := (2103310702833/2500000000000 : ℝ)) (Y := (7933794388803/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (38361283/20000000 : ℝ)) (τ := (185064427/200000000 : ℝ)) (σ := (198548403/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (789370876/835812003 : ℝ) ^ p + (825376346/835812003 : ℝ) ^ p := by
    exact cert_lt (x := (789370876/835812003 : ℝ)) (y := (825376346/835812003 : ℝ)) (X := (6442621695713/25000000000000 : ℝ)) (Y := (74229514500547/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185064427/200000000 : ℝ)) (n' := (835812003/1000000000 : ℝ)) (Ab := (197342719/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (92533261/100000000 : ℝ) ^ p + (198547979/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (92533261/100000000 : ℝ)) (y := (198547979/200000000 : ℝ)) (X := (15871849857359/100000000000000 : ℝ)) (Y := (84128166793363/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198547979/200000000 : ℝ) ^ p + (92533261/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198547979/200000000 : ℝ)) (y := (92533261/100000000 : ℝ)) (X := (84128166793363/100000000000000 : ℝ)) (Y := (15871849857359/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (383614501/200000000 : ℝ)) (τ := (92533261/100000000 : ℝ)) (σ := (198547979/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (131563686/139304059 : ℝ) ^ p + (825388697/835824354 : ℝ) ^ p := by
    exact cert_lt (x := (131563686/139304059 : ℝ)) (y := (825388697/835824354 : ℝ)) (X := (6442539476149/25000000000000 : ℝ)) (Y := (74229843446249/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (92533261/100000000 : ℝ)) (n' := (417912177/500000000 : ℝ)) (Ab := (197345529/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (46266653/50000000 : ℝ) ^ p + (248184951/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (46266653/50000000 : ℝ)) (y := (248184951/250000000 : ℝ)) (X := (496001029233/3125000000000 : ℝ)) (Y := (42063991941421/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248184951/250000000 : ℝ) ^ p + (46266653/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (248184951/250000000 : ℝ)) (y := (46266653/50000000 : ℝ)) (X := (42063991941421/50000000000000 : ℝ)) (Y := (496001029233/3125000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (59939777/31250000 : ℝ)) (τ := (46266653/50000000 : ℝ)) (σ := (248184951/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (263127533/278608295 : ℝ) ^ p + (825389228/835824885 : ℝ) ^ p := by
    exact cert_lt (x := (263127533/278608295 : ℝ)) (y := (825389228/835824885 : ℝ)) (X := (25770143583367/100000000000000 : ℝ)) (Y := (74229857588251/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (46266653/50000000 : ℝ)) (n' := (167164977/200000000 : ℝ)) (Ab := (789382599/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925333079/1000000000 : ℝ) ^ p + (4963699/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (925333079/1000000000 : ℝ)) (y := (4963699/5000000 : ℝ)) (X := (3174408133093/20000000000000 : ℝ)) (Y := (84127975842827/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (4963699/5000000 : ℝ) ^ p + (925333079/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (4963699/5000000 : ℝ)) (y := (925333079/1000000000 : ℝ)) (X := (84127975842827/100000000000000 : ℝ)) (Y := (3174408133093/20000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918072879/1000000000 : ℝ)) (τ := (925333079/1000000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789382619/835824907 : ℝ) ^ p + (825389250/835824907 : ℝ) ^ p := by
    exact cert_lt (x := (789382619/835824907 : ℝ)) (y := (825389250/835824907 : ℝ)) (X := (3221267872659/12500000000000 : ℝ)) (Y := (18557464543543/25000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925333079/1000000000 : ℝ)) (n' := (835824907/1000000000 : ℝ)) (Ab := (789382619/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (23133327/25000000 : ℝ) ^ p + (4963699/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (23133327/25000000 : ℝ)) (y := (4963699/5000000 : ℝ)) (X := (15872041072307/100000000000000 : ℝ)) (Y := (84127975842827/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (4963699/5000000 : ℝ) ^ p + (23133327/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (4963699/5000000 : ℝ)) (y := (23133327/25000000 : ℝ)) (X := (84127975842827/100000000000000 : ℝ)) (Y := (15872041072307/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (197345655/208956227 : ℝ) ^ p + (825389251/835824908 : ℝ) ^ p := by
    exact cert_lt (x := (197345655/208956227 : ℝ)) (y := (825389251/835824908 : ℝ)) (X := (3221267878037/12500000000000 : ℝ)) (Y := (18557464550201/25000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (n' := (208956227/250000000 : ℝ)) (Ab := (39469131/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (23975911/12500000 : ℝ)) (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1656765190/1806534103 : ℝ) ^ p + (1796098446/1806534103 : ℝ) ^ p := by
    exact cert_lt (x := (1656765190/1806534103 : ℝ)) (y := (1796098446/1806534103 : ℝ)) (X := (1283884509157/10000000000000 : ℝ)) (Y := (43580577584753/50000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112275111/1193465897 : ℝ) ^ p + (1183030240/1193465897 : ℝ) ^ p := by
    exact cert_lt (x := (1112275111/1193465897 : ℝ)) (y := (1183030240/1193465897 : ℝ)) (X := (18804360320143/100000000000000 : ℝ)) (Y := (81195640175637/100000000000000 : ℝ)) 759 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (4963699/5000000 : ℝ)) (U := (1193465897/1000000000 : ℝ)) (Ab := (165676519/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (23133327/25000000 : ℝ)) (σ := (4963699/5000000 : ℝ)) (Ab := (1112275111/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab086
