import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 102, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab102 (p : ℝ) (hpa : (387/16 : ℝ) ≤ p) (hpb : p ≤ (775/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (522956784173/26412750000000 : ℝ) (5093753/500000000 : ℝ) (2000000316953/10565100000000 : ℝ) (3033/2500 : ℝ) (97178541/50000000 : ℝ) (242937369/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (14920869/12500000 : ℝ)) ∧
    (∀ j i, if j = i then -(557/500 : ℝ) ≤ X j i ∧ X j i ≤ -(1153/2500 : ℝ)
      else (3881/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2963/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (522956784173/26412750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5093753/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (11514969/12500000 : ℝ) ^ p + (993935519/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (11514969/12500000 : ℝ)) (y := (993935519/1000000000 : ℝ)) (X := (6849177372211/50000000000000 : ℝ)) (Y := (86301663200929/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993935519/1000000000 : ℝ) ^ p + (11514969/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (993935519/1000000000 : ℝ)) (y := (11514969/12500000 : ℝ)) (X := (86301663200929/100000000000000 : ℝ)) (Y := (6849177372211/50000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1915133039/1000000000 : ℝ)) (τ := (11514969/12500000 : ℝ)) (σ := (993935519/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (785351711/830484938 : ℝ) ^ p + (410148716/415242469 : ℝ) ^ p := by
    exact cert_lt (x := (785351711/830484938 : ℝ)) (y := (410148716/415242469 : ℝ)) (X := (1291932692961/5000000000000 : ℝ)) (Y := (3708067355669/5000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (11514969/12500000 : ℝ)) (n' := (415242469/500000000 : ℝ)) (Ab := (785351711/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185351389/200000000 : ℝ) ^ p + (992901229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185351389/200000000 : ℝ)) (y := (992901229/1000000000 : ℝ)) (X := (15847259216413/100000000000000 : ℝ)) (Y := (84152758445581/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992901229/1000000000 : ℝ) ^ p + (185351389/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992901229/1000000000 : ℝ)) (y := (185351389/200000000 : ℝ)) (X := (84152758445581/100000000000000 : ℝ)) (Y := (15847259216413/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (959829087/500000000 : ℝ)) (τ := (185351389/200000000 : ℝ)) (σ := (992901229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (791333272/837045121 : ℝ) ^ p + (826857615/837045121 : ℝ) ^ p := by
    exact cert_lt (x := (791333272/837045121 : ℝ)) (y := (826857615/837045121 : ℝ)) (X := (12831817667401/50000000000000 : ℝ)) (Y := (74336365536801/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185351389/200000000 : ℝ)) (n' := (837045121/1000000000 : ℝ)) (Ab := (98916659/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37079649/40000000 : ℝ) ^ p + (248213449/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (37079649/40000000 : ℝ)) (y := (248213449/250000000 : ℝ)) (X := (1993070952131/12500000000000 : ℝ)) (Y := (84055449272417/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248213449/250000000 : ℝ) ^ p + (37079649/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (248213449/250000000 : ℝ)) (y := (37079649/40000000 : ℝ)) (X := (84055449272417/100000000000000 : ℝ)) (Y := (1993070952131/12500000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1919845021/1000000000 : ℝ)) (τ := (37079649/40000000 : ℝ)) (σ := (248213449/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (395792263/418660363 : ℝ) ^ p + (413566610/418660363 : ℝ) ^ p := by
    exact cert_lt (x := (395792263/418660363 : ℝ)) (y := (413566610/418660363 : ℝ)) (X := (801760444711/3125000000000 : ℝ)) (Y := (74343666932621/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37079649/40000000 : ℝ)) (n' := (418660363/500000000 : ℝ)) (Ab := (395792263/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (231750249/250000000 : ℝ) ^ p + (992851811/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231750249/250000000 : ℝ)) (y := (992851811/1000000000 : ℝ)) (X := (7974319214337/50000000000000 : ℝ)) (Y := (21012844845471/25000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992851811/1000000000 : ℝ) ^ p + (231750249/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992851811/1000000000 : ℝ)) (y := (231750249/250000000 : ℝ)) (X := (21012844845471/25000000000000 : ℝ)) (Y := (7974319214337/50000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1919852807/1000000000 : ℝ)) (τ := (231750249/250000000 : ℝ)) (σ := (992851811/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (791595003/837332219 : ℝ) ^ p + (827144713/837332219 : ℝ) ^ p := by
    exact cert_lt (x := (791595003/837332219 : ℝ)) (y := (827144713/837332219 : ℝ)) (X := (1603501843239/6250000000000 : ℝ)) (Y := (74343971318551/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (231750249/250000000 : ℝ)) (n' := (837332219/1000000000 : ℝ)) (Ab := (791595003/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231750351/250000000 : ℝ) ^ p + (62053233/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (231750351/250000000 : ℝ)) (y := (62053233/62500000 : ℝ)) (X := (15948808432039/100000000000000 : ℝ)) (Y := (656650071947/781250000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62053233/62500000 : ℝ) ^ p + (231750351/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (62053233/62500000 : ℝ)) (y := (231750351/250000000 : ℝ)) (X := (656650071947/781250000000 : ℝ)) (Y := (15948808432039/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479963283/250000000 : ℝ)) (τ := (231750351/250000000 : ℝ)) (σ := (62053233/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (113085063/119618957 : ℝ) ^ p + (118163599/119618957 : ℝ) ^ p := by
    exact cert_lt (x := (113085063/119618957 : ℝ)) (y := (118163599/119618957 : ℝ)) (X := (6414004276127/25000000000000 : ℝ)) (Y := (74343984030937/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231750351/250000000 : ℝ)) (n' := (837332699/1000000000 : ℝ)) (Ab := (791595441/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (927001421/1000000000 : ℝ) ^ p + (248212931/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (927001421/1000000000 : ℝ)) (y := (248212931/250000000 : ℝ)) (X := (318976310311/2000000000000 : ℝ)) (Y := (21012800252033/25000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248212931/250000000 : ℝ) ^ p + (927001421/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248212931/250000000 : ℝ)) (y := (927001421/1000000000 : ℝ)) (X := (21012800252033/25000000000000 : ℝ)) (Y := (318976310311/2000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383970629/200000000 : ℝ)) (τ := (927001421/1000000000 : ℝ)) (σ := (248212931/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (791595459/837332719 : ℝ) ^ p + (827145213/837332719 : ℝ) ^ p := by
    exact cert_lt (x := (791595459/837332719 : ℝ)) (y := (827145213/837332719 : ℝ)) (X := (5131203278427/20000000000000 : ℝ)) (Y := (74343984560619/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (927001421/1000000000 : ℝ)) (n' := (837332719/1000000000 : ℝ)) (Ab := (791595459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (463500711/500000000 : ℝ) ^ p + (248212931/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (463500711/500000000 : ℝ)) (y := (248212931/250000000 : ℝ)) (X := (15948815932227/100000000000000 : ℝ)) (Y := (21012800252033/25000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248212931/250000000 : ℝ) ^ p + (463500711/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248212931/250000000 : ℝ)) (y := (463500711/500000000 : ℝ)) (X := (21012800252033/25000000000000 : ℝ)) (Y := (15948815932227/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (959926573/500000000 : ℝ)) (τ := (463500711/500000000 : ℝ)) (σ := (248212931/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (39579773/41866636 : ℝ) ^ p + (59081801/59809480 : ℝ) ^ p := by
    exact cert_lt (x := (39579773/41866636 : ℝ)) (y := (59081801/59809480 : ℝ)) (X := (2565601643501/10000000000000 : ℝ)) (Y := (2323249518347/3125000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (463500711/500000000 : ℝ)) (n' := (10466659/12500000 : ℝ)) (Ab := (39579773/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (959926573/500000000 : ℝ)) (τ := (463500711/500000000 : ℝ)) (σ := (248212931/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (463500711/500000000 : ℝ)) (n' := (10466659/12500000 : ℝ)) (Ab := (39579773/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (959926573/500000000 : ℝ)) (τ := (463500711/500000000 : ℝ)) (σ := (248212931/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (463500711/500000000 : ℝ)) (n' := (10466659/12500000 : ℝ)) (Ab := (39579773/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (959926573/500000000 : ℝ)) (τ := (463500711/500000000 : ℝ)) (σ := (248212931/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (463500711/500000000 : ℝ)) (n' := (10466659/12500000 : ℝ)) (Ab := (39579773/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (959926573/500000000 : ℝ)) (τ := (463500711/500000000 : ℝ)) (σ := (248212931/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (829669409/903165240 : ℝ) ^ p + (898071487/903165240 : ℝ) ^ p := by
    exact cert_lt (x := (829669409/903165240 : ℝ)) (y := (898071487/903165240 : ℝ)) (X := (6400517928189/50000000000000 : ℝ)) (Y := (87198964483933/100000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1113940121/1193669520 : ℝ) ^ p + (591741007/596834760 : ℝ) ^ p := by
    exact cert_lt (x := (1113940121/1193669520 : ℝ)) (y := (591741007/596834760 : ℝ)) (X := (18745560733503/100000000000000 : ℝ)) (Y := (40627219879619/50000000000000 : ℝ)) 775 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248212931/250000000 : ℝ)) (U := (14920869/12500000 : ℝ)) (Ab := (829669409/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (463500711/500000000 : ℝ)) (σ := (248212931/250000000 : ℝ)) (Ab := (1113940121/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab102
