import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 6, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab006 (p : ℝ) (hpa : (339/16 : ℝ) ≤ p) (hpb : p ≤ (679/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1063968658399/46273500000000 : ℝ) (237577/20000000 : ℝ) (2000000277641/9254700000000 : ℝ) (3033/2500 : ℝ) (193572213/100000000 : ℝ) (967814433/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (9539739/8000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11031/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4419/10000 : ℝ)
      else (1893/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11831/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1063968658399/46273500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (237577/20000000 : ℝ) := by norm_num
  have pc0 : 1 < (909408583/1000000000 : ℝ) ^ p + (496639479/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (909408583/1000000000 : ℝ)) (y := (496639479/500000000 : ℝ)) (X := (13332714083751/100000000000000 : ℝ)) (Y := (86667301454877/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496639479/500000000 : ℝ) ^ p + (909408583/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496639479/500000000 : ℝ)) (y := (909408583/1000000000 : ℝ)) (X := (86667301454877/100000000000000 : ℝ)) (Y := (13332714083751/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1902687541/1000000000 : ℝ)) (τ := (909408583/1000000000 : ℝ)) (σ := (496639479/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (769871068/819383625 : ℝ) ^ p + (32300191/32775345 : ℝ) ^ p := by
    exact cert_lt (x := (769871068/819383625 : ℝ)) (y := (32300191/32775345 : ℝ)) (X := (3330686032091/12500000000000 : ℝ)) (Y := (36677256492431/50000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (909408583/1000000000 : ℝ)) (n' := (6555069/8000000 : ℝ)) (Ab := (192467767/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (228842901/250000000 : ℝ) ^ p + (99219587/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (228842901/250000000 : ℝ)) (y := (99219587/100000000 : ℝ)) (X := (612640332833/4000000000000 : ℝ)) (Y := (42342003431621/50000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99219587/100000000 : ℝ) ^ p + (228842901/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (99219587/100000000 : ℝ)) (y := (228842901/250000000 : ℝ)) (X := (42342003431621/50000000000000 : ℝ)) (Y := (612640332833/4000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (953783737/500000000 : ℝ)) (τ := (228842901/250000000 : ℝ)) (σ := (99219587/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (45666022/48620065 : ℝ) ^ p + (162932451/165308221 : ℝ) ^ p := by
    exact cert_lt (x := (45666022/48620065 : ℝ)) (y := (162932451/165308221 : ℝ)) (X := (26446955550657/100000000000000 : ℝ)) (Y := (73553045206149/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (228842901/250000000 : ℝ)) (n' := (165308221/200000000 : ℝ)) (Ab := (388161187/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (228918537/250000000 : ℝ) ^ p + (39685453/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (228918537/250000000 : ℝ)) (y := (39685453/40000000 : ℝ)) (X := (15423780894477/100000000000000 : ℝ)) (Y := (84576234944427/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39685453/40000000 : ℝ) ^ p + (228918537/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (39685453/40000000 : ℝ)) (y := (228918537/250000000 : ℝ)) (X := (84576234944427/100000000000000 : ℝ)) (Y := (15423780894477/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1907810473/1000000000 : ℝ)) (τ := (228918537/250000000 : ℝ)) (σ := (39685453/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (388324264/413451519 : ℝ) ^ p + (407512094/413451519 : ℝ) ^ p := by
    exact cert_lt (x := (388324264/413451519 : ℝ)) (y := (407512094/413451519 : ℝ)) (X := (26436994358317/100000000000000 : ℝ)) (Y := (36781503285799/50000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (228918537/250000000 : ℝ)) (n' := (413451519/500000000 : ℝ)) (Ab := (48540533/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (228922331/250000000 : ℝ) ^ p + (39685333/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (228922331/250000000 : ℝ)) (y := (39685333/40000000 : ℝ)) (X := (7714602947441/50000000000000 : ℝ)) (Y := (2642837769759/3125000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (39685333/40000000 : ℝ) ^ p + (228922331/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (39685333/40000000 : ℝ)) (y := (228922331/250000000 : ℝ)) (X := (2642837769759/3125000000000 : ℝ)) (Y := (7714602947441/50000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1907822649/1000000000 : ℝ)) (τ := (228922331/250000000 : ℝ)) (σ := (39685333/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (388332443/413460595 : ℝ) ^ p + (81504234/82692119 : ℝ) ^ p := by
    exact cert_lt (x := (388332443/413460595 : ℝ)) (y := (81504234/82692119 : ℝ)) (X := (26436495403619/100000000000000 : ℝ)) (Y := (36781752983727/50000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (228922331/250000000 : ℝ)) (n' := (82692119/100000000 : ℝ)) (Ab := (388332443/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (183138017/200000000 : ℝ) ^ p + (39685327/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (183138017/200000000 : ℝ)) (y := (39685327/40000000 : ℝ)) (X := (15429477979209/100000000000000 : ℝ)) (Y := (8457053732539/10000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39685327/40000000 : ℝ) ^ p + (183138017/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (39685327/40000000 : ℝ)) (y := (183138017/200000000 : ℝ)) (X := (8457053732539/10000000000000 : ℝ)) (Y := (15429477979209/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (95391163/50000000 : ℝ)) (τ := (183138017/200000000 : ℝ)) (σ := (39685327/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (388332853/413461050 : ℝ) ^ p + (16300865/16538442 : ℝ) ^ p := by
    exact cert_lt (x := (388332853/413461050 : ℝ)) (y := (16300865/16538442 : ℝ)) (X := (26436470345367/100000000000000 : ℝ)) (Y := (73563531002783/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (183138017/200000000 : ℝ)) (n' := (8269221/10000000 : ℝ)) (Ab := (388332853/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (457845061/500000000 : ℝ) ^ p + (62008323/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (457845061/500000000 : ℝ)) (y := (62008323/62500000 : ℝ)) (X := (1542949120813/10000000000000 : ℝ)) (Y := (84570524664421/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (62008323/62500000 : ℝ) ^ p + (457845061/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62008323/62500000 : ℝ)) (y := (457845061/500000000 : ℝ)) (X := (84570524664421/100000000000000 : ℝ)) (Y := (1542949120813/10000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (190782329/100000000 : ℝ)) (τ := (457845061/500000000 : ℝ)) (σ := (62008323/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (776665745/826922144 : ℝ) ^ p + (407521647/413461072 : ℝ) ^ p := by
    exact cert_lt (x := (776665745/826922144 : ℝ)) (y := (407521647/413461072 : ℝ)) (X := (26436468665487/100000000000000 : ℝ)) (Y := (73563532213281/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (457845061/500000000 : ℝ)) (n' := (25841317/31250000 : ℝ)) (Ab := (155333149/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (7325521/8000000 : ℝ) ^ p + (992133167/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7325521/8000000 : ℝ)) (y := (992133167/1000000000 : ℝ)) (X := (7714746140373/50000000000000 : ℝ)) (Y := (2642828839241/3125000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992133167/1000000000 : ℝ) ^ p + (7325521/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992133167/1000000000 : ℝ)) (y := (7325521/8000000 : ℝ)) (X := (2642828839241/3125000000000 : ℝ)) (Y := (7714746140373/50000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (476955823/250000000 : ℝ)) (τ := (7325521/8000000 : ℝ)) (σ := (992133167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (258888583/275640716 : ℝ) ^ p + (407521649/413461074 : ℝ) ^ p := by
    exact cert_lt (x := (258888583/275640716 : ℝ)) (y := (407521649/413461074 : ℝ)) (X := (6609117210267/25000000000000 : ℝ)) (Y := (73563532323327/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (7325521/8000000 : ℝ)) (n' := (206730537/250000000 : ℝ)) (Ab := (776665749/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (476955823/250000000 : ℝ)) (τ := (7325521/8000000 : ℝ)) (σ := (992133167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (7325521/8000000 : ℝ)) (n' := (206730537/250000000 : ℝ)) (Ab := (776665749/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (476955823/250000000 : ℝ)) (τ := (7325521/8000000 : ℝ)) (σ := (992133167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (7325521/8000000 : ℝ)) (n' := (206730537/250000000 : ℝ)) (Ab := (776665749/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (476955823/250000000 : ℝ)) (τ := (7325521/8000000 : ℝ)) (σ := (992133167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (7325521/8000000 : ℝ)) (n' := (206730537/250000000 : ℝ)) (Ab := (776665749/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (476955823/250000000 : ℝ)) (τ := (7325521/8000000 : ℝ)) (σ := (992133167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1642162217/1807532625 : ℝ) ^ p + (71826151/72301305 : ℝ) ^ p := by
    exact cert_lt (x := (1642162217/1807532625 : ℝ)) (y := (71826151/72301305 : ℝ)) (X := (13056079770943/100000000000000 : ℝ)) (Y := (86943920444093/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (367690897/397489125 : ℝ) ^ p + (47223541/47698695 : ℝ) ^ p := by
    exact cert_lt (x := (367690897/397489125 : ℝ)) (y := (47223541/47698695 : ℝ)) (X := (19138466912971/100000000000000 : ℝ)) (Y := (80861533555643/100000000000000 : ℝ)) 679 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992133167/1000000000 : ℝ)) (U := (9539739/8000000 : ℝ)) (Ab := (1642162217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (7325521/8000000 : ℝ)) (σ := (992133167/1000000000 : ℝ)) (Ab := (1103072691/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab006
