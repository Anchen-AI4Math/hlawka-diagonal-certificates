import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 3, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab003 (p : ℝ) (hpa : (675/32 : ℝ) ≤ p) (hpb : p ≤ (169/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (85169169377/3685500000000 : ℝ) (3821/320000 : ℝ) (160000022113/737100000000 : ℝ) (3033/2500 : ℝ) (241930191/125000000 : ℝ) (967673723/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192431433/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11027/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1103/2500 : ℝ)
      else (1513/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11831/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (85169169377/3685500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3821/320000 : ℝ) := by norm_num
  have pc0 : 1 < (454491661/500000000 : ℝ) ^ p + (62078519/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (454491661/500000000 : ℝ)) (y := (62078519/62500000 : ℝ)) (X := (13319677254147/100000000000000 : ℝ)) (Y := (4334016925787/5000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (62078519/62500000 : ℝ) ^ p + (454491661/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62078519/62500000 : ℝ)) (y := (454491661/500000000 : ℝ)) (X := (4334016925787/5000000000000 : ℝ)) (Y := (13319677254147/100000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (951119813/500000000 : ℝ)) (τ := (454491661/500000000 : ℝ)) (σ := (62078519/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (769314926/818975269 : ℝ) ^ p + (807034644/818975269 : ℝ) ^ p := by
    exact cert_lt (x := (769314926/818975269 : ℝ)) (y := (807034644/818975269 : ℝ)) (X := (26675033084887/100000000000000 : ℝ)) (Y := (73324968307079/100000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (454491661/500000000 : ℝ)) (n' := (818975269/1000000000 : ℝ)) (Ab := (384657463/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (14296221/15625000 : ℝ) ^ p + (496086009/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (14296221/15625000 : ℝ)) (y := (496086009/500000000 : ℝ)) (X := (3824202946911/25000000000000 : ℝ)) (Y := (4235160193557/5000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496086009/500000000 : ℝ) ^ p + (14296221/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (496086009/500000000 : ℝ)) (y := (14296221/15625000 : ℝ)) (X := (4235160193557/5000000000000 : ℝ)) (Y := (3824202946911/25000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (953565081/500000000 : ℝ)) (τ := (14296221/15625000 : ℝ)) (σ := (496086009/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (258593453/275383778 : ℝ) ^ p + (814210709/826151334 : ℝ) ^ p := by
    exact cert_lt (x := (258593453/275383778 : ℝ)) (y := (814210709/826151334 : ℝ)) (X := (13237851477861/50000000000000 : ℝ)) (Y := (36762148992949/50000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (14296221/15625000 : ℝ)) (n' := (413075667/500000000 : ℝ)) (Ab := (775780359/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (457631613/500000000 : ℝ) ^ p + (198422407/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (457631613/500000000 : ℝ)) (y := (198422407/200000000 : ℝ)) (X := (15404923016903/100000000000000 : ℝ)) (Y := (84595091949723/100000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198422407/200000000 : ℝ) ^ p + (457631613/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198422407/200000000 : ℝ)) (y := (457631613/500000000 : ℝ)) (X := (84595091949723/100000000000000 : ℝ)) (Y := (15404923016903/100000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1907375261/1000000000 : ℝ)) (τ := (457631613/500000000 : ℝ)) (σ := (198422407/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (388054658/413258263 : ℝ) ^ p + (814575901/826516526 : ℝ) ^ p := by
    exact cert_lt (x := (388054658/413258263 : ℝ)) (y := (814575901/826516526 : ℝ)) (X := (6616409565933/25000000000000 : ℝ)) (Y := (14706872606937/20000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (457631613/500000000 : ℝ)) (n' := (413258263/500000000 : ℝ)) (Ab := (194027329/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (7322229/8000000 : ℝ) ^ p + (198421799/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (7322229/8000000 : ℝ)) (y := (198421799/200000000 : ℝ)) (X := (3852599794711/25000000000000 : ℝ)) (Y := (42294808114061/50000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198421799/200000000 : ℝ) ^ p + (7322229/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (198421799/200000000 : ℝ)) (y := (7322229/8000000 : ℝ)) (X := (42294808114061/50000000000000 : ℝ)) (Y := (3852599794711/25000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (95369381/50000000 : ℝ)) (τ := (7322229/8000000 : ℝ)) (σ := (198421799/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (258708639/275511652 : ℝ) ^ p + (814594331/826534956 : ℝ) ^ p := by
    exact cert_lt (x := (258708639/275511652 : ℝ)) (y := (814594331/826534956 : ℝ)) (X := (13232565209221/50000000000000 : ℝ)) (Y := (36767435391267/50000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (7322229/8000000 : ℝ)) (n' := (206633739/250000000 : ℝ)) (Ab := (776125917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (915279403/1000000000 : ℝ) ^ p + (992108841/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915279403/1000000000 : ℝ)) (y := (992108841/1000000000 : ℝ)) (X := (123285407191/800000000000 : ℝ)) (Y := (4229466942429/5000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992108841/1000000000 : ℝ) ^ p + (915279403/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992108841/1000000000 : ℝ)) (y := (915279403/1000000000 : ℝ)) (X := (4229466942429/5000000000000 : ℝ)) (Y := (123285407191/800000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (476847061/250000000 : ℝ)) (τ := (915279403/1000000000 : ℝ)) (σ := (992108841/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (776126755/826535887 : ℝ) ^ p + (814595262/826535887 : ℝ) ^ p := by
    exact cert_lt (x := (776126755/826535887 : ℝ)) (y := (814595262/826535887 : ℝ)) (X := (13232552163923/50000000000000 : ℝ)) (Y := (3676744821557/5000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (915279403/1000000000 : ℝ)) (n' := (826535887/1000000000 : ℝ)) (Ab := (155225351/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (915279441/1000000000 : ℝ) ^ p + (496054417/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915279441/1000000000 : ℝ)) (y := (496054417/500000000 : ℝ)) (X := (3852672353721/25000000000000 : ℝ)) (Y := (84589326240439/100000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496054417/500000000 : ℝ) ^ p + (915279441/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496054417/500000000 : ℝ)) (y := (915279441/1000000000 : ℝ)) (X := (84589326240439/100000000000000 : ℝ)) (Y := (3852672353721/25000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (76295531/40000000 : ℝ)) (τ := (915279441/1000000000 : ℝ)) (σ := (496054417/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (194031699/206633983 : ℝ) ^ p + (814595307/826535932 : ℝ) ^ p := by
    exact cert_lt (x := (194031699/206633983 : ℝ)) (y := (814595307/826535932 : ℝ)) (X := (6616275855861/25000000000000 : ℝ)) (Y := (18383724417717/25000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (915279441/1000000000 : ℝ)) (n' := (206633983/250000000 : ℝ)) (Ab := (194031699/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (228819861/250000000 : ℝ) ^ p + (992108833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (228819861/250000000 : ℝ)) (y := (992108833/1000000000 : ℝ)) (X := (7705345240969/50000000000000 : ℝ)) (Y := (21147331109819/25000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992108833/1000000000 : ℝ) ^ p + (228819861/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992108833/1000000000 : ℝ)) (y := (228819861/250000000 : ℝ)) (X := (21147331109819/25000000000000 : ℝ)) (Y := (7705345240969/50000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1907388277/1000000000 : ℝ)) (τ := (228819861/250000000 : ℝ)) (σ := (992108833/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (48507925/51658496 : ℝ) ^ p + (814595311/826535936 : ℝ) ^ p := by
    exact cert_lt (x := (48507925/51658496 : ℝ)) (y := (814595311/826535936 : ℝ)) (X := (13232551799587/50000000000000 : ℝ)) (Y := (36767448890533/50000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (228819861/250000000 : ℝ)) (n' := (1614328/1953125 : ℝ)) (Ab := (1940317/2500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1907388277/1000000000 : ℝ)) (τ := (228819861/250000000 : ℝ)) (σ := (992108833/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (228819861/250000000 : ℝ)) (n' := (1614328/1953125 : ℝ)) (Ab := (1940317/2500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1907388277/1000000000 : ℝ)) (τ := (228819861/250000000 : ℝ)) (σ := (992108833/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (228819861/250000000 : ℝ)) (n' := (1614328/1953125 : ℝ)) (Ab := (1940317/2500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1907388277/1000000000 : ℝ)) (τ := (228819861/250000000 : ℝ)) (σ := (992108833/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (228819861/250000000 : ℝ)) (n' := (1614328/1953125 : ℝ)) (Ab := (1940317/2500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1907388277/1000000000 : ℝ)) (τ := (228819861/250000000 : ℝ)) (σ := (992108833/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (234507214/258224081 : ℝ) ^ p + (1795627942/1807568567 : ℝ) ^ p := by
    exact cert_lt (x := (234507214/258224081 : ℝ)) (y := (1795627942/1807568567 : ℝ)) (X := (6532640192529/50000000000000 : ℝ)) (Y := (86934719916301/100000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1102696251/1192431433 : ℝ) ^ p + (1180490808/1192431433 : ℝ) ^ p := by
    exact cert_lt (x := (1102696251/1192431433 : ℝ)) (y := (1180490808/1192431433 : ℝ)) (X := (19152476559679/100000000000000 : ℝ)) (Y := (40423762044567/50000000000000 : ℝ)) 169 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992108833/1000000000 : ℝ)) (U := (1192431433/1000000000 : ℝ)) (Ab := (820775249/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (228819861/250000000 : ℝ)) (σ := (992108833/1000000000 : ℝ)) (Ab := (1102696251/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab003
