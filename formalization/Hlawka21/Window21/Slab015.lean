import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 15, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab015 (p : ℝ) (hpa : (687/32 : ℝ) ≤ p) (hpb : p ≤ (43/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2124127647389/93775500000000 : ℝ) (1169723/100000000 : ℝ) (4000000562653/18755100000000 : ℝ) (3033/2500 : ℝ) (484137373/250000000 : ℝ) (968229307/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596288087/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5521/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(111/250 : ℝ)
      else (949/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11833/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2124127647389/93775500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1169723/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (227665239/250000000 : ℝ) ^ p + (993346081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (227665239/250000000 : ℝ)) (y := (993346081/1000000000 : ℝ)) (X := (13371170076587/100000000000000 : ℝ)) (Y := (2165721146631/2500000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993346081/1000000000 : ℝ) ^ p + (227665239/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993346081/1000000000 : ℝ)) (y := (227665239/250000000 : ℝ)) (X := (2165721146631/2500000000000 : ℝ)) (Y := (13371170076587/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1904007037/1000000000 : ℝ)) (τ := (227665239/250000000 : ℝ)) (σ := (993346081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (771509756/820583035 : ℝ) ^ p + (161777161/164116607 : ℝ) ^ p := by
    exact cert_lt (x := (771509756/820583035 : ℝ)) (y := (161777161/164116607 : ℝ)) (X := (5311731245091/20000000000000 : ℝ)) (Y := (73441345201871/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (227665239/250000000 : ℝ)) (n' := (164116607/200000000 : ℝ)) (Ab := (192877439/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (36663523/40000000 : ℝ) ^ p + (3969067/4000000 : ℝ) ^ p := by
    exact cert_lt (x := (36663523/40000000 : ℝ)) (y := (3969067/4000000 : ℝ)) (X := (7686265149787/50000000000000 : ℝ)) (Y := (8462748480439/10000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (3969067/4000000 : ℝ) ^ p + (36663523/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (3969067/4000000 : ℝ)) (y := (36663523/40000000 : ℝ)) (X := (8462748480439/10000000000000 : ℝ)) (Y := (7686265149787/50000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (76354193/40000000 : ℝ)) (τ := (36663523/40000000 : ℝ)) (σ := (3969067/4000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (777918278/827684525 : ℝ) ^ p + (163197459/165536905 : ℝ) ^ p := by
    exact cert_lt (x := (777918278/827684525 : ℝ)) (y := (163197459/165536905 : ℝ)) (X := (26362495531731/100000000000000 : ℝ)) (Y := (73637505880029/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (36663523/40000000 : ℝ)) (n' := (33107381/40000000 : ℝ)) (Ab := (388959139/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (916883171/1000000000 : ℝ) ^ p + (992208493/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (916883171/1000000000 : ℝ)) (y := (992208493/1000000000 : ℝ)) (X := (3095857970209/20000000000000 : ℝ)) (Y := (84520724884563/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992208493/1000000000 : ℝ) ^ p + (916883171/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992208493/1000000000 : ℝ)) (y := (916883171/1000000000 : ℝ)) (X := (84520724884563/100000000000000 : ℝ)) (Y := (3095857970209/20000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (119318229/62500000 : ℝ)) (τ := (916883171/1000000000 : ℝ)) (σ := (992208493/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (45778601/48708054 : ℝ) ^ p + (408169844/414018459 : ℝ) ^ p := by
    exact cert_lt (x := (45778601/48708054 : ℝ)) (y := (408169844/414018459 : ℝ)) (X := (26352835946183/100000000000000 : ℝ)) (Y := (73647165096367/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (916883171/1000000000 : ℝ)) (n' := (414018459/500000000 : ℝ)) (Ab := (778236217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (916897697/1000000000 : ℝ) ^ p + (496102807/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (916897697/1000000000 : ℝ)) (y := (496102807/500000000 : ℝ)) (X := (774228163367/5000000000000 : ℝ)) (Y := (42257726126159/50000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496102807/500000000 : ℝ) ^ p + (916897697/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496102807/500000000 : ℝ)) (y := (916897697/1000000000 : ℝ)) (X := (42257726126159/50000000000000 : ℝ)) (Y := (774228163367/5000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1909103311/1000000000 : ℝ)) (τ := (916897697/1000000000 : ℝ)) (σ := (496102807/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (259417288/276018087 : ℝ) ^ p + (816357031/828054261 : ℝ) ^ p := by
    exact cert_lt (x := (259417288/276018087 : ℝ)) (y := (816357031/828054261 : ℝ)) (X := (5270472119187/20000000000000 : ℝ)) (Y := (73647640293023/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (916897697/1000000000 : ℝ)) (n' := (828054261/1000000000 : ℝ)) (Ab := (97281483/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (229224603/250000000 : ℝ) ^ p + (31006421/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (229224603/250000000 : ℝ)) (y := (31006421/31250000 : ℝ)) (X := (1548482288011/10000000000000 : ℝ)) (Y := (84515192200073/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (31006421/31250000 : ℝ) ^ p + (229224603/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (31006421/31250000 : ℝ)) (y := (229224603/250000000 : ℝ)) (X := (84515192200073/100000000000000 : ℝ)) (Y := (1548482288011/10000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (477275971/250000000 : ℝ)) (τ := (229224603/250000000 : ℝ)) (σ := (31006421/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (155650527/165611023 : ℝ) ^ p + (163271577/165611023 : ℝ) ^ p := by
    exact cert_lt (x := (155650527/165611023 : ℝ)) (y := (163271577/165611023 : ℝ)) (X := (131761687819/500000000000 : ℝ)) (Y := (73647663692109/100000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (229224603/250000000 : ℝ)) (n' := (165611023/200000000 : ℝ)) (Ab := (155650527/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (916898447/1000000000 : ℝ) ^ p + (198441093/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (916898447/1000000000 : ℝ)) (y := (198441093/200000000 : ℝ)) (X := (7742417794267/50000000000000 : ℝ)) (Y := (10564397422577/12500000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198441093/200000000 : ℝ) ^ p + (916898447/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198441093/200000000 : ℝ)) (y := (916898447/1000000000 : ℝ)) (X := (10564397422577/12500000000000 : ℝ)) (Y := (7742417794267/50000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (238637989/125000000 : ℝ)) (τ := (916898447/1000000000 : ℝ)) (σ := (198441093/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (778252673/828055157 : ℝ) ^ p + (816357927/828055157 : ℝ) ^ p := by
    exact cert_lt (x := (778252673/828055157 : ℝ)) (y := (816357927/828055157 : ℝ)) (X := (26352336490747/100000000000000 : ℝ)) (Y := (36823832421441/50000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (916898447/1000000000 : ℝ)) (n' := (828055157/1000000000 : ℝ)) (Ab := (778252673/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (57306153/62500000 : ℝ) ^ p + (198441093/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (57306153/62500000 : ℝ)) (y := (198441093/200000000 : ℝ)) (X := (967802246977/6250000000000 : ℝ)) (Y := (10564397422577/12500000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198441093/200000000 : ℝ) ^ p + (57306153/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (198441093/200000000 : ℝ)) (y := (57306153/62500000 : ℝ)) (X := (10564397422577/12500000000000 : ℝ)) (Y := (967802246977/6250000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1909103913/1000000000 : ℝ)) (τ := (57306153/62500000 : ℝ)) (σ := (198441093/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (129708779/138009193 : ℝ) ^ p + (408178964/414027579 : ℝ) ^ p := by
    exact cert_lt (x := (129708779/138009193 : ℝ)) (y := (408178964/414027579 : ℝ)) (X := (6588084133633/25000000000000 : ℝ)) (Y := (36823832435141/50000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (57306153/62500000 : ℝ)) (n' := (414027579/500000000 : ℝ)) (Ab := (389126337/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1909103913/1000000000 : ℝ)) (τ := (57306153/62500000 : ℝ)) (σ := (198441093/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (57306153/62500000 : ℝ)) (n' := (414027579/500000000 : ℝ)) (Ab := (389126337/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1909103913/1000000000 : ℝ)) (τ := (57306153/62500000 : ℝ)) (σ := (198441093/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (57306153/62500000 : ℝ)) (n' := (414027579/500000000 : ℝ)) (Ab := (389126337/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1909103913/1000000000 : ℝ)) (τ := (57306153/62500000 : ℝ)) (σ := (198441093/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (57306153/62500000 : ℝ)) (n' := (414027579/500000000 : ℝ)) (Ab := (389126337/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1909103913/1000000000 : ℝ)) (τ := (57306153/62500000 : ℝ)) (σ := (198441093/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1643966821/1807423826 : ℝ) ^ p + (897863298/903711913 : ℝ) ^ p := by
    exact cert_lt (x := (1643966821/1807423826 : ℝ)) (y := (897863298/903711913 : ℝ)) (X := (13028981668411/100000000000000 : ℝ)) (Y := (17394203717419/20000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (552093709/596288087 : ℝ) ^ p + (590439472/596288087 : ℝ) ^ p := by
    exact cert_lt (x := (552093709/596288087 : ℝ)) (y := (590439472/596288087 : ℝ)) (X := (19097139083121/100000000000000 : ℝ)) (Y := (40451430751777/50000000000000 : ℝ)) 43 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198441093/200000000 : ℝ)) (U := (596288087/500000000 : ℝ)) (Ab := (1643966821/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (57306153/62500000 : ℝ)) (σ := (198441093/200000000 : ℝ)) (Ab := (552093709/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab015
