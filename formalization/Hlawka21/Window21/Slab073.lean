import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 73, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab073 (p : ℝ) (hpa : (745/32 : ℝ) ≤ p) (hpb : p ≤ (373/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (420352774573/20338500000000 : ℝ) (10646213/1000000000 : ℝ) (800000122031/4067700000000 : ℝ) (3033/2500 : ℝ) (485352409/250000000 : ℝ) (970666077/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (119330067/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11109/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(57/125 : ℝ)
      else (771/1000 : ℝ) ≤ X j i ∧ X j i ≤ (5923/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (420352774573/20338500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10646213/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (91797177/100000000 : ℝ) ^ p + (31054697/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (91797177/100000000 : ℝ)) (y := (31054697/31250000 : ℝ)) (X := (6798743559899/50000000000000 : ℝ)) (Y := (43201265276107/50000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31054697/31250000 : ℝ) ^ p + (91797177/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (31054697/31250000 : ℝ)) (y := (91797177/100000000 : ℝ)) (X := (43201265276107/50000000000000 : ℝ)) (Y := (6798743559899/50000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (955861037/500000000 : ℝ)) (τ := (91797177/100000000 : ℝ)) (σ := (31054697/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (781103143/827489482 : ℝ) ^ p + (42991751/43552078 : ℝ) ^ p := by
    exact cert_lt (x := (781103143/827489482 : ℝ)) (y := (42991751/43552078 : ℝ)) (X := (26057117097907/100000000000000 : ℝ)) (Y := (3697144192411/5000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (91797177/100000000 : ℝ)) (n' := (413744741/500000000 : ℝ)) (Ab := (781103143/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (461827953/500000000 : ℝ) ^ p + (496349847/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461827953/500000000 : ℝ)) (y := (496349847/500000000 : ℝ)) (X := (1570206627889/10000000000000 : ℝ)) (Y := (84297950160739/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496349847/500000000 : ℝ) ^ p + (461827953/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496349847/500000000 : ℝ)) (y := (461827953/500000000 : ℝ)) (X := (84297950160739/100000000000000 : ℝ)) (Y := (1570206627889/10000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (4790889/2500000 : ℝ)) (τ := (461827953/500000000 : ℝ)) (σ := (496349847/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (787227758/834228171 : ℝ) ^ p + (823581958/834228171 : ℝ) ^ p := by
    exact cert_lt (x := (787227758/834228171 : ℝ)) (y := (823581958/834228171 : ℝ)) (X := (25875422839321/100000000000000 : ℝ)) (Y := (74124578601727/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (461827953/500000000 : ℝ)) (n' := (834228171/1000000000 : ℝ)) (Ab := (393613879/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (230977097/250000000 : ℝ) ^ p + (496324483/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (230977097/250000000 : ℝ)) (y := (496324483/500000000 : ℝ)) (X := (7901216626233/50000000000000 : ℝ)) (Y := (21049395951837/25000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496324483/500000000 : ℝ) ^ p + (230977097/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496324483/500000000 : ℝ)) (y := (230977097/250000000 : ℝ)) (X := (21049395951837/25000000000000 : ℝ)) (Y := (7901216626233/50000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958278677/500000000 : ℝ)) (τ := (230977097/250000000 : ℝ)) (σ := (496324483/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (787498900/834526553 : ℝ) ^ p + (823880340/834526553 : ℝ) ^ p := by
    exact cert_lt (x := (787498900/834526553 : ℝ)) (y := (823880340/834526553 : ℝ)) (X := (25867435434097/100000000000000 : ℝ)) (Y := (74132565796371/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (230977097/250000000 : ℝ)) (n' := (834526553/1000000000 : ℝ)) (Ab := (7874989/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (230979871/250000000 : ℝ) ^ p + (124080841/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (230979871/250000000 : ℝ)) (y := (124080841/125000000 : ℝ)) (X := (15806858204239/100000000000000 : ℝ)) (Y := (21048289628813/25000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124080841/125000000 : ℝ) ^ p + (230979871/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124080841/125000000 : ℝ)) (y := (230979871/250000000 : ℝ)) (X := (21048289628813/25000000000000 : ℝ)) (Y := (15806858204239/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (479141553/250000000 : ℝ)) (τ := (230979871/250000000 : ℝ)) (σ := (124080841/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (393755407/417269832 : ℝ) ^ p + (823893451/834539664 : ℝ) ^ p := by
    exact cert_lt (x := (393755407/417269832 : ℝ)) (y := (823893451/834539664 : ℝ)) (X := (404173196871/1562500000000 : ℝ)) (Y := (74132916644133/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (230979871/250000000 : ℝ)) (n' := (52158729/62500000 : ℝ)) (Ab := (393755407/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (923919971/1000000000 : ℝ) ^ p + (99264663/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (923919971/1000000000 : ℝ)) (y := (99264663/100000000 : ℝ)) (X := (3161410488233/20000000000000 : ℝ)) (Y := (84192964740793/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99264663/100000000 : ℝ) ^ p + (923919971/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99264663/100000000 : ℝ)) (y := (923919971/1000000000 : ℝ)) (X := (84192964740793/100000000000000 : ℝ)) (Y := (3161410488233/20000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1916566601/1000000000 : ℝ)) (τ := (923919971/1000000000 : ℝ)) (σ := (99264663/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (787511336/834540239 : ℝ) ^ p + (823894026/834540239 : ℝ) ^ p := by
    exact cert_lt (x := (787511336/834540239 : ℝ)) (y := (823894026/834540239 : ℝ)) (X := (6466767206967/25000000000000 : ℝ)) (Y := (74132932030803/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (923919971/1000000000 : ℝ)) (n' := (834540239/1000000000 : ℝ)) (Ab := (98438917/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (923919993/1000000000 : ℝ) ^ p + (7941173/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (923919993/1000000000 : ℝ)) (y := (7941173/8000000 : ℝ)) (X := (15807061215783/100000000000000 : ℝ)) (Y := (5262059678397/6250000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (7941173/8000000 : ℝ) ^ p + (923919993/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7941173/8000000 : ℝ)) (y := (923919993/1000000000 : ℝ)) (X := (5262059678397/6250000000000 : ℝ)) (Y := (15807061215783/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (958283309/500000000 : ℝ)) (τ := (923919993/1000000000 : ℝ)) (σ := (7941173/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (157502272/166908053 : ℝ) ^ p + (823894052/834540265 : ℝ) ^ p := by
    exact cert_lt (x := (157502272/166908053 : ℝ)) (y := (823894052/834540265 : ℝ)) (X := (25867068418337/100000000000000 : ℝ)) (Y := (74132932726547/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (923919993/1000000000 : ℝ)) (n' := (166908053/200000000 : ℝ)) (Ab := (2460973/3125000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (461959997/500000000 : ℝ) ^ p + (7941173/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (461959997/500000000 : ℝ)) (y := (7941173/8000000 : ℝ)) (X := (15807061614629/100000000000000 : ℝ)) (Y := (5262059678397/6250000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (7941173/8000000 : ℝ) ^ p + (461959997/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (7941173/8000000 : ℝ)) (y := (461959997/500000000 : ℝ)) (X := (5262059678397/6250000000000 : ℝ)) (Y := (15807061614629/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1916566619/1000000000 : ℝ)) (τ := (461959997/500000000 : ℝ)) (σ := (7941173/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (112501623/119220038 : ℝ) ^ p + (823894053/834540266 : ℝ) ^ p := by
    exact cert_lt (x := (112501623/119220038 : ℝ)) (y := (823894053/834540266 : ℝ)) (X := (1616691778843/6250000000000 : ℝ)) (Y := (74132932753307/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (461959997/500000000 : ℝ)) (n' := (417270133/500000000 : ℝ)) (Ab := (787511361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1916566619/1000000000 : ℝ)) (τ := (461959997/500000000 : ℝ)) (σ := (7941173/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (461959997/500000000 : ℝ)) (n' := (417270133/500000000 : ℝ)) (Ab := (787511361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1916566619/1000000000 : ℝ)) (τ := (461959997/500000000 : ℝ)) (σ := (7941173/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (461959997/500000000 : ℝ)) (n' := (417270133/500000000 : ℝ)) (Ab := (787511361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1916566619/1000000000 : ℝ)) (τ := (461959997/500000000 : ℝ)) (σ := (7941173/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (461959997/500000000 : ℝ)) (n' := (417270133/500000000 : ℝ)) (Ab := (787511361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1916566619/1000000000 : ℝ)) (τ := (461959997/500000000 : ℝ)) (σ := (7941173/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (275766047/301116555 : ℝ) ^ p + (1796053117/1806699330 : ℝ) ^ p := by
    exact cert_lt (x := (275766047/301116555 : ℝ)) (y := (1796053117/1806699330 : ℝ)) (X := (12870817102541/100000000000000 : ℝ)) (Y := (87129183126441/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (370294001/397766890 : ℝ) ^ p + (1182654457/1193300670 : ℝ) ^ p := by
    exact cert_lt (x := (370294001/397766890 : ℝ)) (y := (1182654457/1193300670 : ℝ)) (X := (18853932993921/100000000000000 : ℝ)) (Y := (81146067646921/100000000000000 : ℝ)) 373 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (7941173/8000000 : ℝ)) (U := (119330067/100000000 : ℝ)) (Ab := (827298141/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (461959997/500000000 : ℝ)) (σ := (7941173/8000000 : ℝ)) (Ab := (1110882003/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab073
