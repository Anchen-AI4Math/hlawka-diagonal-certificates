import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 68, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab068 (p : ℝ) (hpa : (185/8 : ℝ) ≤ p) (hpb : p ≤ (741/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (105177773611/5050500000000 : ℝ) (5364721/500000000 : ℝ) (200000030303/1010100000000 : ℝ) (3033/2500 : ℝ) (970510089/500000000 : ℝ) (970470831/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (59661863/50000000 : ℝ)) ∧
    (∀ j i, if j = i then -(694/625 : ℝ) ≤ X j i ∧ X j i ≤ -(91/200 : ℝ)
      else (7701/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2369/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (105177773611/5050500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5364721/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (57336801/62500000 : ℝ) ^ p + (993717287/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57336801/62500000 : ℝ)) (y := (993717287/1000000000 : ℝ)) (X := (13579323195331/100000000000000 : ℝ)) (Y := (43210347494867/50000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993717287/1000000000 : ℝ) ^ p + (57336801/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (993717287/1000000000 : ℝ)) (y := (57336801/62500000 : ℝ)) (X := (43210347494867/50000000000000 : ℝ)) (Y := (13579323195331/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1911106103/1000000000 : ℝ)) (τ := (57336801/62500000 : ℝ)) (σ := (993717287/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (780336406/826944745 : ℝ) ^ p + (816215303/826944745 : ℝ) ^ p := by
    exact cert_lt (x := (780336406/826944745 : ℝ)) (y := (816215303/826944745 : ℝ)) (X := (2609678568723/10000000000000 : ℝ)) (Y := (73903215814499/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (57336801/62500000 : ℝ)) (n' := (165388949/200000000 : ℝ)) (Ab := (390168203/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (923094369/1000000000 : ℝ) ^ p + (198532793/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (923094369/1000000000 : ℝ)) (y := (198532793/200000000 : ℝ)) (X := (1567581187793/10000000000000 : ℝ)) (Y := (10540525661393/12500000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198532793/200000000 : ℝ) ^ p + (923094369/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198532793/200000000 : ℝ)) (y := (923094369/1000000000 : ℝ)) (X := (10540525661393/12500000000000 : ℝ)) (Y := (1567581187793/10000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957879167/500000000 : ℝ)) (τ := (923094369/1000000000 : ℝ)) (σ := (198532793/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (786485738/833714529 : ℝ) ^ p + (17510321/17738607 : ℝ) ^ p := by
    exact cert_lt (x := (786485738/833714529 : ℝ)) (y := (17510321/17738607 : ℝ)) (X := (1295695093631/5000000000000 : ℝ)) (Y := (9260762441553/12500000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (923094369/1000000000 : ℝ)) (n' := (833714529/1000000000 : ℝ)) (Ab := (393242869/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (461675093/500000000 : ℝ) ^ p + (496306319/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461675093/500000000 : ℝ)) (y := (496306319/500000000 : ℝ)) (X := (15776717519907/100000000000000 : ℝ)) (Y := (42111649834723/50000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496306319/500000000 : ℝ) ^ p + (461675093/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496306319/500000000 : ℝ)) (y := (461675093/500000000 : ℝ)) (X := (42111649834723/50000000000000 : ℝ)) (Y := (15776717519907/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (239495353/125000000 : ℝ)) (τ := (461675093/500000000 : ℝ)) (σ := (496306319/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (786760529/834017102 : ℝ) ^ p + (411643830/417008551 : ℝ) ^ p := by
    exact cert_lt (x := (786760529/834017102 : ℝ)) (y := (411643830/417008551 : ℝ)) (X := (5181157344381/20000000000000 : ℝ)) (Y := (1852355353771/2500000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (461675093/500000000 : ℝ)) (n' := (417008551/500000000 : ℝ)) (Ab := (786760529/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (461680767/500000000 : ℝ) ^ p + (62038147/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (461680767/500000000 : ℝ)) (y := (62038147/62500000 : ℝ)) (X := (3156241608521/20000000000000 : ℝ)) (Y := (1052735102839/1250000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (62038147/62500000 : ℝ) ^ p + (461680767/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62038147/62500000 : ℝ)) (y := (461680767/500000000 : ℝ)) (X := (1052735102839/1250000000000 : ℝ)) (Y := (3156241608521/20000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957985943/500000000 : ℝ)) (τ := (461680767/500000000 : ℝ)) (σ := (62038147/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (786772717/834030522 : ℝ) ^ p + (411650540/417015261 : ℝ) ^ p := by
    exact cert_lt (x := (786772717/834030522 : ℝ)) (y := (411650540/417015261 : ℝ)) (X := (12952713573189/50000000000000 : ℝ)) (Y := (14818914788259/20000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (461680767/500000000 : ℝ)) (n' := (417015261/500000000 : ℝ)) (Ab := (786772717/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (923362037/1000000000 : ℝ) ^ p + (992610251/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (923362037/1000000000 : ℝ)) (y := (992610251/1000000000 : ℝ)) (X := (7890703556643/50000000000000 : ℝ)) (Y := (21054652447901/25000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992610251/1000000000 : ℝ) ^ p + (923362037/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992610251/1000000000 : ℝ)) (y := (923362037/1000000000 : ℝ)) (X := (21054652447901/25000000000000 : ℝ)) (Y := (7890703556643/50000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (29937067/15625000 : ℝ)) (τ := (923362037/1000000000 : ℝ)) (σ := (992610251/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (786773257/834031117 : ℝ) ^ p + (823301675/834031117 : ℝ) ^ p := by
    exact cert_lt (x := (786773257/834031117 : ℝ)) (y := (823301675/834031117 : ℝ)) (X := (5181082183369/20000000000000 : ℝ)) (Y := (74094589893027/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (923362037/1000000000 : ℝ)) (n' := (834031117/1000000000 : ℝ)) (Ab := (786773257/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (923362059/1000000000 : ℝ) ^ p + (496305123/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (923362059/1000000000 : ℝ)) (y := (496305123/500000000 : ℝ)) (X := (15781415820209/100000000000000 : ℝ)) (Y := (3368743998723/4000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496305123/500000000 : ℝ) ^ p + (923362059/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496305123/500000000 : ℝ)) (y := (923362059/1000000000 : ℝ)) (X := (3368743998723/4000000000000 : ℝ)) (Y := (15781415820209/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (383194461/200000000 : ℝ)) (τ := (923362059/1000000000 : ℝ)) (σ := (496305123/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (786773281/834031143 : ℝ) ^ p + (823301701/834031143 : ℝ) ^ p := by
    exact cert_lt (x := (786773281/834031143 : ℝ)) (y := (823301701/834031143 : ℝ)) (X := (12952705257599/50000000000000 : ℝ)) (Y := (74094590590077/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (923362059/1000000000 : ℝ)) (n' := (834031143/1000000000 : ℝ)) (Ab := (786773281/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (46168103/50000000 : ℝ) ^ p + (496305123/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (46168103/50000000 : ℝ)) (y := (496305123/500000000 : ℝ)) (X := (15781416215979/100000000000000 : ℝ)) (Y := (3368743998723/4000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496305123/500000000 : ℝ) ^ p + (46168103/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (496305123/500000000 : ℝ)) (y := (46168103/50000000 : ℝ)) (X := (3368743998723/4000000000000 : ℝ)) (Y := (15781416215979/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (957986153/500000000 : ℝ)) (τ := (46168103/50000000 : ℝ)) (σ := (496305123/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (393386641/417015572 : ℝ) ^ p + (411650851/417015572 : ℝ) ^ p := by
    exact cert_lt (x := (393386641/417015572 : ℝ)) (y := (411650851/417015572 : ℝ)) (X := (25905410558399/100000000000000 : ℝ)) (Y := (37047295308443/50000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (46168103/50000000 : ℝ)) (n' := (104253893/125000000 : ℝ)) (Ab := (393386641/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (957986153/500000000 : ℝ)) (τ := (46168103/50000000 : ℝ)) (σ := (496305123/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (46168103/50000000 : ℝ)) (n' := (104253893/125000000 : ℝ)) (Ab := (393386641/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (957986153/500000000 : ℝ)) (τ := (46168103/50000000 : ℝ)) (σ := (496305123/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (46168103/50000000 : ℝ)) (n' := (104253893/125000000 : ℝ)) (Ab := (393386641/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (957986153/500000000 : ℝ)) (τ := (46168103/50000000 : ℝ)) (σ := (496305123/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (46168103/50000000 : ℝ)) (n' := (104253893/125000000 : ℝ)) (Ab := (393386641/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (957986153/500000000 : ℝ)) (τ := (46168103/50000000 : ℝ)) (σ := (496305123/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (826871349/903381370 : ℝ) ^ p + (898016649/903381370 : ℝ) ^ p := by
    exact cert_lt (x := (826871349/903381370 : ℝ)) (y := (898016649/903381370 : ℝ)) (X := (2576686186279/20000000000000 : ℝ)) (Y := (87116569307201/100000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (555168139/596618630 : ℝ) ^ p + (591253909/596618630 : ℝ) ^ p := by
    exact cert_lt (x := (555168139/596618630 : ℝ)) (y := (591253909/596618630 : ℝ)) (X := (4718363087149/25000000000000 : ℝ)) (Y := (40563274203747/50000000000000 : ℝ)) 741 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496305123/500000000 : ℝ)) (U := (59661863/50000000 : ℝ)) (Ab := (826871349/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (46168103/50000000 : ℝ)) (σ := (496305123/500000000 : ℝ)) (Ab := (555168139/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab068
