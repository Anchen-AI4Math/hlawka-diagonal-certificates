import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 135, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab135 (p : ℝ) (hpa : (807/32 : ℝ) ≤ p) (hpb : p ≤ (101/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1040690332783/55077750000000 : ℝ) (1942147/200000000 : ℝ) (4000000660933/22031100000000 : ℝ) (3033/2500 : ℝ) (121615249/62500000 : ℝ) (15201389/15625000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (37315261/31250000 : ℝ)) ∧
    (∀ j i, if j = i then -(11173/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2333/5000 : ℝ)
      else (1563/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1040690332783/55077750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1942147/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (924573711/1000000000 : ℝ) ^ p + (497066989/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924573711/1000000000 : ℝ)) (y := (497066989/500000000 : ℝ)) (X := (6902301202149/50000000000000 : ℝ)) (Y := (86195415785447/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497066989/500000000 : ℝ) ^ p + (924573711/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497066989/500000000 : ℝ)) (y := (924573711/1000000000 : ℝ)) (X := (86195415785447/100000000000000 : ℝ)) (Y := (6902301202149/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1918707689/1000000000 : ℝ)) (τ := (924573711/1000000000 : ℝ)) (σ := (497066989/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (789809323/833585920 : ℝ) ^ p + (164775037/166717184 : ℝ) ^ p := by
    exact cert_lt (x := (789809323/833585920 : ℝ)) (y := (164775037/166717184 : ℝ)) (X := (3201475050543/12500000000000 : ℝ)) (Y := (743882012121/1000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (924573711/1000000000 : ℝ)) (n' := (651239/781250 : ℝ)) (Ab := (789809323/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (464995807/500000000 : ℝ) ^ p + (99311913/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (464995807/500000000 : ℝ)) (y := (99311913/100000000 : ℝ)) (X := (7999550286509/50000000000000 : ℝ)) (Y := (84000916903023/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99311913/100000000 : ℝ) ^ p + (464995807/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99311913/100000000 : ℝ)) (y := (464995807/500000000 : ℝ)) (X := (84000916903023/100000000000000 : ℝ)) (Y := (7999550286509/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (240388843/125000000 : ℝ)) (τ := (464995807/500000000 : ℝ)) (σ := (99311913/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (113661437/119992572 : ℝ) ^ p + (830237269/839948004 : ℝ) ^ p := by
    exact cert_lt (x := (113661437/119992572 : ℝ)) (y := (830237269/839948004 : ℝ)) (X := (25443930257421/100000000000000 : ℝ)) (Y := (18639017823467/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (464995807/500000000 : ℝ)) (n' := (209987001/250000000 : ℝ)) (Ab := (795630059/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (232551831/250000000 : ℝ) ^ p + (993075109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232551831/250000000 : ℝ)) (y := (993075109/1000000000 : ℝ)) (X := (3218613285767/20000000000000 : ℝ)) (Y := (41953475469887/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993075109/1000000000 : ℝ) ^ p + (232551831/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993075109/1000000000 : ℝ)) (y := (232551831/250000000 : ℝ)) (X := (41953475469887/50000000000000 : ℝ)) (Y := (3218613285767/20000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1923282433/1000000000 : ℝ)) (τ := (232551831/250000000 : ℝ)) (σ := (993075109/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795861081/840200552 : ℝ) ^ p + (830489817/840200552 : ℝ) ^ p := by
    exact cert_lt (x := (795861081/840200552 : ℝ)) (y := (830489817/840200552 : ℝ)) (X := (5087462197757/20000000000000 : ℝ)) (Y := (14912538002013/20000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (232551831/250000000 : ℝ)) (n' := (105025069/125000000 : ℝ)) (Ab := (795861081/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (465107913/500000000 : ℝ) ^ p + (124134171/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (465107913/500000000 : ℝ)) (y := (124134171/125000000 : ℝ)) (X := (4024195209329/25000000000000 : ℝ)) (Y := (41951618363561/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124134171/125000000 : ℝ) ^ p + (465107913/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124134171/125000000 : ℝ)) (y := (465107913/500000000 : ℝ)) (X := (41951618363561/50000000000000 : ℝ)) (Y := (4024195209329/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (961644597/500000000 : ℝ)) (τ := (465107913/500000000 : ℝ)) (σ := (124134171/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (795870186/840210505 : ℝ) ^ p + (166099954/168042101 : ℝ) ^ p := by
    exact cert_lt (x := (795870186/840210505 : ℝ)) (y := (166099954/168042101 : ℝ)) (X := (12718525258217/50000000000000 : ℝ)) (Y := (74562950785913/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (465107913/500000000 : ℝ)) (n' := (168042101/200000000 : ℝ)) (Ab := (397935093/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465108081/500000000 : ℝ) ^ p + (993073299/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465108081/500000000 : ℝ)) (y := (993073299/1000000000 : ℝ)) (X := (1609692764807/10000000000000 : ℝ)) (Y := (1310985773863/1562500000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993073299/1000000000 : ℝ) ^ p + (465108081/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993073299/1000000000 : ℝ)) (y := (465108081/500000000 : ℝ)) (X := (1310985773863/1562500000000 : ℝ)) (Y := (1609692764807/10000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1923289461/1000000000 : ℝ)) (τ := (465108081/500000000 : ℝ)) (σ := (993073299/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (795870545/840210898 : ℝ) ^ p + (830500163/840210898 : ℝ) ^ p := by
    exact cert_lt (x := (795870545/840210898 : ℝ)) (y := (830500163/840210898 : ℝ)) (X := (5087407963021/20000000000000 : ℝ)) (Y := (74562961082691/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465108081/500000000 : ℝ)) (n' := (420105449/500000000 : ℝ)) (Ab := (159174109/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (465108087/500000000 : ℝ) ^ p + (993073297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465108087/500000000 : ℝ)) (y := (993073297/1000000000 : ℝ)) (X := (3219386578267/20000000000000 : ℝ)) (Y := (20975771315143/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993073297/1000000000 : ℝ) ^ p + (465108087/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993073297/1000000000 : ℝ)) (y := (465108087/500000000 : ℝ)) (X := (20975771315143/25000000000000 : ℝ)) (Y := (3219386578267/20000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1923289471/1000000000 : ℝ)) (τ := (465108087/500000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (44215031/46678384 : ℝ) ^ p + (830500177/840210912 : ℝ) ^ p := by
    exact cert_lt (x := (44215031/46678384 : ℝ)) (y := (830500177/840210912 : ℝ)) (X := (25437039604327/100000000000000 : ℝ)) (Y := (74562961449497/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (465108087/500000000 : ℝ)) (n' := (26256591/31250000 : ℝ)) (Ab := (397935279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (37208647/40000000 : ℝ) ^ p + (993073297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (37208647/40000000 : ℝ)) (y := (993073297/1000000000 : ℝ)) (X := (16096933328273/100000000000000 : ℝ)) (Y := (20975771315143/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993073297/1000000000 : ℝ) ^ p + (37208647/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (993073297/1000000000 : ℝ)) (y := (37208647/40000000 : ℝ)) (X := (20975771315143/25000000000000 : ℝ)) (Y := (16096933328273/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (795870559/840210913 : ℝ) ^ p + (830500178/840210913 : ℝ) ^ p := by
    exact cert_lt (x := (795870559/840210913 : ℝ)) (y := (830500178/840210913 : ℝ)) (X := (6359259911729/25000000000000 : ℝ)) (Y := (74562961475697/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1664337707/1805911648 : ℝ) ^ p + (1796200913/1805911648 : ℝ) ^ p := by
    exact cert_lt (x := (1664337707/1805911648 : ℝ)) (y := (1796200913/1805911648 : ℝ)) (X := (636399864481/5000000000000 : ℝ)) (Y := (872720030849/1000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1117211313/1194088352 : ℝ) ^ p + (1184377617/1194088352 : ℝ) ^ p := by
    exact cert_lt (x := (1117211313/1194088352 : ℝ)) (y := (1184377617/1194088352 : ℝ)) (X := (18631434165539/100000000000000 : ℝ)) (Y := (81368566596637/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993073297/1000000000 : ℝ)) (U := (37315261/31250000 : ℝ)) (Ab := (1664337707/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ)) (Ab := (1117211313/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab135
