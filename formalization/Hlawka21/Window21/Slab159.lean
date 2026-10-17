import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 159, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab159 (p : ℝ) (hpa : (831/32 : ℝ) ≤ p) (hpb : p ≤ (26 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2074299137021/113431500000000 : ℝ) (9390739/1000000000 : ℝ) (4000000680589/22686300000000 : ℝ) (3033/2500 : ℝ) (973692721/500000000 : ℝ) (973661483/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149298789/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2239/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(4703/10000 : ℝ)
      else (7851/10000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2074299137021/113431500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9390739/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (926853423/1000000000 : ℝ) ^ p + (994270689/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926853423/1000000000 : ℝ)) (y := (994270689/1000000000 : ℝ)) (X := (13876741965813/100000000000000 : ℝ)) (Y := (17224655652709/20000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994270689/1000000000 : ℝ) ^ p + (926853423/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994270689/1000000000 : ℝ)) (y := (926853423/1000000000 : ℝ)) (X := (17224655652709/20000000000000 : ℝ)) (Y := (13876741965813/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (120070257/62500000 : ℝ)) (τ := (926853423/1000000000 : ℝ)) (σ := (994270689/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (264275259/278553325 : ℝ) ^ p + (826269236/835659975 : ℝ) ^ p := by
    exact cert_lt (x := (264275259/278553325 : ℝ)) (y := (826269236/835659975 : ℝ)) (X := (6364908659151/25000000000000 : ℝ)) (Y := (7454036633981/10000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (926853423/1000000000 : ℝ)) (n' := (33426399/40000000 : ℝ)) (Ab := (792825777/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46608479/50000000 : ℝ) ^ p + (993270323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46608479/50000000 : ℝ)) (y := (993270323/1000000000 : ℝ)) (X := (16101564746213/100000000000000 : ℝ)) (Y := (83898453277867/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993270323/1000000000 : ℝ) ^ p + (46608479/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (993270323/1000000000 : ℝ)) (y := (46608479/50000000 : ℝ)) (X := (83898453277867/100000000000000 : ℝ)) (Y := (16101564746213/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1925439903/1000000000 : ℝ)) (τ := (46608479/50000000 : ℝ)) (σ := (993270323/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (798531700/841882071 : ℝ) ^ p + (832491332/841882071 : ℝ) ^ p := by
    exact cert_lt (x := (798531700/841882071 : ℝ)) (y := (832491332/841882071 : ℝ)) (X := (2529667357091/10000000000000 : ℝ)) (Y := (14940665534253/20000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46608479/50000000 : ℝ)) (n' := (841882071/1000000000 : ℝ)) (Ab := (7985317/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (932373057/1000000000 : ℝ) ^ p + (993228577/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (932373057/1000000000 : ℝ)) (y := (993228577/1000000000 : ℝ)) (X := (4048299192209/25000000000000 : ℝ)) (Y := (83806821404207/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993228577/1000000000 : ℝ) ^ p + (932373057/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993228577/1000000000 : ℝ)) (y := (932373057/1000000000 : ℝ)) (X := (83806821404207/100000000000000 : ℝ)) (Y := (4048299192209/25000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (962800817/500000000 : ℝ)) (τ := (932373057/1000000000 : ℝ)) (σ := (993228577/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (798749427/842119529 : ℝ) ^ p + (832728790/842119529 : ℝ) ^ p := by
    exact cert_lt (x := (798749427/842119529 : ℝ)) (y := (832728790/842119529 : ℝ)) (X := (25290495538507/100000000000000 : ℝ)) (Y := (7470950589569/10000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (932373057/1000000000 : ℝ)) (n' := (842119529/1000000000 : ℝ)) (Ab := (798749427/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (93238077/100000000 : ℝ) ^ p + (993226989/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (93238077/100000000 : ℝ)) (y := (993226989/1000000000 : ℝ)) (X := (8098340008699/50000000000000 : ℝ)) (Y := (41901668833731/50000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993226989/1000000000 : ℝ) ^ p + (93238077/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993226989/1000000000 : ℝ)) (y := (93238077/100000000 : ℝ)) (X := (41901668833731/50000000000000 : ℝ)) (Y := (8098340008699/50000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1925607759/1000000000 : ℝ)) (τ := (93238077/100000000 : ℝ)) (σ := (993226989/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (798757679/842128529 : ℝ) ^ p + (832737790/842128529 : ℝ) ^ p := by
    exact cert_lt (x := (798757679/842128529 : ℝ)) (y := (832737790/842128529 : ℝ)) (X := (5058052268403/20000000000000 : ℝ)) (Y := (74709740000419/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (93238077/100000000 : ℝ)) (n' := (842128529/1000000000 : ℝ)) (Ab := (798757679/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (466190531/500000000 : ℝ) ^ p + (993226929/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (466190531/500000000 : ℝ)) (y := (993226929/1000000000 : ℝ)) (X := (8098405950469/50000000000000 : ℝ)) (Y := (83803206042859/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993226929/1000000000 : ℝ) ^ p + (466190531/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993226929/1000000000 : ℝ)) (y := (466190531/500000000 : ℝ)) (X := (83803206042859/100000000000000 : ℝ)) (Y := (8098405950469/50000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1925607991/1000000000 : ℝ)) (τ := (466190531/500000000 : ℝ)) (σ := (993226929/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (399378996/421064435 : ℝ) ^ p + (832738131/842128870 : ℝ) ^ p := by
    exact cert_lt (x := (399378996/421064435 : ℝ)) (y := (832738131/842128870 : ℝ)) (X := (25290252749333/100000000000000 : ℝ)) (Y := (74709748870303/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (466190531/500000000 : ℝ)) (n' := (84212887/100000000 : ℝ)) (Ab := (99844749/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (58273817/62500000 : ℝ) ^ p + (993226927/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (58273817/62500000 : ℝ)) (y := (993226927/1000000000 : ℝ)) (X := (4049204104379/25000000000000 : ℝ)) (Y := (5237700103461/6250000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993226927/1000000000 : ℝ) ^ p + (58273817/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (993226927/1000000000 : ℝ)) (y := (58273817/62500000 : ℝ)) (X := (5237700103461/6250000000000 : ℝ)) (Y := (4049204104379/25000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1925607999/1000000000 : ℝ)) (τ := (58273817/62500000 : ℝ)) (σ := (993226927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (798758003/842128882 : ℝ) ^ p + (832738143/842128882 : ℝ) ^ p := by
    exact cert_lt (x := (798758003/842128882 : ℝ)) (y := (832738143/842128882 : ℝ)) (X := (25290252434881/100000000000000 : ℝ)) (Y := (74709749182439/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (58273817/62500000 : ℝ)) (n' := (421064441/500000000 : ℝ)) (Ab := (798758003/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (932381073/1000000000 : ℝ) ^ p + (993226927/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (932381073/1000000000 : ℝ)) (y := (993226927/1000000000 : ℝ)) (X := (16196816869173/100000000000000 : ℝ)) (Y := (5237700103461/6250000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993226927/1000000000 : ℝ) ^ p + (932381073/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993226927/1000000000 : ℝ)) (y := (932381073/1000000000 : ℝ)) (X := (5237700103461/6250000000000 : ℝ)) (Y := (16196816869173/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (240701/125000 : ℝ)) (τ := (932381073/1000000000 : ℝ)) (σ := (993226927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (798758003/842128883 : ℝ) ^ p + (832738144/842128883 : ℝ) ^ p := by
    exact cert_lt (x := (798758003/842128883 : ℝ)) (y := (832738144/842128883 : ℝ)) (X := (12645125827033/50000000000000 : ℝ)) (Y := (74709749208451/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (932381073/1000000000 : ℝ)) (n' := (842128883/1000000000 : ℝ)) (Ab := (798758003/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (240701/125000 : ℝ)) (τ := (932381073/1000000000 : ℝ)) (σ := (993226927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (932381073/1000000000 : ℝ)) (n' := (842128883/1000000000 : ℝ)) (Ab := (798758003/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (240701/125000 : ℝ)) (τ := (932381073/1000000000 : ℝ)) (σ := (993226927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (932381073/1000000000 : ℝ)) (n' := (842128883/1000000000 : ℝ)) (Ab := (798758003/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (240701/125000 : ℝ)) (τ := (932381073/1000000000 : ℝ)) (σ := (993226927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (932381073/1000000000 : ℝ)) (n' := (842128883/1000000000 : ℝ)) (Ab := (798758003/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (240701/125000 : ℝ)) (τ := (932381073/1000000000 : ℝ)) (σ := (993226927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1667733737/1805609688 : ℝ) ^ p + (1796218949/1805609688 : ℝ) ^ p := by
    exact cert_lt (x := (1667733737/1805609688 : ℝ)) (y := (1796218949/1805609688 : ℝ)) (X := (6339336316589/50000000000000 : ℝ)) (Y := (349285310971/400000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1119461651/1194390312 : ℝ) ^ p + (1184999573/1194390312 : ℝ) ^ p := by
    exact cert_lt (x := (1119461651/1194390312 : ℝ)) (y := (1184999573/1194390312 : ℝ)) (X := (9276981038663/50000000000000 : ℝ)) (Y := (81446038758607/100000000000000 : ℝ)) 26 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993226927/1000000000 : ℝ)) (U := (149298789/125000000 : ℝ)) (Ab := (1667733737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (932381073/1000000000 : ℝ)) (σ := (993226927/1000000000 : ℝ)) (Ab := (1119461651/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab159
