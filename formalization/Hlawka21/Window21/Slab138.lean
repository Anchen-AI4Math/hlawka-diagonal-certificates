import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 138, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab138 (p : ℝ) (hpa : (405/16 : ℝ) ≤ p) (hpb : p ≤ (811/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (41609456671/2211300000000 : ℝ) (1933913/200000000 : ℝ) (400000066339/2211300000000 : ℝ) (3033/2500 : ℝ) (973020793/500000000 : ℝ) (972987939/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194126251/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(447/400 : ℝ) ≤ X j i ∧ X j i ≤ -(4671/10000 : ℝ)
      else (391/500 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (41609456671/2211300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1933913/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (924866391/1000000000 : ℝ) ^ p + (994151407/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924866391/1000000000 : ℝ)) (y := (994151407/1000000000 : ℝ)) (X := (13813845674243/100000000000000 : ℝ)) (Y := (21546543168007/25000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994151407/1000000000 : ℝ) ^ p + (924866391/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994151407/1000000000 : ℝ)) (y := (924866391/1000000000 : ℝ)) (X := (21546543168007/25000000000000 : ℝ)) (Y := (13813845674243/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (959508899/500000000 : ℝ)) (τ := (924866391/1000000000 : ℝ)) (σ := (994151407/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (790196291/833853092 : ℝ) ^ p + (824183527/833853092 : ℝ) ^ p := by
    exact cert_lt (x := (790196291/833853092 : ℝ)) (y := (824183527/833853092 : ℝ)) (X := (2559221970703/10000000000000 : ℝ)) (Y := (18601945462487/25000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (924866391/1000000000 : ℝ)) (n' := (208463273/250000000 : ℝ)) (Ab := (790196291/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (465135753/500000000 : ℝ) ^ p + (496569179/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465135753/500000000 : ℝ)) (y := (496569179/500000000 : ℝ)) (X := (16012257345929/100000000000000 : ℝ)) (Y := (83987760875127/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496569179/500000000 : ℝ) ^ p + (465135753/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496569179/500000000 : ℝ)) (y := (465135753/500000000 : ℝ)) (X := (83987760875127/100000000000000 : ℝ)) (Y := (16012257345929/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (240426233/125000000 : ℝ)) (τ := (465135753/500000000 : ℝ)) (σ := (496569179/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (796002561/840197477 : ℝ) ^ p + (830527912/840197477 : ℝ) ^ p := by
    exact cert_lt (x := (796002561/840197477 : ℝ)) (y := (830527912/840197477 : ℝ)) (X := (6356243955863/25000000000000 : ℝ)) (Y := (74575025168879/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (465135753/500000000 : ℝ)) (n' := (840197477/1000000000 : ℝ)) (Ab := (796002561/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (7269419/7812500 : ℝ) ^ p + (99309463/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (7269419/7812500 : ℝ)) (y := (99309463/100000000 : ℝ)) (X := (8052963654357/50000000000000 : ℝ)) (Y := (83894090123809/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99309463/100000000 : ℝ) ^ p + (7269419/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (99309463/100000000 : ℝ)) (y := (7269419/7812500 : ℝ)) (X := (83894090123809/100000000000000 : ℝ)) (Y := (8052963654357/50000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (961790131/500000000 : ℝ)) (τ := (7269419/7812500 : ℝ)) (σ := (99309463/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (796231861/840448067 : ℝ) ^ p + (830778502/840448067 : ℝ) ^ p := by
    exact cert_lt (x := (796231861/840448067 : ℝ)) (y := (830778502/840448067 : ℝ)) (X := (12709207256017/50000000000000 : ℝ)) (Y := (37290793221581/50000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (7269419/7812500 : ℝ)) (n' := (840448067/1000000000 : ℝ)) (Ab := (796231861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (93049403/100000000 : ℝ) ^ p + (993092909/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (93049403/100000000 : ℝ)) (y := (993092909/1000000000 : ℝ)) (X := (16109611740497/100000000000000 : ℝ)) (Y := (83890405583431/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993092909/1000000000 : ℝ) ^ p + (93049403/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993092909/1000000000 : ℝ)) (y := (93049403/100000000 : ℝ)) (X := (83890405583431/100000000000000 : ℝ)) (Y := (16109611740497/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1923586939/1000000000 : ℝ)) (τ := (93049403/100000000 : ℝ)) (σ := (993092909/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (796240853/840457894 : ℝ) ^ p + (830788329/840457894 : ℝ) ^ p := by
    exact cert_lt (x := (796240853/840457894 : ℝ)) (y := (830788329/840457894 : ℝ)) (X := (12709078618371/50000000000000 : ℝ)) (Y := (14916368735613/20000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (93049403/100000000 : ℝ)) (n' := (420228947/500000000 : ℝ)) (Ab := (796240853/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (930494359/1000000000 : ℝ) ^ p + (496546421/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (930494359/1000000000 : ℝ)) (y := (496546421/500000000 : ℝ)) (X := (8054878049127/50000000000000 : ℝ)) (Y := (83890262144271/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496546421/500000000 : ℝ) ^ p + (930494359/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496546421/500000000 : ℝ)) (y := (930494359/1000000000 : ℝ)) (X := (83890262144271/100000000000000 : ℝ)) (Y := (8054878049127/50000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1923587201/1000000000 : ℝ)) (τ := (930494359/1000000000 : ℝ)) (σ := (496546421/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (796241206/840458279 : ℝ) ^ p + (830788714/840458279 : ℝ) ^ p := by
    exact cert_lt (x := (796241206/840458279 : ℝ)) (y := (830788714/840458279 : ℝ)) (X := (12709073867323/50000000000000 : ℝ)) (Y := (74581853755851/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (930494359/1000000000 : ℝ)) (n' := (840458279/1000000000 : ℝ)) (Ab := (398120603/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232623593/250000000 : ℝ) ^ p + (993092839/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232623593/250000000 : ℝ)) (y := (993092839/1000000000 : ℝ)) (X := (3221952360477/20000000000000 : ℝ)) (Y := (83890255721627/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993092839/1000000000 : ℝ) ^ p + (232623593/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993092839/1000000000 : ℝ)) (y := (232623593/250000000 : ℝ)) (X := (83890255721627/100000000000000 : ℝ)) (Y := (3221952360477/20000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1923587211/1000000000 : ℝ)) (τ := (232623593/250000000 : ℝ)) (σ := (993092839/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (796241219/840458294 : ℝ) ^ p + (830788729/840458294 : ℝ) ^ p := by
    exact cert_lt (x := (796241219/840458294 : ℝ)) (y := (830788729/840458294 : ℝ)) (X := (6354536688757/25000000000000 : ℝ)) (Y := (18645463537123/25000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232623593/250000000 : ℝ)) (n' := (420229147/500000000 : ℝ)) (Ab := (796241219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (930494373/1000000000 : ℝ) ^ p + (993092839/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (930494373/1000000000 : ℝ)) (y := (993092839/1000000000 : ℝ)) (X := (3221952448233/20000000000000 : ℝ)) (Y := (83890255721627/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993092839/1000000000 : ℝ) ^ p + (930494373/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993092839/1000000000 : ℝ)) (y := (930494373/1000000000 : ℝ)) (X := (83890255721627/100000000000000 : ℝ)) (Y := (3221952448233/20000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (480896803/250000000 : ℝ)) (τ := (930494373/1000000000 : ℝ)) (σ := (993092839/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (53082748/56030553 : ℝ) ^ p + (166157746/168091659 : ℝ) ^ p := by
    exact cert_lt (x := (53082748/56030553 : ℝ)) (y := (166157746/168091659 : ℝ)) (X := (3177268349699/12500000000000 : ℝ)) (Y := (18645463543667/25000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (930494373/1000000000 : ℝ)) (n' := (168091659/200000000 : ℝ)) (Ab := (39812061/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (480896803/250000000 : ℝ)) (τ := (930494373/1000000000 : ℝ)) (σ := (993092839/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (930494373/1000000000 : ℝ)) (n' := (168091659/200000000 : ℝ)) (Ab := (39812061/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (480896803/250000000 : ℝ)) (τ := (930494373/1000000000 : ℝ)) (σ := (993092839/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (930494373/1000000000 : ℝ)) (n' := (168091659/200000000 : ℝ)) (Ab := (39812061/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (480896803/250000000 : ℝ)) (τ := (930494373/1000000000 : ℝ)) (σ := (993092839/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (930494373/1000000000 : ℝ)) (n' := (168091659/200000000 : ℝ)) (Ab := (39812061/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (480896803/250000000 : ℝ)) (τ := (930494373/1000000000 : ℝ)) (σ := (993092839/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1664772772/1805873749 : ℝ) ^ p + (1796204184/1805873749 : ℝ) ^ p := by
    exact cert_lt (x := (1664772772/1805873749 : ℝ)) (y := (1796204184/1805873749 : ℝ)) (X := (12721665202471/100000000000000 : ℝ)) (Y := (3491133402919/4000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1117498335/1194126251 : ℝ) ^ p + (1184456686/1194126251 : ℝ) ^ p := by
    exact cert_lt (x := (1117498335/1194126251 : ℝ)) (y := (1184456686/1194126251 : ℝ)) (X := (9310753393997/50000000000000 : ℝ)) (Y := (81378494024581/100000000000000 : ℝ)) 811 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993092839/1000000000 : ℝ)) (U := (1194126251/1000000000 : ℝ)) (Ab := (416193193/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (930494373/1000000000 : ℝ)) (σ := (993092839/1000000000 : ℝ)) (Ab := (223499667/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab138
