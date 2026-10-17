import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 149, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab149 (p : ℝ) (hpa : (821/32 : ℝ) ≤ p) (hpb : p ≤ (411/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2077199948207/112066500000000 : ℝ) (2380377/250000000 : ℝ) (4000000672399/22413300000000 : ℝ) (3033/2500 : ℝ) (48668849/25000000 : ℝ) (973344987/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597132429/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5593/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(293/625 : ℝ)
      else (7837/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5931/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2077199948207/112066500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2380377/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (925920453/1000000000 : ℝ) ^ p + (497107237/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925920453/1000000000 : ℝ)) (y := (497107237/500000000 : ℝ)) (X := (13847180095737/100000000000000 : ℝ)) (Y := (4307641927979/5000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497107237/500000000 : ℝ) ^ p + (925920453/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497107237/500000000 : ℝ)) (y := (925920453/1000000000 : ℝ)) (X := (4307641927979/5000000000000 : ℝ)) (Y := (13847180095737/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1920134927/1000000000 : ℝ)) (τ := (925920453/1000000000 : ℝ)) (σ := (497107237/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (263863549/278271035 : ℝ) ^ p + (275097199/278271035 : ℝ) ^ p := by
    exact cert_lt (x := (263863549/278271035 : ℝ)) (y := (275097199/278271035 : ℝ)) (X := (510436219681/2000000000000 : ℝ)) (Y := (37239095313369/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (925920453/1000000000 : ℝ)) (n' := (166962621/200000000 : ℝ)) (Ab := (791590647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931278843/1000000000 : ℝ) ^ p + (19864161/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (931278843/1000000000 : ℝ)) (y := (19864161/20000000 : ℝ)) (X := (16059637409743/100000000000000 : ℝ)) (Y := (83940379933853/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (19864161/20000000 : ℝ) ^ p + (931278843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19864161/20000000 : ℝ)) (y := (931278843/1000000000 : ℝ)) (X := (83940379933853/100000000000000 : ℝ)) (Y := (16059637409743/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1924486893/1000000000 : ℝ)) (τ := (931278843/1000000000 : ℝ)) (σ := (19864161/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (797344153/841093083 : ℝ) ^ p + (14588975/14756019 : ℝ) ^ p := by
    exact cert_lt (x := (797344153/841093083 : ℝ)) (y := (14588975/14756019 : ℝ)) (X := (25356833291153/100000000000000 : ℝ)) (Y := (74643168305469/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931278843/1000000000 : ℝ)) (n' := (841093083/1000000000 : ℝ)) (Ab := (797344153/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (465743647/500000000 : ℝ) ^ p + (993165377/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465743647/500000000 : ℝ)) (y := (993165377/1000000000 : ℝ)) (X := (16152231274921/100000000000000 : ℝ)) (Y := (10480973440031/12500000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993165377/1000000000 : ℝ) ^ p + (465743647/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993165377/1000000000 : ℝ)) (y := (465743647/500000000 : ℝ)) (X := (10480973440031/12500000000000 : ℝ)) (Y := (16152231274921/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1924652671/1000000000 : ℝ)) (τ := (465743647/500000000 : ℝ)) (σ := (993165377/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797567282/841336667 : ℝ) ^ p + (831815159/841336667 : ℝ) ^ p := by
    exact cert_lt (x := (797567282/841336667 : ℝ)) (y := (831815159/841336667 : ℝ)) (X := (25350476193661/100000000000000 : ℝ)) (Y := (74649524756679/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (465743647/500000000 : ℝ)) (n' := (841336667/1000000000 : ℝ)) (Ab := (398783641/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (232873831/250000000 : ℝ) ^ p + (993163727/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232873831/250000000 : ℝ)) (y := (993163727/1000000000 : ℝ)) (X := (16155808441693/100000000000000 : ℝ)) (Y := (524026308133/625000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993163727/1000000000 : ℝ) ^ p + (232873831/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163727/1000000000 : ℝ)) (y := (232873831/250000000 : ℝ)) (X := (524026308133/625000000000 : ℝ)) (Y := (16155808441693/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924659051/1000000000 : ℝ)) (τ := (232873831/250000000 : ℝ)) (σ := (993163727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (34677212/36580263 : ℝ) ^ p + (14593413/14760457 : ℝ) ^ p := by
    exact cert_lt (x := (34677212/36580263 : ℝ)) (y := (14593413/14760457 : ℝ)) (X := (20280185061/80000000000 : ℝ)) (Y := (1866244238041/2500000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (232873831/250000000 : ℝ)) (n' := (841346049/1000000000 : ℝ)) (Ab := (199393969/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (931495633/1000000000 : ℝ) ^ p + (62072729/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (931495633/1000000000 : ℝ)) (y := (62072729/62500000 : ℝ)) (X := (16155946108777/100000000000000 : ℝ)) (Y := (83844072681283/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62072729/62500000 : ℝ) ^ p + (931495633/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62072729/62500000 : ℝ)) (y := (931495633/1000000000 : ℝ)) (X := (83844072681283/100000000000000 : ℝ)) (Y := (16155946108777/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1924659297/1000000000 : ℝ)) (τ := (931495633/1000000000 : ℝ)) (σ := (62072729/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797576207/841346410 : ℝ) ^ p + (21890129/22140695 : ℝ) ^ p := by
    exact cert_lt (x := (797576207/841346410 : ℝ)) (y := (21890129/22140695 : ℝ)) (X := (12675111083089/50000000000000 : ℝ)) (Y := (74649778939597/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (931495633/1000000000 : ℝ)) (n' := (84134641/100000000 : ℝ)) (Ab := (797576207/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186299129/200000000 : ℝ) ^ p + (993163661/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186299129/200000000 : ℝ)) (y := (993163661/1000000000 : ℝ)) (X := (8077975727547/50000000000000 : ℝ)) (Y := (41922033087787/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993163661/1000000000 : ℝ) ^ p + (186299129/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163661/1000000000 : ℝ)) (y := (186299129/200000000 : ℝ)) (X := (41922033087787/50000000000000 : ℝ)) (Y := (8077975727547/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962329653/500000000 : ℝ)) (τ := (186299129/200000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797576221/841346425 : ℝ) ^ p + (831824917/841346425 : ℝ) ^ p := by
    exact cert_lt (x := (797576221/841346425 : ℝ)) (y := (831824917/841346425 : ℝ)) (X := (6337555496713/25000000000000 : ℝ)) (Y := (18662444832731/25000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186299129/200000000 : ℝ)) (n' := (33653857/40000000 : ℝ)) (Ab := (797576221/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (465747823/500000000 : ℝ) ^ p + (993163661/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465747823/500000000 : ℝ)) (y := (993163661/1000000000 : ℝ)) (X := (16155951900621/100000000000000 : ℝ)) (Y := (41922033087787/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993163661/1000000000 : ℝ) ^ p + (465747823/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163661/1000000000 : ℝ)) (y := (465747823/500000000 : ℝ)) (X := (41922033087787/50000000000000 : ℝ)) (Y := (16155951900621/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (398788111/420673213 : ℝ) ^ p + (415912459/420673213 : ℝ) ^ p := by
    exact cert_lt (x := (398788111/420673213 : ℝ)) (y := (415912459/420673213 : ℝ)) (X := (25350222029327/100000000000000 : ℝ)) (Y := (74649779357013/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1666341889/1805735142 : ℝ) ^ p + (299368939/300955857 : ℝ) ^ p := by
    exact cert_lt (x := (1666341889/1805735142 : ℝ)) (y := (299368939/300955857 : ℝ)) (X := (2539771867741/20000000000000 : ℝ)) (Y := (2182528522531/2500000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (559268306/597132429 : ℝ) ^ p + (197457225/199044143 : ℝ) ^ p := by
    exact cert_lt (x := (559268306/597132429 : ℝ)) (y := (197457225/199044143 : ℝ)) (X := (9292853559907/50000000000000 : ℝ)) (Y := (81414293311441/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993163661/1000000000 : ℝ)) (U := (597132429/500000000 : ℝ)) (Ab := (1666341889/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ)) (Ab := (279634153/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab149
