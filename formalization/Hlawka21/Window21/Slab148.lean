import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 148, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab148 (p : ℝ) (hpa : (205/8 : ℝ) ≤ p) (hpb : p ≤ (821/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (4154988343/223860000000 : ℝ) (148981/15625000 : ℝ) (200000033579/1119300000000 : ℝ) (3033/2500 : ℝ) (243336247/125000000 : ℝ) (973312919/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194252287/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2237/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2343/5000 : ℝ)
      else (1567/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11861/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (4154988343/223860000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (148981/15625000 : ℝ) := by norm_num
  have pc0 : 1 < (231456461/250000000 : ℝ) ^ p + (248552199/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (231456461/250000000 : ℝ)) (y := (248552199/250000000 : ℝ)) (X := (13844183484301/100000000000000 : ℝ)) (Y := (43077918296109/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248552199/250000000 : ℝ) ^ p + (231456461/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248552199/250000000 : ℝ)) (y := (231456461/250000000 : ℝ)) (X := (43077918296109/50000000000000 : ℝ)) (Y := (13844183484301/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (24000433/12500000 : ℝ)) (τ := (231456461/250000000 : ℝ)) (σ := (248552199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (395732725/417363537 : ℝ) ^ p + (412596145/417363537 : ℝ) ^ p := by
    exact cert_lt (x := (395732725/417363537 : ℝ)) (y := (412596145/417363537 : ℝ)) (X := (1595507862339/6250000000000 : ℝ)) (Y := (18617968798737/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (231456461/250000000 : ℝ)) (n' := (417363537/500000000 : ℝ)) (Ab := (15829309/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931188473/1000000000 : ℝ) ^ p + (993201767/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931188473/1000000000 : ℝ)) (y := (993201767/1000000000 : ℝ)) (X := (8027692082481/50000000000000 : ℝ)) (Y := (41972316710727/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993201767/1000000000 : ℝ) ^ p + (931188473/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993201767/1000000000 : ℝ)) (y := (931188473/1000000000 : ℝ)) (X := (41972316710727/50000000000000 : ℝ)) (Y := (8027692082481/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (12027439/6250000 : ℝ)) (τ := (931188473/1000000000 : ℝ)) (σ := (993201767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (797223737/841012878 : ℝ) ^ p + (415739047/420506439 : ℝ) ^ p := by
    exact cert_lt (x := (797223737/841012878 : ℝ)) (y := (415739047/420506439 : ℝ)) (X := (25362944020271/100000000000000 : ℝ)) (Y := (37318528422367/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931188473/1000000000 : ℝ)) (n' := (420506439/500000000 : ℝ)) (Ab := (797223737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (931397431/1000000000 : ℝ) ^ p + (993158999/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931397431/1000000000 : ℝ)) (y := (993158999/1000000000 : ℝ)) (X := (1009254692877/6250000000000 : ℝ)) (Y := (16770388506729/20000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993158999/1000000000 : ℝ) ^ p + (931397431/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993158999/1000000000 : ℝ)) (y := (931397431/1000000000 : ℝ)) (X := (16770388506729/20000000000000 : ℝ)) (Y := (1009254692877/6250000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192455643/100000000 : ℝ)) (τ := (931397431/1000000000 : ℝ)) (σ := (993158999/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797447419/841257088 : ℝ) ^ p + (1856523/1877806 : ℝ) ^ p := by
    exact cert_lt (x := (797447419/841257088 : ℝ)) (y := (1856523/1877806 : ℝ)) (X := (12678284847439/50000000000000 : ℝ)) (Y := (74643431552227/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (931397431/1000000000 : ℝ)) (n' := (6572321/7812500 : ℝ)) (Ab := (797447419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (465702747/500000000 : ℝ) ^ p + (993157343/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465702747/500000000 : ℝ)) (y := (993157343/1000000000 : ℝ)) (X := (16151662007869/100000000000000 : ℝ)) (Y := (4192417773563/5000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993157343/1000000000 : ℝ) ^ p + (465702747/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993157343/1000000000 : ℝ)) (y := (465702747/500000000 : ℝ)) (X := (4192417773563/5000000000000 : ℝ)) (Y := (16151662007869/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924562837/1000000000 : ℝ)) (τ := (465702747/500000000 : ℝ)) (σ := (993157343/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (265818683/280422170 : ℝ) ^ p + (59409409/60090465 : ℝ) ^ p := by
    exact cert_lt (x := (265818683/280422170 : ℝ)) (y := (59409409/60090465 : ℝ)) (X := (25356323870173/100000000000000 : ℝ)) (Y := (18660919358661/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (465702747/500000000 : ℝ)) (n' := (84126651/100000000 : ℝ)) (Ab := (797456049/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (186281161/200000000 : ℝ) ^ p + (993157279/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186281161/200000000 : ℝ)) (y := (993157279/1000000000 : ℝ)) (X := (4037950093817/25000000000000 : ℝ)) (Y := (83848216843789/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993157279/1000000000 : ℝ) ^ p + (186281161/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993157279/1000000000 : ℝ)) (y := (186281161/200000000 : ℝ)) (X := (83848216843789/100000000000000 : ℝ)) (Y := (4037950093817/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481140771/250000000 : ℝ)) (τ := (186281161/200000000 : ℝ)) (σ := (993157279/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797456381/841266873 : ℝ) ^ p + (831732089/841266873 : ℝ) ^ p := by
    exact cert_lt (x := (797456381/841266873 : ℝ)) (y := (831732089/841266873 : ℝ)) (X := (25356314002411/100000000000000 : ℝ)) (Y := (597149495261/800000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (186281161/200000000 : ℝ)) (n' := (841266873/1000000000 : ℝ)) (Ab := (797456381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (931405817/1000000000 : ℝ) ^ p + (993157277/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931405817/1000000000 : ℝ)) (y := (993157277/1000000000 : ℝ)) (X := (8075902857113/50000000000000 : ℝ)) (Y := (20962053127921/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993157277/1000000000 : ℝ) ^ p + (931405817/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993157277/1000000000 : ℝ)) (y := (931405817/1000000000 : ℝ)) (X := (20962053127921/25000000000000 : ℝ)) (Y := (8075902857113/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797456394/841266887 : ℝ) ^ p + (831732103/841266887 : ℝ) ^ p := by
    exact cert_lt (x := (797456394/841266887 : ℝ)) (y := (831732103/841266887 : ℝ)) (X := (6339078445349/25000000000000 : ℝ)) (Y := (37321843636487/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1666200916/1805747713 : ℝ) ^ p + (256601847/257963959 : ℝ) ^ p := by
    exact cert_lt (x := (1666200916/1805747713 : ℝ)) (y := (256601847/257963959 : ℝ)) (X := (12700907884197/100000000000000 : ℝ)) (Y := (43649546173099/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1118443140/1194252287 : ℝ) ^ p + (1184717503/1194252287 : ℝ) ^ p := by
    exact cert_lt (x := (1118443140/1194252287 : ℝ)) (y := (1184717503/1194252287 : ℝ)) (X := (9294462746063/50000000000000 : ℝ)) (Y := (3256443006633/4000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993157277/1000000000 : ℝ)) (U := (1194252287/1000000000 : ℝ)) (Ab := (416550229/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ)) (Ab := (55922157/50000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab148
