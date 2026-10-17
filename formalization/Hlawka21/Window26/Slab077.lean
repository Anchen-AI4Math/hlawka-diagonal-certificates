import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 77, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab077 (p : ℝ) (hpa : (493/16 : ℝ) ≤ p) (hpb : p ≤ (247/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1425468367909/109199500000000 : ℝ) (6675391/1000000000 : ℝ) (3200000655197/21839900000000 : ℝ) (591/500 : ℝ) (488900009/250000000 : ℝ) (977755491/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (579140919/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10923/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2813/5000 : ℝ)
      else (2071/2500 : ℝ) ≤ X j i ∧ X j i ≤ (2301/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1425468367909/109199500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6675391/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (944094803/1000000000 : ℝ) ^ p + (994011113/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944094803/1000000000 : ℝ)) (y := (994011113/1000000000 : ℝ)) (X := (529001479373/3125000000000 : ℝ)) (Y := (41535986889167/50000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994011113/1000000000 : ℝ) ^ p + (944094803/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994011113/1000000000 : ℝ)) (y := (944094803/1000000000 : ℝ)) (X := (41535986889167/50000000000000 : ℝ)) (Y := (529001479373/3125000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (484526479/250000000 : ℝ)) (τ := (944094803/1000000000 : ℝ)) (σ := (994011113/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (276038448/290284717 : ℝ) ^ p + (864178760/870854151 : ℝ) ^ p := by
    exact cert_lt (x := (276038448/290284717 : ℝ)) (y := (864178760/870854151 : ℝ)) (X := (21146543578109/100000000000000 : ℝ)) (Y := (3154138296781/4000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (944094803/1000000000 : ℝ)) (n' := (870854151/1000000000 : ℝ)) (Ab := (51757209/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (947223347/1000000000 : ℝ) ^ p + (15520281/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (947223347/1000000000 : ℝ)) (y := (15520281/15625000 : ℝ)) (X := (2343568626861/12500000000000 : ℝ)) (Y := (20312867669761/25000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (15520281/15625000 : ℝ) ^ p + (947223347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (15520281/15625000 : ℝ)) (y := (947223347/1000000000 : ℝ)) (X := (20312867669761/25000000000000 : ℝ)) (Y := (2343568626861/12500000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1940521331/1000000000 : ℝ)) (τ := (947223347/1000000000 : ℝ)) (σ := (15520281/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (831403621/874414928 : ℝ) ^ p + (867739537/874414928 : ℝ) ^ p := by
    exact cert_lt (x := (831403621/874414928 : ℝ)) (y := (867739537/874414928 : ℝ)) (X := (10534962898003/50000000000000 : ℝ)) (Y := (9866259456221/12500000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (947223347/1000000000 : ℝ)) (n' := (54650933/62500000 : ℝ)) (Ab := (831403621/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (947303913/1000000000 : ℝ) ^ p + (993278459/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (947303913/1000000000 : ℝ)) (y := (993278459/1000000000 : ℝ)) (X := (4699461657579/25000000000000 : ℝ)) (Y := (20300543372049/25000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993278459/1000000000 : ℝ) ^ p + (947303913/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993278459/1000000000 : ℝ)) (y := (947303913/1000000000 : ℝ)) (X := (20300543372049/25000000000000 : ℝ)) (Y := (4699461657579/25000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (485145593/250000000 : ℝ)) (τ := (947303913/1000000000 : ℝ)) (σ := (993278459/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (831488151/874506470 : ℝ) ^ p + (867831079/874506470 : ℝ) ^ p := by
    exact cert_lt (x := (831488151/874506470 : ℝ)) (y := (867831079/874506470 : ℝ)) (X := (4213592556537/20000000000000 : ℝ)) (Y := (78932038103391/100000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (947303913/1000000000 : ℝ)) (n' := (87450647/100000000 : ℝ)) (Ab := (831488151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (118413247/125000000 : ℝ) ^ p + (496638979/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (118413247/125000000 : ℝ)) (y := (496638979/500000000 : ℝ)) (X := (18799110607087/100000000000000 : ℝ)) (Y := (634382101033/781250000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496638979/500000000 : ℝ) ^ p + (118413247/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496638979/500000000 : ℝ)) (y := (118413247/125000000 : ℝ)) (X := (634382101033/781250000000 : ℝ)) (Y := (18799110607087/100000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (970291967/500000000 : ℝ)) (τ := (118413247/125000000 : ℝ)) (σ := (496638979/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (415745158/437254407 : ℝ) ^ p + (867833423/874508814 : ℝ) ^ p := by
    exact cert_lt (x := (415745158/437254407 : ℝ)) (y := (867833423/874508814 : ℝ)) (X := (21067912954239/100000000000000 : ℝ)) (Y := (78932088348679/100000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (118413247/125000000 : ℝ)) (n' := (437254407/500000000 : ℝ)) (Ab := (207872579/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (947306029/1000000000 : ℝ) ^ p + (198655589/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (947306029/1000000000 : ℝ)) (y := (198655589/200000000 : ℝ)) (X := (18799143080671/100000000000000 : ℝ)) (Y := (2537527378739/3125000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198655589/200000000 : ℝ) ^ p + (947306029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198655589/200000000 : ℝ)) (y := (947306029/1000000000 : ℝ)) (X := (2537527378739/3125000000000 : ℝ)) (Y := (18799143080671/100000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (970291987/500000000 : ℝ)) (τ := (947306029/1000000000 : ℝ)) (σ := (198655589/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (277163457/291502958 : ℝ) ^ p + (867833483/874508874 : ℝ) ^ p := by
    exact cert_lt (x := (277163457/291502958 : ℝ)) (y := (867833483/874508874 : ℝ)) (X := (10533955675851/50000000000000 : ℝ)) (Y := (39466044817409/50000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (947306029/1000000000 : ℝ)) (n' := (437254437/500000000 : ℝ)) (Ab := (831490371/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (94730603/100000000 : ℝ) ^ p + (198655589/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (94730603/100000000 : ℝ)) (y := (198655589/200000000 : ℝ)) (X := (18799143693381/100000000000000 : ℝ)) (Y := (2537527378739/3125000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198655589/200000000 : ℝ) ^ p + (94730603/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198655589/200000000 : ℝ)) (y := (94730603/100000000 : ℝ)) (X := (2537527378739/3125000000000 : ℝ)) (Y := (18799143693381/100000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (77623359/40000000 : ℝ)) (τ := (94730603/100000000 : ℝ)) (σ := (198655589/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (831490372/874508875 : ℝ) ^ p + (867833484/874508875 : ℝ) ^ p := by
    exact cert_lt (x := (831490372/874508875 : ℝ)) (y := (867833484/874508875 : ℝ)) (X := (4213582278037/20000000000000 : ℝ)) (Y := (39466044828127/50000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (94730603/100000000 : ℝ)) (n' := (6996071/8000000 : ℝ)) (Ab := (207872593/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (77623359/40000000 : ℝ)) (τ := (94730603/100000000 : ℝ)) (σ := (198655589/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (94730603/100000000 : ℝ)) (n' := (6996071/8000000 : ℝ)) (Ab := (207872593/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (77623359/40000000 : ℝ)) (τ := (94730603/100000000 : ℝ)) (σ := (198655589/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (94730603/100000000 : ℝ)) (n' := (6996071/8000000 : ℝ)) (Ab := (207872593/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (77623359/40000000 : ℝ)) (τ := (94730603/100000000 : ℝ)) (σ := (198655589/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (94730603/100000000 : ℝ)) (n' := (6996071/8000000 : ℝ)) (Ab := (207872593/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (77623359/40000000 : ℝ)) (τ := (94730603/100000000 : ℝ)) (σ := (198655589/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (94730603/100000000 : ℝ)) (n' := (6996071/8000000 : ℝ)) (Ab := (207872593/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (77623359/40000000 : ℝ)) (τ := (94730603/100000000 : ℝ)) (σ := (198655589/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (856310845/920859081 : ℝ) ^ p + (1835042771/1841718162 : ℝ) ^ p := by
    exact cert_lt (x := (856310845/920859081 : ℝ)) (y := (1835042771/1841718162 : ℝ)) (X := (2651377500061/25000000000000 : ℝ)) (Y := (2234862254981/2500000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1092284287/1158281838 : ℝ) ^ p + (1151606447/1158281838 : ℝ) ^ p := by
    exact cert_lt (x := (1092284287/1158281838 : ℝ)) (y := (1151606447/1158281838 : ℝ)) (X := (16343664806663/100000000000000 : ℝ)) (Y := (41828167858519/50000000000000 : ℝ)) 247 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198655589/200000000 : ℝ)) (U := (579140919/500000000 : ℝ)) (Ab := (171262169/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (94730603/100000000 : ℝ)) (σ := (198655589/200000000 : ℝ)) (Ab := (1092284287/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab077
