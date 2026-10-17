import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 6, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab006 (p : ℝ) (hpa : (211/8 : ℝ) ≤ p) (hpb : p ≤ (423/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (72645552353/4673650000000 : ℝ) (7978777/1000000000 : ℝ) (1600000280419/9347300000000 : ℝ) (591/500 : ℝ) (60882649/31250000 : ℝ) (121757733/125000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (288899067/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10801/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5477/10000 : ℝ)
      else (8131/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2867/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (72645552353/4673650000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7978777/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (23355439/25000000 : ℝ) ^ p + (993181309/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23355439/25000000 : ℝ)) (y := (993181309/1000000000 : ℝ)) (X := (2068377032177/12500000000000 : ℝ)) (Y := (83453002965979/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993181309/1000000000 : ℝ) ^ p + (23355439/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (993181309/1000000000 : ℝ)) (y := (23355439/25000000 : ℝ)) (X := (83453002965979/100000000000000 : ℝ)) (Y := (2068377032177/12500000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1927398869/1000000000 : ℝ)) (τ := (23355439/25000000 : ℝ)) (σ := (993181309/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (814534732/862880125 : ℝ) ^ p + (854901348/862880125 : ℝ) ^ p := by
    exact cert_lt (x := (814534732/862880125 : ℝ)) (y := (854901348/862880125 : ℝ)) (X := (21776210537243/100000000000000 : ℝ)) (Y := (78223790791823/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (23355439/25000000 : ℝ)) (n' := (6903041/8000000 : ℝ)) (Ab := (203633683/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (937708379/1000000000 : ℝ) ^ p + (992401671/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937708379/1000000000 : ℝ)) (y := (992401671/1000000000 : ℝ)) (X := (9130874632707/50000000000000 : ℝ)) (Y := (16347653712691/20000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992401671/1000000000 : ℝ) ^ p + (937708379/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992401671/1000000000 : ℝ)) (y := (937708379/1000000000 : ℝ)) (X := (16347653712691/20000000000000 : ℝ)) (Y := (9130874632707/50000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (38602201/20000000 : ℝ)) (τ := (937708379/1000000000 : ℝ)) (σ := (992401671/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (818213536/866912821 : ℝ) ^ p + (858934044/866912821 : ℝ) ^ p := by
    exact cert_lt (x := (818213536/866912821 : ℝ)) (y := (858934044/866912821 : ℝ)) (X := (21686376799551/100000000000000 : ℝ)) (Y := (195784061317/250000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (937708379/1000000000 : ℝ)) (n' := (866912821/1000000000 : ℝ)) (Ab := (25569173/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (468909093/500000000 : ℝ) ^ p + (49618783/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (468909093/500000000 : ℝ)) (y := (49618783/50000000 : ℝ)) (X := (183183695381/1000000000000 : ℝ)) (Y := (81681648466189/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (49618783/50000000 : ℝ) ^ p + (468909093/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (49618783/50000000 : ℝ)) (y := (468909093/500000000 : ℝ)) (X := (81681648466189/100000000000000 : ℝ)) (Y := (183183695381/1000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (965096923/500000000 : ℝ)) (τ := (468909093/500000000 : ℝ)) (σ := (49618783/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (818329026/867039433 : ℝ) ^ p + (859060656/867039433 : ℝ) ^ p := by
    exact cert_lt (x := (818329026/867039433 : ℝ)) (y := (859060656/867039433 : ℝ)) (X := (4336713573931/20000000000000 : ℝ)) (Y := (39158216524083/50000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (468909093/500000000 : ℝ)) (n' := (867039433/1000000000 : ℝ)) (Ab := (409164513/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (937821619/1000000000 : ℝ) ^ p + (198474969/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (937821619/1000000000 : ℝ)) (y := (198474969/200000000 : ℝ)) (X := (18320142431299/100000000000000 : ℝ)) (Y := (81679875004353/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198474969/200000000 : ℝ) ^ p + (937821619/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198474969/200000000 : ℝ)) (y := (937821619/1000000000 : ℝ)) (X := (81679875004353/100000000000000 : ℝ)) (Y := (18320142431299/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (120637279/62500000 : ℝ)) (τ := (937821619/1000000000 : ℝ)) (σ := (198474969/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (818332637/867043391 : ℝ) ^ p + (859064614/867043391 : ℝ) ^ p := by
    exact cert_lt (x := (818332637/867043391 : ℝ)) (y := (859064614/867043391 : ℝ)) (X := (2168348055761/10000000000000 : ℝ)) (Y := (78316520833299/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (937821619/1000000000 : ℝ)) (n' := (867043391/1000000000 : ℝ)) (Ab := (818332637/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (937821727/1000000000 : ℝ) ^ p + (992374819/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937821727/1000000000 : ℝ)) (y := (992374819/1000000000 : ℝ)) (X := (18320198208071/100000000000000 : ℝ)) (Y := (40839909214133/50000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992374819/1000000000 : ℝ) ^ p + (937821727/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992374819/1000000000 : ℝ)) (y := (937821727/1000000000 : ℝ)) (X := (40839909214133/50000000000000 : ℝ)) (Y := (18320198208071/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (965098273/500000000 : ℝ)) (τ := (937821727/1000000000 : ℝ)) (σ := (992374819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (163666550/173408703 : ℝ) ^ p + (859064738/867043515 : ℝ) ^ p := by
    exact cert_lt (x := (163666550/173408703 : ℝ)) (y := (859064738/867043515 : ℝ)) (X := (2168347773197/10000000000000 : ℝ)) (Y := (4894782723969/6250000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (937821727/1000000000 : ℝ)) (n' := (173408703/200000000 : ℝ)) (Ab := (3273331/4000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (93782173/100000000 : ℝ) ^ p + (992374819/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (93782173/100000000 : ℝ)) (y := (992374819/1000000000 : ℝ)) (X := (18320199757429/100000000000000 : ℝ)) (Y := (40839909214133/50000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992374819/1000000000 : ℝ) ^ p + (93782173/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992374819/1000000000 : ℝ)) (y := (93782173/100000000 : ℝ)) (X := (40839909214133/50000000000000 : ℝ)) (Y := (18320199757429/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1930196549/1000000000 : ℝ)) (τ := (93782173/100000000 : ℝ)) (σ := (992374819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (818332753/867043519 : ℝ) ^ p + (859064742/867043519 : ℝ) ^ p := by
    exact cert_lt (x := (818332753/867043519 : ℝ)) (y := (859064742/867043519 : ℝ)) (X := (21683477188873/100000000000000 : ℝ)) (Y := (3915826183611/5000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (93782173/100000000 : ℝ)) (n' := (867043519/1000000000 : ℝ)) (Ab := (818332753/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1930196549/1000000000 : ℝ)) (τ := (93782173/100000000 : ℝ)) (σ := (992374819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (93782173/100000000 : ℝ)) (n' := (867043519/1000000000 : ℝ)) (Ab := (818332753/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1930196549/1000000000 : ℝ)) (τ := (93782173/100000000 : ℝ)) (σ := (992374819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (93782173/100000000 : ℝ)) (n' := (867043519/1000000000 : ℝ)) (Ab := (818332753/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1930196549/1000000000 : ℝ)) (τ := (93782173/100000000 : ℝ)) (σ := (992374819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (93782173/100000000 : ℝ)) (n' := (867043519/1000000000 : ℝ)) (Ab := (818332753/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1930196549/1000000000 : ℝ)) (τ := (93782173/100000000 : ℝ)) (σ := (992374819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (93782173/100000000 : ℝ)) (n' := (867043519/1000000000 : ℝ)) (Ab := (818332753/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1930196549/1000000000 : ℝ)) (τ := (93782173/100000000 : ℝ)) (σ := (992374819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (565220741/614801244 : ℝ) ^ p + (1836424955/1844403732 : ℝ) ^ p := by
    exact cert_lt (x := (565220741/614801244 : ℝ)) (y := (1836424955/1844403732 : ℝ)) (X := (1353633657777/12500000000000 : ℝ)) (Y := (89170930970813/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1080045421/1155596268 : ℝ) ^ p + (1147617491/1155596268 : ℝ) ^ p := by
    exact cert_lt (x := (1080045421/1155596268 : ℝ)) (y := (1147617491/1155596268 : ℝ)) (X := (1673733564867/10000000000000 : ℝ)) (Y := (83262664878793/100000000000000 : ℝ)) 423 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992374819/1000000000 : ℝ)) (U := (288899067/250000000 : ℝ)) (Ab := (1695662223/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (93782173/100000000 : ℝ)) (σ := (992374819/1000000000 : ℝ)) (Ab := (1080045421/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab006
