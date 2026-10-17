import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 39, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab039 (p : ℝ) (hpa : (455/16 : ℝ) ≤ p) (hpb : p ≤ (57/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2248592503/157472656250 : ℝ) (7315791/1000000000 : ℝ) (640000120939/4031300000000 : ℝ) (591/500 : ℝ) (487986209/250000000 : ℝ) (3903681/4000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231380497/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5431/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5553/10000 : ℝ)
      else (513/625 : ℝ) ≤ X j i ∧ X j i ≤ (5743/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2248592503/157472656250 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7315791/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (23480209/25000000 : ℝ) ^ p + (99359313/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (23480209/25000000 : ℝ)) (y := (99359313/100000000 : ℝ)) (X := (16738462525001/100000000000000 : ℝ)) (Y := (65048091713/78125000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99359313/100000000 : ℝ) ^ p + (23480209/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (99359313/100000000 : ℝ)) (y := (23480209/25000000 : ℝ)) (X := (65048091713/78125000000 : ℝ)) (Y := (16738462525001/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193280149/100000000 : ℝ)) (τ := (23480209/25000000 : ℝ)) (σ := (99359313/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (821375215/866953187 : ℝ) ^ p + (859637396/866953187 : ℝ) ^ p := by
    exact cert_lt (x := (821375215/866953187 : ℝ)) (y := (859637396/866953187 : ℝ)) (X := (10728264632489/50000000000000 : ℝ)) (Y := (39271736064339/50000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (23480209/25000000 : ℝ)) (n' := (866953187/1000000000 : ℝ)) (Ab := (164275043/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (942525211/1000000000 : ℝ) ^ p + (248211167/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (942525211/1000000000 : ℝ)) (y := (248211167/250000000 : ℝ)) (X := (18507587331343/100000000000000 : ℝ)) (Y := (40746215402477/50000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248211167/250000000 : ℝ) ^ p + (942525211/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248211167/250000000 : ℝ)) (y := (942525211/1000000000 : ℝ)) (X := (40746215402477/50000000000000 : ℝ)) (Y := (18507587331343/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1935369879/1000000000 : ℝ)) (τ := (942525211/1000000000 : ℝ)) (σ := (248211167/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (412432889/435378099 : ℝ) ^ p + (287813469/290252066 : ℝ) ^ p := by
    exact cert_lt (x := (412432889/435378099 : ℝ)) (y := (287813469/290252066 : ℝ)) (X := (106866425617/500000000000 : ℝ)) (Y := (15725343263429/20000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (942525211/1000000000 : ℝ)) (n' := (435378099/500000000 : ℝ)) (Ab := (412432889/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (942619817/1000000000 : ℝ) ^ p + (992821997/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942619817/1000000000 : ℝ)) (y := (992821997/1000000000 : ℝ)) (X := (18560604909411/100000000000000 : ℝ)) (Y := (40719706902373/50000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992821997/1000000000 : ℝ) ^ p + (942619817/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992821997/1000000000 : ℝ)) (y := (942619817/1000000000 : ℝ)) (X := (40719706902373/50000000000000 : ℝ)) (Y := (18560604909411/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (967720907/500000000 : ℝ)) (τ := (942619817/1000000000 : ℝ)) (σ := (992821997/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (206241288/217716119 : ℝ) ^ p + (863548685/870864476 : ℝ) ^ p := by
    exact cert_lt (x := (206241288/217716119 : ℝ)) (y := (863548685/870864476 : ℝ)) (X := (10685462122427/50000000000000 : ℝ)) (Y := (39314538506019/50000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (942619817/1000000000 : ℝ)) (n' := (217716119/250000000 : ℝ)) (Ab := (25780161/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (377049/400000 : ℝ) ^ p + (992821353/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (377049/400000 : ℝ)) (y := (992821353/1000000000 : ℝ)) (X := (9281055304081/50000000000000 : ℝ)) (Y := (81437908272361/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992821353/1000000000 : ℝ) ^ p + (377049/400000 : ℝ) ^ p := by
    exact cert_lt (x := (992821353/1000000000 : ℝ)) (y := (377049/400000 : ℝ)) (X := (81437908272361/100000000000000 : ℝ)) (Y := (9281055304081/50000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1935443853/1000000000 : ℝ)) (τ := (377049/400000 : ℝ)) (σ := (992821353/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (824967970/870867547 : ℝ) ^ p + (863551756/870867547 : ℝ) ^ p := by
    exact cert_lt (x := (824967970/870867547 : ℝ)) (y := (863551756/870867547 : ℝ)) (X := (21370856955477/100000000000000 : ℝ)) (Y := (39314571979463/50000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (377049/400000 : ℝ)) (n' := (870867547/1000000000 : ℝ)) (Ab := (82496797/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (58913911/62500000 : ℝ) ^ p + (198564267/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (58913911/62500000 : ℝ)) (y := (198564267/200000000 : ℝ)) (X := (3712430652211/20000000000000 : ℝ)) (Y := (81437866192649/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198564267/200000000 : ℝ) ^ p + (58913911/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (198564267/200000000 : ℝ)) (y := (58913911/62500000 : ℝ)) (X := (81437866192649/100000000000000 : ℝ)) (Y := (3712430652211/20000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1935443911/1000000000 : ℝ)) (τ := (58913911/62500000 : ℝ)) (σ := (198564267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (412484025/435433817 : ℝ) ^ p + (123364549/124409662 : ℝ) ^ p := by
    exact cert_lt (x := (412484025/435433817 : ℝ)) (y := (123364549/124409662 : ℝ)) (X := (1068542758639/5000000000000 : ℝ)) (Y := (39314572927747/50000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (58913911/62500000 : ℝ)) (n' := (435433817/500000000 : ℝ)) (Ab := (16499361/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (942622579/1000000000 : ℝ) ^ p + (496410667/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (942622579/1000000000 : ℝ)) (y := (496410667/500000000 : ℝ)) (X := (4640538736181/25000000000000 : ℝ)) (Y := (10179732981861/12500000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496410667/500000000 : ℝ) ^ p + (942622579/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496410667/500000000 : ℝ)) (y := (942622579/1000000000 : ℝ)) (X := (10179732981861/12500000000000 : ℝ)) (Y := (4640538736181/25000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1935443913/1000000000 : ℝ)) (τ := (942622579/1000000000 : ℝ)) (σ := (496410667/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (824968053/870867637 : ℝ) ^ p + (863551846/870867637 : ℝ) ^ p := by
    exact cert_lt (x := (824968053/870867637 : ℝ)) (y := (863551846/870867637 : ℝ)) (X := (21370855289517/100000000000000 : ℝ)) (Y := (78629145920893/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (942622579/1000000000 : ℝ)) (n' := (870867637/1000000000 : ℝ)) (Ab := (824968053/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1935443913/1000000000 : ℝ)) (τ := (942622579/1000000000 : ℝ)) (σ := (496410667/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (942622579/1000000000 : ℝ)) (n' := (870867637/1000000000 : ℝ)) (Ab := (824968053/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1935443913/1000000000 : ℝ)) (τ := (942622579/1000000000 : ℝ)) (σ := (496410667/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (942622579/1000000000 : ℝ)) (n' := (870867637/1000000000 : ℝ)) (Ab := (824968053/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1935443913/1000000000 : ℝ)) (τ := (942622579/1000000000 : ℝ)) (σ := (496410667/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (942622579/1000000000 : ℝ)) (n' := (870867637/1000000000 : ℝ)) (Ab := (824968053/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1935443913/1000000000 : ℝ)) (τ := (942622579/1000000000 : ℝ)) (σ := (496410667/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (942622579/1000000000 : ℝ)) (n' := (870867637/1000000000 : ℝ)) (Ab := (824968053/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1935443913/1000000000 : ℝ)) (τ := (942622579/1000000000 : ℝ)) (σ := (496410667/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1704176731/1843097515 : ℝ) ^ p + (262254532/263299645 : ℝ) ^ p := by
    exact cert_lt (x := (1704176731/1843097515 : ℝ)) (y := (262254532/263299645 : ℝ)) (X := (10716181232817/100000000000000 : ℝ)) (Y := (89283819097477/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1086116339/1156902485 : ℝ) ^ p + (1149586694/1156902485 : ℝ) ^ p := by
    exact cert_lt (x := (1086116339/1156902485 : ℝ)) (y := (1149586694/1156902485 : ℝ)) (X := (16539348722957/100000000000000 : ℝ)) (Y := (83460651714843/100000000000000 : ℝ)) 57 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496410667/500000000 : ℝ)) (U := (231380497/200000000 : ℝ)) (Ab := (1704176731/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (942622579/1000000000 : ℝ)) (σ := (496410667/500000000 : ℝ)) (Ab := (1086116339/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab039
