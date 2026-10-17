import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 10, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab010 (p : ℝ) (hpa : (213/8 : ℝ) ≤ p) (hpb : p ≤ (427/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (90695248291/5897437500000 : ℝ) (789219/100000000 : ℝ) (1600000283077/9435900000000 : ℝ) (591/500 : ℝ) (487180831/250000000 : ℝ) (487151129/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1155760101/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10809/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5487/10000 : ℝ)
      else (8141/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11471/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (90695248291/5897437500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (789219/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (934865573/1000000000 : ℝ) ^ p + (198646787/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (934865573/1000000000 : ℝ)) (y := (198646787/200000000 : ℝ)) (X := (8285875363701/50000000000000 : ℝ)) (Y := (41714133498717/50000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198646787/200000000 : ℝ) ^ p + (934865573/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198646787/200000000 : ℝ)) (y := (934865573/1000000000 : ℝ)) (X := (41714133498717/50000000000000 : ℝ)) (Y := (8285875363701/50000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (482024877/250000000 : ℝ)) (τ := (934865573/1000000000 : ℝ)) (σ := (198646787/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (45301139/47967445 : ℝ) ^ p + (9505798/9593489 : ℝ) ^ p := by
    exact cert_lt (x := (45301139/47967445 : ℝ)) (y := (9505798/9593489 : ℝ)) (X := (21734525369449/100000000000000 : ℝ)) (Y := (78265476045077/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (934865573/1000000000 : ℝ)) (n' := (86341401/100000000 : ℝ)) (Ab := (407710251/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (117291861/125000000 : ℝ) ^ p + (496229031/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (117291861/125000000 : ℝ)) (y := (496229031/500000000 : ℝ)) (X := (18293655490421/100000000000000 : ℝ)) (Y := (5106647650567/6250000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496229031/500000000 : ℝ) ^ p + (117291861/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496229031/500000000 : ℝ)) (y := (117291861/125000000 : ℝ)) (X := (5106647650567/6250000000000 : ℝ)) (Y := (18293655490421/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (38615859/20000000 : ℝ)) (τ := (117291861/125000000 : ℝ)) (σ := (496229031/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (819075952/867417953 : ℝ) ^ p + (859525763/867417953 : ℝ) ^ p := by
    exact cert_lt (x := (819075952/867417953 : ℝ)) (y := (859525763/867417953 : ℝ)) (X := (1352845949801/6250000000000 : ℝ)) (Y := (626835728979/800000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (117291861/125000000 : ℝ)) (n' := (867417953/1000000000 : ℝ)) (Ab := (51192247/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (938442677/1000000000 : ℝ) ^ p + (99243249/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (938442677/1000000000 : ℝ)) (y := (99243249/100000000 : ℝ)) (X := (18349820502467/100000000000000 : ℝ)) (Y := (81650196527091/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99243249/100000000 : ℝ) ^ p + (938442677/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99243249/100000000 : ℝ)) (y := (938442677/1000000000 : ℝ)) (X := (81650196527091/100000000000000 : ℝ)) (Y := (18349820502467/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1930875167/1000000000 : ℝ)) (τ := (938442677/1000000000 : ℝ)) (σ := (99243249/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (136531550/144590353 : ℝ) ^ p + (143274988/144590353 : ℝ) ^ p := by
    exact cert_lt (x := (136531550/144590353 : ℝ)) (y := (143274988/144590353 : ℝ)) (X := (10821393611069/50000000000000 : ℝ)) (Y := (78357214182539/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (938442677/1000000000 : ℝ)) (n' := (433771059/500000000 : ℝ)) (Ab := (8191893/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (187689201/200000000 : ℝ) ^ p + (992431699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187689201/200000000 : ℝ)) (y := (992431699/1000000000 : ℝ)) (X := (18351557243487/100000000000000 : ℝ)) (Y := (20412114945389/25000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992431699/1000000000 : ℝ) ^ p + (187689201/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992431699/1000000000 : ℝ)) (y := (187689201/200000000 : ℝ)) (X := (20412114945389/25000000000000 : ℝ)) (Y := (18351557243487/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (241359713/125000000 : ℝ)) (τ := (187689201/200000000 : ℝ)) (σ := (992431699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (819192799/867545951 : ℝ) ^ p + (859653761/867545951 : ℝ) ^ p := by
    exact cert_lt (x := (819192799/867545951 : ℝ)) (y := (859653761/867545951 : ℝ)) (X := (2705337794401/12500000000000 : ℝ)) (Y := (78357299004701/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (187689201/200000000 : ℝ)) (n' := (867545951/1000000000 : ℝ)) (Ab := (819192799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (234611527/250000000 : ℝ) ^ p + (39697267/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (234611527/250000000 : ℝ)) (y := (39697267/40000000 : ℝ)) (X := (1835161099731/10000000000000 : ℝ)) (Y := (3265936283477/4000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39697267/40000000 : ℝ) ^ p + (234611527/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (39697267/40000000 : ℝ)) (y := (234611527/250000000 : ℝ)) (X := (3265936283477/4000000000000 : ℝ)) (Y := (1835161099731/10000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1930877783/1000000000 : ℝ)) (τ := (234611527/250000000 : ℝ)) (σ := (39697267/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (819192907/867546070 : ℝ) ^ p + (85965388/86754607 : ℝ) ^ p := by
    exact cert_lt (x := (819192907/867546070 : ℝ)) (y := (85965388/86754607 : ℝ)) (X := (2164269927583/10000000000000 : ℝ)) (Y := (39178650819047/50000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (234611527/250000000 : ℝ)) (n' := (86754607/100000000 : ℝ)) (Ab := (819192907/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (938446111/1000000000 : ℝ) ^ p + (496215837/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (938446111/1000000000 : ℝ)) (y := (496215837/500000000 : ℝ)) (X := (9175806281479/50000000000000 : ℝ)) (Y := (20412101222829/25000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496215837/500000000 : ℝ) ^ p + (938446111/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496215837/500000000 : ℝ)) (y := (938446111/1000000000 : ℝ)) (X := (20412101222829/25000000000000 : ℝ)) (Y := (9175806281479/50000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (386175557/200000000 : ℝ)) (τ := (938446111/1000000000 : ℝ)) (σ := (496215837/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (819192910/867546073 : ℝ) ^ p + (859653883/867546073 : ℝ) ^ p := by
    exact cert_lt (x := (819192910/867546073 : ℝ)) (y := (859653883/867546073 : ℝ)) (X := (21642699393723/100000000000000 : ℝ)) (Y := (39178650852241/50000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (938446111/1000000000 : ℝ)) (n' := (867546073/1000000000 : ℝ)) (Ab := (81919291/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (386175557/200000000 : ℝ)) (τ := (938446111/1000000000 : ℝ)) (σ := (496215837/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (938446111/1000000000 : ℝ)) (n' := (867546073/1000000000 : ℝ)) (Ab := (81919291/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (386175557/200000000 : ℝ)) (τ := (938446111/1000000000 : ℝ)) (σ := (496215837/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (938446111/1000000000 : ℝ)) (n' := (867546073/1000000000 : ℝ)) (Ab := (81919291/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (386175557/200000000 : ℝ)) (τ := (938446111/1000000000 : ℝ)) (σ := (496215837/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (938446111/1000000000 : ℝ)) (n' := (867546073/1000000000 : ℝ)) (Ab := (81919291/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (386175557/200000000 : ℝ)) (τ := (938446111/1000000000 : ℝ)) (σ := (496215837/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (938446111/1000000000 : ℝ)) (n' := (867546073/1000000000 : ℝ)) (Ab := (81919291/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (386175557/200000000 : ℝ)) (τ := (938446111/1000000000 : ℝ)) (σ := (496215837/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1696761551/1844239899 : ℝ) ^ p + (612115903/614746633 : ℝ) ^ p := by
    exact cert_lt (x := (1696761551/1844239899 : ℝ)) (y := (612115903/614746633 : ℝ)) (X := (10814420745429/100000000000000 : ℝ)) (Y := (44592789733801/50000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1080820948/1155760101 : ℝ) ^ p + (127540879/128417789 : ℝ) ^ p := by
    exact cert_lt (x := (1080820948/1155760101 : ℝ)) (y := (127540879/128417789 : ℝ)) (X := (8355868853191/50000000000000 : ℝ)) (Y := (83288262872967/100000000000000 : ℝ)) 427 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496215837/500000000 : ℝ)) (U := (1155760101/1000000000 : ℝ)) (Ab := (1696761551/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (938446111/1000000000 : ℝ)) (σ := (496215837/500000000 : ℝ)) (Ab := (270205237/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab010
