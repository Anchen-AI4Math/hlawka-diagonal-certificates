import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 37, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab037 (p : ℝ) (hpa : (453/16 : ℝ) ≤ p) (hpb : p ≤ (227/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (35996991097/2508487500000 : ℝ) (7352867/1000000000 : ℝ) (3200000602037/20067900000000 : ℝ) (591/500 : ℝ) (975867857/500000000 : ℝ) (487907617/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578413123/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5429/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5549/10000 : ℝ)
      else (2051/2500 : ℝ) ≤ X j i ∧ X j i ≤ (2297/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (35996991097/2508487500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7352867/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (938927477/1000000000 : ℝ) ^ p + (993569553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (938927477/1000000000 : ℝ)) (y := (993569553/1000000000 : ℝ)) (X := (8363814301301/50000000000000 : ℝ)) (Y := (83272391764853/100000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993569553/1000000000 : ℝ) ^ p + (938927477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993569553/1000000000 : ℝ)) (y := (938927477/1000000000 : ℝ)) (X := (83272391764853/100000000000000 : ℝ)) (Y := (8363814301301/50000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193249703/100000000 : ℝ)) (τ := (938927477/1000000000 : ℝ)) (σ := (993569553/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (820989085/866726324 : ℝ) ^ p + (859373457/866726324 : ℝ) ^ p := by
    exact cert_lt (x := (820989085/866726324 : ℝ)) (y := (859373457/866726324 : ℝ)) (X := (21474440965919/100000000000000 : ℝ)) (Y := (7852556032429/10000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (938927477/1000000000 : ℝ)) (n' := (216681581/250000000 : ℝ)) (Ab := (164197817/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (942254621/1000000000 : ℝ) ^ p + (248204801/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (942254621/1000000000 : ℝ)) (y := (248204801/250000000 : ℝ)) (X := (231171794493/1250000000000 : ℝ)) (Y := (5094142214927/6250000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248204801/250000000 : ℝ) ^ p + (942254621/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248204801/250000000 : ℝ)) (y := (942254621/1000000000 : ℝ)) (X := (5094142214927/6250000000000 : ℝ)) (Y := (231171794493/1250000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (77402953/40000000 : ℝ)) (τ := (942254621/1000000000 : ℝ)) (σ := (248204801/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (824490746/870542753 : ℝ) ^ p + (863189886/870542753 : ℝ) ^ p := by
    exact cert_lt (x := (824490746/870542753 : ℝ)) (y := (863189886/870542753 : ℝ)) (X := (21390820788051/100000000000000 : ℝ)) (Y := (15721836126347/20000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (942254621/1000000000 : ℝ)) (n' := (870542753/1000000000 : ℝ)) (Ab := (412245373/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (471175031/500000000 : ℝ) ^ p + (992796347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471175031/500000000 : ℝ)) (y := (992796347/1000000000 : ℝ)) (X := (18546970270859/100000000000000 : ℝ)) (Y := (16290609512741/20000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992796347/1000000000 : ℝ) ^ p + (471175031/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992796347/1000000000 : ℝ)) (y := (471175031/500000000 : ℝ)) (X := (16290609512741/20000000000000 : ℝ)) (Y := (18546970270859/100000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1935146409/1000000000 : ℝ)) (τ := (471175031/500000000 : ℝ)) (σ := (992796347/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (68715917/72554336 : ℝ) ^ p + (863299165/870652032 : ℝ) ^ p := by
    exact cert_lt (x := (68715917/72554336 : ℝ)) (y := (863299165/870652032 : ℝ)) (X := (21388435951663/100000000000000 : ℝ)) (Y := (9826445683081/12500000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (471175031/500000000 : ℝ)) (n' := (6801969/7812500 : ℝ)) (Ab := (206147751/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (58897049/62500000 : ℝ) ^ p + (496397847/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (58897049/62500000 : ℝ)) (y := (496397847/500000000 : ℝ)) (X := (1854849047487/10000000000000 : ℝ)) (Y := (3258061095727/4000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496397847/500000000 : ℝ) ^ p + (58897049/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (496397847/500000000 : ℝ)) (y := (58897049/62500000 : ℝ)) (X := (3258061095727/4000000000000 : ℝ)) (Y := (1854849047487/10000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (967574239/500000000 : ℝ)) (τ := (58897049/62500000 : ℝ)) (σ := (496397847/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (274864621/290218383 : ℝ) ^ p + (863302282/870655149 : ℝ) ^ p := by
    exact cert_lt (x := (274864621/290218383 : ℝ)) (y := (863302282/870655149 : ℝ)) (X := (21388367432093/100000000000000 : ℝ)) (Y := (15722326696049/20000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (58897049/62500000 : ℝ)) (n' := (870655149/1000000000 : ℝ)) (Ab := (824593863/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (942352861/1000000000 : ℝ) ^ p + (248198919/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (942352861/1000000000 : ℝ)) (y := (248198919/250000000 : ℝ)) (X := (9274266740093/50000000000000 : ℝ)) (Y := (40725742744967/50000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248198919/250000000 : ℝ) ^ p + (942352861/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248198919/250000000 : ℝ)) (y := (942352861/1000000000 : ℝ)) (X := (40725742744967/50000000000000 : ℝ)) (Y := (9274266740093/50000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1935148537/1000000000 : ℝ)) (τ := (942352861/1000000000 : ℝ)) (σ := (248198919/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (824593944/870655237 : ℝ) ^ p + (863302370/870655237 : ℝ) ^ p := by
    exact cert_lt (x := (824593944/870655237 : ℝ)) (y := (863302370/870655237 : ℝ)) (X := (1336772856663/6250000000000 : ℝ)) (Y := (39305817700237/50000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (942352861/1000000000 : ℝ)) (n' := (870655237/1000000000 : ℝ)) (Ab := (103074243/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (942352863/1000000000 : ℝ) ^ p + (39711827/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (942352863/1000000000 : ℝ)) (y := (39711827/40000000 : ℝ)) (X := (2318566824651/12500000000000 : ℝ)) (Y := (81451483161977/100000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (39711827/40000000 : ℝ) ^ p + (942352863/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39711827/40000000 : ℝ)) (y := (942352863/1000000000 : ℝ)) (X := (81451483161977/100000000000000 : ℝ)) (Y := (2318566824651/12500000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (967574269/500000000 : ℝ)) (τ := (942352863/1000000000 : ℝ)) (σ := (39711827/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (824593946/870655239 : ℝ) ^ p + (863302372/870655239 : ℝ) ^ p := by
    exact cert_lt (x := (824593946/870655239 : ℝ)) (y := (863302372/870655239 : ℝ)) (X := (10694182892241/50000000000000 : ℝ)) (Y := (19652908861029/25000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (942352863/1000000000 : ℝ)) (n' := (870655239/1000000000 : ℝ)) (Ab := (412296973/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (967574269/500000000 : ℝ)) (τ := (942352863/1000000000 : ℝ)) (σ := (39711827/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (942352863/1000000000 : ℝ)) (n' := (870655239/1000000000 : ℝ)) (Ab := (412296973/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (967574269/500000000 : ℝ)) (τ := (942352863/1000000000 : ℝ)) (σ := (39711827/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (942352863/1000000000 : ℝ)) (n' := (870655239/1000000000 : ℝ)) (Ab := (412296973/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (967574269/500000000 : ℝ)) (τ := (942352863/1000000000 : ℝ)) (σ := (39711827/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (942352863/1000000000 : ℝ)) (n' := (870655239/1000000000 : ℝ)) (Ab := (412296973/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (967574269/500000000 : ℝ)) (τ := (942352863/1000000000 : ℝ)) (σ := (39711827/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (942352863/1000000000 : ℝ)) (n' := (870655239/1000000000 : ℝ)) (Ab := (412296973/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (967574269/500000000 : ℝ)) (τ := (942352863/1000000000 : ℝ)) (σ := (39711827/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1703694599/1843173754 : ℝ) ^ p + (1835820887/1843173754 : ℝ) ^ p := by
    exact cert_lt (x := (1703694599/1843173754 : ℝ)) (y := (1835820887/1843173754 : ℝ)) (X := (10722540191873/100000000000000 : ℝ)) (Y := (22319364996913/25000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (542884314/578413123 : ℝ) ^ p + (1149473379/1156826246 : ℝ) ^ p := by
    exact cert_lt (x := (542884314/578413123 : ℝ)) (y := (1149473379/1156826246 : ℝ)) (X := (4137636207123/25000000000000 : ℝ)) (Y := (20862363956001/25000000000000 : ℝ)) 227 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (39711827/40000000 : ℝ)) (U := (578413123/500000000 : ℝ)) (Ab := (1703694599/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (942352863/1000000000 : ℝ)) (σ := (39711827/40000000 : ℝ)) (Ab := (271442157/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab037
