import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 59, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab059 (p : ℝ) (hpa : (475/16 : ℝ) ≤ p) (hpb : p ≤ (119/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (14316552337/1052125000000 : ℝ) (3482179/500000000 : ℝ) (128000025251/841700000000 : ℝ) (591/500 : ℝ) (976970263/500000000 : ℝ) (488461171/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157644651/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2179/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(5593/10000 : ℝ)
      else (33/40 : ℝ) ≤ X j i ∧ X j i ≤ (11497/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (14316552337/1052125000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3482179/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (941881689/1000000000 : ℝ) ^ p + (248454991/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (941881689/1000000000 : ℝ)) (y := (248454991/250000000 : ℝ)) (X := (3368383448701/20000000000000 : ℝ)) (Y := (20789525616373/25000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248454991/250000000 : ℝ) ^ p + (941881689/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248454991/250000000 : ℝ)) (y := (941881689/1000000000 : ℝ)) (X := (20789525616373/25000000000000 : ℝ)) (Y := (3368383448701/20000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1935701653/1000000000 : ℝ)) (τ := (941881689/1000000000 : ℝ)) (σ := (248454991/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (412528654/434549043 : ℝ) ^ p + (431066864/434549043 : ℝ) ^ p := by
    exact cert_lt (x := (412528654/434549043 : ℝ)) (y := (431066864/434549043 : ℝ)) (X := (21286576904671/100000000000000 : ℝ)) (Y := (78713424236983/100000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (941881689/1000000000 : ℝ)) (n' := (434549043/500000000 : ℝ)) (Ab := (206264327/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (472548829/500000000 : ℝ) ^ p + (3972361/4000000 : ℝ) ^ p := by
    exact cert_lt (x := (472548829/500000000 : ℝ)) (y := (3972361/4000000 : ℝ)) (X := (18639378918509/100000000000000 : ℝ)) (Y := (81360641246281/100000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (3972361/4000000 : ℝ) ^ p + (472548829/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (3972361/4000000 : ℝ)) (y := (472548829/500000000 : ℝ)) (X := (81360641246281/100000000000000 : ℝ)) (Y := (18639378918509/100000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (484546977/250000000 : ℝ)) (τ := (472548829/500000000 : ℝ)) (σ := (3972361/4000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (414219669/436385300 : ℝ) ^ p + (432903121/436385300 : ℝ) ^ p := by
    exact cert_lt (x := (414219669/436385300 : ℝ)) (y := (432903121/436385300 : ℝ)) (X := (21206939122647/100000000000000 : ℝ)) (Y := (78793061770821/100000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (472548829/500000000 : ℝ)) (n' := (4363853/5000000 : ℝ)) (Ab := (414219669/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (945184473/1000000000 : ℝ) ^ p + (993069317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (945184473/1000000000 : ℝ)) (y := (993069317/1000000000 : ℝ)) (X := (18690383603289/100000000000000 : ℝ)) (Y := (40654818137913/50000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993069317/1000000000 : ℝ) ^ p + (945184473/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993069317/1000000000 : ℝ)) (y := (945184473/1000000000 : ℝ)) (X := (40654818137913/50000000000000 : ℝ)) (Y := (18690383603289/100000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (193825379/100000000 : ℝ)) (τ := (945184473/1000000000 : ℝ)) (σ := (993069317/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (828530471/872869567 : ℝ) ^ p + (865905209/872869567 : ℝ) ^ p := by
    exact cert_lt (x := (828530471/872869567 : ℝ)) (y := (865905209/872869567 : ℝ)) (X := (10602400847373/50000000000000 : ℝ)) (Y := (19698799911161/25000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (945184473/1000000000 : ℝ)) (n' := (872869567/1000000000 : ℝ)) (Ab := (828530471/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (236296701/250000000 : ℝ) ^ p + (496534377/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (236296701/250000000 : ℝ)) (y := (496534377/500000000 : ℝ)) (X := (3738350989373/20000000000000 : ℝ)) (Y := (2540883278343/3125000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496534377/500000000 : ℝ) ^ p + (236296701/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496534377/500000000 : ℝ)) (y := (236296701/250000000 : ℝ)) (X := (2540883278343/3125000000000 : ℝ)) (Y := (3738350989373/20000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (969127779/500000000 : ℝ)) (τ := (236296701/250000000 : ℝ)) (σ := (496534377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (276177639/290957408 : ℝ) ^ p + (432953933/436436112 : ℝ) ^ p := by
    exact cert_lt (x := (276177639/290957408 : ℝ)) (y := (432953933/436436112 : ℝ)) (X := (5301185950959/25000000000000 : ℝ)) (Y := (1231175891171/1562500000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (236296701/250000000 : ℝ)) (n' := (27277257/31250000 : ℝ)) (Ab := (828532917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (472593433/500000000 : ℝ) ^ p + (993068739/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (472593433/500000000 : ℝ)) (y := (993068739/1000000000 : ℝ)) (X := (747671656929/4000000000000 : ℝ)) (Y := (20327057092481/25000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993068739/1000000000 : ℝ) ^ p + (472593433/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993068739/1000000000 : ℝ)) (y := (472593433/500000000 : ℝ)) (X := (20327057092481/25000000000000 : ℝ)) (Y := (747671656929/4000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (387651121/200000000 : ℝ)) (τ := (472593433/500000000 : ℝ)) (σ := (993068739/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (828532983/872872295 : ℝ) ^ p + (865907937/872872295 : ℝ) ^ p := by
    exact cert_lt (x := (828532983/872872295 : ℝ)) (y := (865907937/872872295 : ℝ)) (X := (21204742742899/100000000000000 : ℝ)) (Y := (19698814642129/25000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (472593433/500000000 : ℝ)) (n' := (174574459/200000000 : ℝ)) (Ab := (828532983/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (945186869/1000000000 : ℝ) ^ p + (496534369/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (945186869/1000000000 : ℝ)) (y := (496534369/500000000 : ℝ)) (X := (4672948297053/25000000000000 : ℝ)) (Y := (81308225934121/100000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496534369/500000000 : ℝ) ^ p + (945186869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496534369/500000000 : ℝ)) (y := (945186869/1000000000 : ℝ)) (X := (81308225934121/100000000000000 : ℝ)) (Y := (4672948297053/25000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1938255607/1000000000 : ℝ)) (τ := (945186869/1000000000 : ℝ)) (σ := (496534369/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (276177662/290957433 : ℝ) ^ p + (865907941/872872299 : ℝ) ^ p := by
    exact cert_lt (x := (276177662/290957433 : ℝ)) (y := (865907941/872872299 : ℝ)) (X := (2120474213621/10000000000000 : ℝ)) (Y := (39397629327457/50000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (945186869/1000000000 : ℝ)) (n' := (872872299/1000000000 : ℝ)) (Ab := (414266493/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1938255607/1000000000 : ℝ)) (τ := (945186869/1000000000 : ℝ)) (σ := (496534369/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (945186869/1000000000 : ℝ)) (n' := (872872299/1000000000 : ℝ)) (Ab := (414266493/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1938255607/1000000000 : ℝ)) (τ := (945186869/1000000000 : ℝ)) (σ := (496534369/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (945186869/1000000000 : ℝ)) (n' := (872872299/1000000000 : ℝ)) (Ab := (414266493/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1938255607/1000000000 : ℝ)) (τ := (945186869/1000000000 : ℝ)) (σ := (496534369/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (945186869/1000000000 : ℝ)) (n' := (872872299/1000000000 : ℝ)) (Ab := (414266493/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1938255607/1000000000 : ℝ)) (τ := (945186869/1000000000 : ℝ)) (σ := (496534369/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (945186869/1000000000 : ℝ)) (n' := (872872299/1000000000 : ℝ)) (Ab := (414266493/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1938255607/1000000000 : ℝ)) (τ := (945186869/1000000000 : ℝ)) (σ := (496534369/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1708783394/1842355349 : ℝ) ^ p + (1835390991/1842355349 : ℝ) ^ p := by
    exact cert_lt (x := (1708783394/1842355349 : ℝ)) (y := (1835390991/1842355349 : ℝ)) (X := (5327826321171/50000000000000 : ℝ)) (Y := (714754781429/800000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1089462740/1157644651 : ℝ) ^ p + (1150680293/1157644651 : ℝ) ^ p := by
    exact cert_lt (x := (1089462740/1157644651 : ℝ)) (y := (1150680293/1157644651 : ℝ)) (X := (16432517139743/100000000000000 : ℝ)) (Y := (83567483430219/100000000000000 : ℝ)) 119 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496534369/500000000 : ℝ)) (U := (1157644651/1000000000 : ℝ)) (Ab := (854391697/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (945186869/1000000000 : ℝ)) (σ := (496534369/500000000 : ℝ)) (Ab := (54473137/50000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab059
