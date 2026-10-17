import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 56, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab056 (p : ℝ) (hpa : (59/2 : ℝ) ≤ p) (hpb : p ≤ (473/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (35818307047/2613700000000 : ℝ) (7014937/1000000000 : ℝ) (400000078411/2613700000000 : ℝ) (591/500 : ℝ) (976825903/500000000 : ℝ) (976777379/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578767831/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1089/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(5587/10000 : ℝ)
      else (2061/2500 : ℝ) ≤ X j i ∧ X j i ≤ (2299/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (35818307047/2613700000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7014937/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (941495731/1000000000 : ℝ) ^ p + (15527921/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (941495731/1000000000 : ℝ)) (y := (15527921/15625000 : ℝ)) (X := (8413469571157/50000000000000 : ℝ)) (Y := (41586540789249/50000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (15527921/15625000 : ℝ) ^ p + (941495731/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (15527921/15625000 : ℝ)) (y := (941495731/1000000000 : ℝ)) (X := (41586540789249/50000000000000 : ℝ)) (Y := (8413469571157/50000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (77411307/40000000 : ℝ)) (τ := (941495731/1000000000 : ℝ)) (σ := (15527921/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (824524922/868790009 : ℝ) ^ p + (861775072/868790009 : ℝ) ^ p := by
    exact cert_lt (x := (824524922/868790009 : ℝ)) (y := (861775072/868790009 : ℝ)) (X := (532776622401/2500000000000 : ℝ)) (Y := (39344468021811/50000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (941495731/1000000000 : ℝ)) (n' := (868790009/1000000000 : ℝ)) (Ab := (412262461/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (944726589/1000000000 : ℝ) ^ p + (198610887/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (944726589/1000000000 : ℝ)) (y := (198610887/200000000 : ℝ)) (X := (3724068989947/20000000000000 : ℝ)) (Y := (20344918592937/25000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198610887/200000000 : ℝ) ^ p + (944726589/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198610887/200000000 : ℝ)) (y := (944726589/1000000000 : ℝ)) (X := (20344918592937/25000000000000 : ℝ)) (Y := (3724068989947/20000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60555657/31250000 : ℝ)) (τ := (944726589/1000000000 : ℝ)) (σ := (198610887/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (827922946/872481673 : ℝ) ^ p + (865466736/872481673 : ℝ) ^ p := by
    exact cert_lt (x := (827922946/872481673 : ℝ)) (y := (865466736/872481673 : ℝ)) (X := (663465744097/3125000000000 : ℝ)) (Y := (19692274309043/25000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (944726589/1000000000 : ℝ)) (n' := (872481673/1000000000 : ℝ)) (Ab := (413961473/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (59050907/62500000 : ℝ) ^ p + (496516627/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (59050907/62500000 : ℝ)) (y := (496516627/500000000 : ℝ)) (X := (2333955400371/12500000000000 : ℝ)) (Y := (2541511769759/3125000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496516627/500000000 : ℝ) ^ p + (59050907/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (496516627/500000000 : ℝ)) (y := (59050907/62500000 : ℝ)) (X := (2541511769759/3125000000000 : ℝ)) (Y := (2333955400371/12500000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (968923883/500000000 : ℝ)) (τ := (59050907/62500000 : ℝ)) (σ := (496516627/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (828015250/872581961 : ℝ) ^ p + (865567024/872581961 : ℝ) ^ p := by
    exact cert_lt (x := (828015250/872581961 : ℝ)) (y := (865567024/872581961 : ℝ)) (X := (5307183598197/25000000000000 : ℝ)) (Y := (78771266532787/100000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (59050907/62500000 : ℝ)) (n' := (872581961/1000000000 : ℝ)) (Ab := (3312061/4000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (944816891/1000000000 : ℝ) ^ p + (24825817/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (944816891/1000000000 : ℝ)) (y := (24825817/25000000 : ℝ)) (X := (18673033114639/100000000000000 : ℝ)) (Y := (40663493455393/50000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (24825817/25000000 : ℝ) ^ p + (944816891/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24825817/25000000 : ℝ)) (y := (944816891/1000000000 : ℝ)) (X := (40663493455393/50000000000000 : ℝ)) (Y := (18673033114639/100000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1937849571/1000000000 : ℝ)) (τ := (944816891/1000000000 : ℝ)) (σ := (24825817/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (828017747/872584674 : ℝ) ^ p + (865569737/872584674 : ℝ) ^ p := by
    exact cert_lt (x := (828017747/872584674 : ℝ)) (y := (865569737/872584674 : ℝ)) (X := (21228675703179/100000000000000 : ℝ)) (Y := (19692831302667/25000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (944816891/1000000000 : ℝ)) (n' := (436292337/500000000 : ℝ)) (Ab := (828017747/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (236204239/250000000 : ℝ) ^ p + (124129083/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (236204239/250000000 : ℝ)) (y := (124129083/125000000 : ℝ)) (X := (18673071091771/100000000000000 : ℝ)) (Y := (81326948173233/100000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124129083/125000000 : ℝ) ^ p + (236204239/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124129083/125000000 : ℝ)) (y := (236204239/250000000 : ℝ)) (X := (81326948173233/100000000000000 : ℝ)) (Y := (18673071091771/100000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (96892481/50000000 : ℝ)) (τ := (236204239/250000000 : ℝ)) (σ := (124129083/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (828017816/872584749 : ℝ) ^ p + (865569812/872584749 : ℝ) ^ p := by
    exact cert_lt (x := (828017816/872584749 : ℝ)) (y := (865569812/872584749 : ℝ)) (X := (1061433702947/5000000000000 : ℝ)) (Y := (15754265366559/20000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (236204239/250000000 : ℝ)) (n' := (872584749/1000000000 : ℝ)) (Ab := (103502227/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (944816959/1000000000 : ℝ) ^ p + (993032663/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944816959/1000000000 : ℝ)) (y := (993032663/1000000000 : ℝ)) (X := (18673072844563/100000000000000 : ℝ)) (Y := (81326945752137/100000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993032663/1000000000 : ℝ) ^ p + (944816959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993032663/1000000000 : ℝ)) (y := (944816959/1000000000 : ℝ)) (X := (81326945752137/100000000000000 : ℝ)) (Y := (18673072844563/100000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (968924811/500000000 : ℝ)) (τ := (944816959/1000000000 : ℝ)) (σ := (993032663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (828017819/872584752 : ℝ) ^ p + (865569815/872584752 : ℝ) ^ p := by
    exact cert_lt (x := (828017819/872584752 : ℝ)) (y := (865569815/872584752 : ℝ)) (X := (663396067971/3125000000000 : ℝ)) (Y := (984641586221/1250000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (944816959/1000000000 : ℝ)) (n' := (54536547/62500000 : ℝ)) (Ab := (828017819/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (968924811/500000000 : ℝ)) (τ := (944816959/1000000000 : ℝ)) (σ := (993032663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (944816959/1000000000 : ℝ)) (n' := (54536547/62500000 : ℝ)) (Ab := (828017819/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (968924811/500000000 : ℝ)) (τ := (944816959/1000000000 : ℝ)) (σ := (993032663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (944816959/1000000000 : ℝ)) (n' := (54536547/62500000 : ℝ)) (Ab := (828017819/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (968924811/500000000 : ℝ)) (τ := (944816959/1000000000 : ℝ)) (σ := (993032663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (944816959/1000000000 : ℝ)) (n' := (54536547/62500000 : ℝ)) (Ab := (828017819/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (968924811/500000000 : ℝ)) (τ := (944816959/1000000000 : ℝ)) (σ := (993032663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (944816959/1000000000 : ℝ)) (n' := (54536547/62500000 : ℝ)) (Ab := (828017819/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (968924811/500000000 : ℝ)) (τ := (944816959/1000000000 : ℝ)) (σ := (993032663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (854058163/921232169 : ℝ) ^ p + (1835449401/1842464338 : ℝ) ^ p := by
    exact cert_lt (x := (854058163/921232169 : ℝ)) (y := (1835449401/1842464338 : ℝ)) (X := (533219860363/5000000000000 : ℝ)) (Y := (89335603049107/100000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1088975483/1157535662 : ℝ) ^ p + (1150520725/1157535662 : ℝ) ^ p := by
    exact cert_lt (x := (1088975483/1157535662 : ℝ)) (y := (1150520725/1157535662 : ℝ)) (X := (8223989487203/50000000000000 : ℝ)) (Y := (16710404333083/20000000000000 : ℝ)) 473 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993032663/1000000000 : ℝ)) (U := (578767831/500000000 : ℝ)) (Ab := (854058163/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (944816959/1000000000 : ℝ)) (σ := (993032663/1000000000 : ℝ)) (Ab := (1088975483/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab056
