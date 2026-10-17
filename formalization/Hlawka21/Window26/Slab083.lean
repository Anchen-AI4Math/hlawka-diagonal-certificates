import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 83, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab083 (p : ℝ) (hpa : (499/16 : ℝ) ≤ p) (hpb : p ≤ (125/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (284700947171/22105700000000 : ℝ) (329213/50000000 : ℝ) (3200000663171/22105700000000 : ℝ) (591/500 : ℝ) (489031737/250000000 : ℝ) (978019999/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (579243979/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2733/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(5637/10000 : ℝ)
      else (1659/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2877/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (284700947171/22105700000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (329213/50000000 : ℝ) := by norm_num
  have pc0 : 1 < (944795613/1000000000 : ℝ) ^ p + (497036143/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (944795613/1000000000 : ℝ)) (y := (497036143/500000000 : ℝ)) (X := (1695541313089/10000000000000 : ℝ)) (Y := (83044608574253/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497036143/500000000 : ℝ) ^ p + (944795613/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497036143/500000000 : ℝ)) (y := (944795613/1000000000 : ℝ)) (X := (83044608574253/100000000000000 : ℝ)) (Y := (1695541313089/10000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1938867899/1000000000 : ℝ)) (τ := (944795613/1000000000 : ℝ)) (σ := (497036143/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (414542801/435703257 : ℝ) ^ p + (432411127/435703257 : ℝ) ^ p := by
    exact cert_lt (x := (414542801/435703257 : ℝ)) (y := (432411127/435703257 : ℝ)) (X := (10551163474223/50000000000000 : ℝ)) (Y := (78897674430367/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (944795613/1000000000 : ℝ)) (n' := (435703257/500000000 : ℝ)) (Ab := (414542801/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (947895749/1000000000 : ℝ) ^ p + (993364609/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (947895749/1000000000 : ℝ)) (y := (993364609/1000000000 : ℝ)) (X := (234789137607/1250000000000 : ℝ)) (Y := (40608444366499/50000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993364609/1000000000 : ℝ) ^ p + (947895749/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993364609/1000000000 : ℝ)) (y := (947895749/1000000000 : ℝ)) (X := (40608444366499/50000000000000 : ℝ)) (Y := (234789137607/1250000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (970630179/500000000 : ℝ)) (τ := (947895749/1000000000 : ℝ)) (σ := (993364609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (416171733/437465615 : ℝ) ^ p + (86834697/87493123 : ℝ) ^ p := by
    exact cert_lt (x := (416171733/437465615 : ℝ)) (y := (86834697/87493123 : ℝ)) (X := (21026670060429/100000000000000 : ℝ)) (Y := (2467916590419/3125000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (947895749/1000000000 : ℝ)) (n' := (87493123/100000000 : ℝ)) (Ab := (416171733/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (118496797/125000000 : ℝ) ^ p + (993345523/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (118496797/125000000 : ℝ)) (y := (993345523/1000000000 : ℝ)) (X := (4707970237701/25000000000000 : ℝ)) (Y := (81168138532739/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993345523/1000000000 : ℝ) ^ p + (118496797/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993345523/1000000000 : ℝ)) (y := (118496797/125000000 : ℝ)) (X := (81168138532739/100000000000000 : ℝ)) (Y := (4707970237701/25000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1941319899/1000000000 : ℝ)) (τ := (118496797/125000000 : ℝ)) (σ := (993345523/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (832425951/875020477 : ℝ) ^ p + (868436217/875020477 : ℝ) ^ p := by
    exact cert_lt (x := (832425951/875020477 : ℝ)) (y := (868436217/875020477 : ℝ)) (X := (10512380797269/50000000000000 : ℝ)) (Y := (19743809884039/25000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (118496797/125000000 : ℝ)) (n' := (875020477/1000000000 : ℝ)) (Ab := (832425951/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (947976359/1000000000 : ℝ) ^ p + (993345041/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (947976359/1000000000 : ℝ)) (y := (993345041/1000000000 : ℝ)) (X := (18833112023157/100000000000000 : ℝ)) (Y := (20291726939113/25000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993345041/1000000000 : ℝ) ^ p + (947976359/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993345041/1000000000 : ℝ)) (y := (947976359/1000000000 : ℝ)) (X := (20291726939113/25000000000000 : ℝ)) (Y := (18833112023157/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (9706607/5000000 : ℝ)) (τ := (947976359/1000000000 : ℝ)) (σ := (993345041/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (104053504/109377841 : ℝ) ^ p + (217109617/218755682 : ℝ) ^ p := by
    exact cert_lt (x := (104053504/109377841 : ℝ)) (y := (217109617/218755682 : ℝ)) (X := (1314044618869/6250000000000 : ℝ)) (Y := (78975287671747/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (947976359/1000000000 : ℝ)) (n' := (109377841/125000000 : ℝ)) (Ab := (1625836/1953125 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (947976409/1000000000 : ℝ) ^ p + (993345029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (947976409/1000000000 : ℝ)) (y := (993345029/1000000000 : ℝ)) (X := (18833143064819/100000000000000 : ℝ)) (Y := (81166877114949/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993345029/1000000000 : ℝ) ^ p + (947976409/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993345029/1000000000 : ℝ)) (y := (947976409/1000000000 : ℝ)) (X := (81166877114949/100000000000000 : ℝ)) (Y := (18833143064819/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (970660719/500000000 : ℝ)) (τ := (947976409/1000000000 : ℝ)) (σ := (993345029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (832428083/875022784 : ℝ) ^ p + (217109631/218755696 : ℝ) ^ p := by
    exact cert_lt (x := (832428083/875022784 : ℝ)) (y := (217109631/218755696 : ℝ)) (X := (2628089013383/12500000000000 : ℝ)) (Y := (78975288869253/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (947976409/1000000000 : ℝ)) (n' := (13672231/15625000 : ℝ)) (Ab := (832428083/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (94797641/100000000 : ℝ) ^ p + (993345029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94797641/100000000 : ℝ)) (y := (993345029/1000000000 : ℝ)) (X := (4708285921413/25000000000000 : ℝ)) (Y := (81166877114949/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993345029/1000000000 : ℝ) ^ p + (94797641/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993345029/1000000000 : ℝ)) (y := (94797641/100000000 : ℝ)) (X := (81166877114949/100000000000000 : ℝ)) (Y := (4708285921413/25000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1941321439/1000000000 : ℝ)) (τ := (94797641/100000000 : ℝ)) (σ := (993345029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (832428084/875022785 : ℝ) ^ p + (173687705/175004557 : ℝ) ^ p := by
    exact cert_lt (x := (832428084/875022785 : ℝ)) (y := (173687705/175004557 : ℝ)) (X := (4204942429097/20000000000000 : ℝ)) (Y := (78975288890637/100000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (94797641/100000000 : ℝ)) (n' := (175004557/200000000 : ℝ)) (Ab := (208107021/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1941321439/1000000000 : ℝ)) (τ := (94797641/100000000 : ℝ)) (σ := (993345029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (94797641/100000000 : ℝ)) (n' := (175004557/200000000 : ℝ)) (Ab := (208107021/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1941321439/1000000000 : ℝ)) (τ := (94797641/100000000 : ℝ)) (σ := (993345029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (94797641/100000000 : ℝ)) (n' := (175004557/200000000 : ℝ)) (Ab := (208107021/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1941321439/1000000000 : ℝ)) (τ := (94797641/100000000 : ℝ)) (σ := (993345029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (94797641/100000000 : ℝ)) (n' := (175004557/200000000 : ℝ)) (Ab := (208107021/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1941321439/1000000000 : ℝ)) (τ := (94797641/100000000 : ℝ)) (σ := (993345029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (94797641/100000000 : ℝ)) (n' := (175004557/200000000 : ℝ)) (Ab := (208107021/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1941321439/1000000000 : ℝ)) (τ := (94797641/100000000 : ℝ)) (σ := (993345029/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (856920926/920756021 : ℝ) ^ p + (917463891/920756021 : ℝ) ^ p := by
    exact cert_lt (x := (856920926/920756021 : ℝ)) (y := (917463891/920756021 : ℝ)) (X := (661851674873/6250000000000 : ℝ)) (Y := (44705186729747/50000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1093187599/1158487958 : ℝ) ^ p + (575951849/579243979 : ℝ) ^ p := by
    exact cert_lt (x := (1093187599/1158487958 : ℝ)) (y := (575951849/579243979 : ℝ)) (X := (16315453295891/100000000000000 : ℝ)) (Y := (41842273639689/50000000000000 : ℝ)) 125 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993345029/1000000000 : ℝ)) (U := (579243979/500000000 : ℝ)) (Ab := (428460463/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (94797641/100000000 : ℝ)) (σ := (993345029/1000000000 : ℝ)) (Ab := (1093187599/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab083
