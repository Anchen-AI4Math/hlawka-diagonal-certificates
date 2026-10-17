import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 142, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab142 (p : ℝ) (hpa : (407/16 : ℝ) ≤ p) (hpb : p ≤ (815/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (519818146853/27777750000000 : ℝ) (2403801/250000000 : ℝ) (2000000333333/11111100000000 : ℝ) (3033/2500 : ℝ) (973151413/500000000 : ℝ) (243279719/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597088361/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11179/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4677/10000 : ℝ)
      else (3913/5000 : ℝ) ≤ X j i ∧ X j i ≤ (593/500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (519818146853/27777750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2403801/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (115656641/125000000 : ℝ) ^ p + (248543623/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115656641/125000000 : ℝ)) (y := (248543623/250000000 : ℝ)) (X := (13826067987249/100000000000000 : ℝ)) (Y := (21543487605227/25000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248543623/250000000 : ℝ) ^ p + (115656641/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248543623/250000000 : ℝ)) (y := (115656641/125000000 : ℝ)) (X := (21543487605227/25000000000000 : ℝ)) (Y := (13826067987249/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (95971381/50000000 : ℝ)) (τ := (115656641/125000000 : ℝ)) (σ := (248543623/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (263569250/278068573 : ℝ) ^ p + (274863505/278068573 : ℝ) ^ p := by
    exact cert_lt (x := (263569250/278068573 : ℝ)) (y := (274863505/278068573 : ℝ)) (X := (25566366951909/100000000000000 : ℝ)) (Y := (372168172899/500000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115656641/125000000 : ℝ)) (n' := (834205719/1000000000 : ℝ)) (Ab := (3162831/4000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (465320611/500000000 : ℝ) ^ p + (993163847/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465320611/500000000 : ℝ)) (y := (993163847/1000000000 : ℝ)) (X := (4007410562871/25000000000000 : ℝ)) (Y := (83970376228401/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993163847/1000000000 : ℝ) ^ p + (465320611/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163847/1000000000 : ℝ)) (y := (465320611/500000000 : ℝ)) (X := (83970376228401/100000000000000 : ℝ)) (Y := (4007410562871/25000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1923805069/1000000000 : ℝ)) (τ := (465320611/500000000 : ℝ)) (σ := (993163847/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (199123696/210131649 : ℝ) ^ p + (23080872/23347961 : ℝ) ^ p := by
    exact cert_lt (x := (199123696/210131649 : ℝ)) (y := (23080872/23347961 : ℝ)) (X := (12699976334479/50000000000000 : ℝ)) (Y := (74600048209883/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (465320611/500000000 : ℝ)) (n' := (210131649/250000000 : ℝ)) (Ab := (12445231/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (46542663/50000000 : ℝ) ^ p + (496560253/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (46542663/50000000 : ℝ)) (y := (496560253/500000000 : ℝ)) (X := (1007682444707/6250000000000 : ℝ)) (Y := (83877098083053/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496560253/500000000 : ℝ) ^ p + (46542663/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (496560253/500000000 : ℝ)) (y := (46542663/50000000 : ℝ)) (X := (83877098083053/100000000000000 : ℝ)) (Y := (1007682444707/6250000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (961986883/500000000 : ℝ)) (τ := (46542663/50000000 : ℝ)) (σ := (496560253/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (796721813/840774606 : ℝ) ^ p + (138526567/140129101 : ℝ) ^ p := by
    exact cert_lt (x := (796721813/840774606 : ℝ)) (y := (138526567/140129101 : ℝ)) (X := (5078693398863/20000000000000 : ℝ)) (Y := (74606533931013/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (46542663/50000000 : ℝ)) (n' := (420387303/500000000 : ℝ)) (Ab := (796721813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (930861521/1000000000 : ℝ) ^ p + (248279703/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (930861521/1000000000 : ℝ)) (y := (248279703/250000000 : ℝ)) (X := (2015820464401/12500000000000 : ℝ)) (Y := (83873454292373/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248279703/250000000 : ℝ) ^ p + (930861521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248279703/250000000 : ℝ)) (y := (930861521/1000000000 : ℝ)) (X := (83873454292373/100000000000000 : ℝ)) (Y := (2015820464401/12500000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1923980333/1000000000 : ℝ)) (τ := (930861521/1000000000 : ℝ)) (σ := (248279703/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (796730657/840784267 : ℝ) ^ p + (831169063/840784267 : ℝ) ^ p := by
    exact cert_lt (x := (796730657/840784267 : ℝ)) (y := (831169063/840784267 : ℝ)) (X := (25393214700293/100000000000000 : ℝ)) (Y := (4662924156863/6250000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (930861521/1000000000 : ℝ)) (n' := (840784267/1000000000 : ℝ)) (Ab := (796730657/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (930861843/1000000000 : ℝ) ^ p + (496559373/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (930861843/1000000000 : ℝ)) (y := (496559373/500000000 : ℝ)) (X := (8063352895829/50000000000000 : ℝ)) (Y := (4193665616479/5000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496559373/500000000 : ℝ) ^ p + (930861843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496559373/500000000 : ℝ)) (y := (930861843/1000000000 : ℝ)) (X := (4193665616479/5000000000000 : ℝ)) (Y := (8063352895829/50000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1923980589/1000000000 : ℝ)) (τ := (930861843/1000000000 : ℝ)) (σ := (496559373/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (398365501/420392322 : ℝ) ^ p + (23088040/23355129 : ℝ) ^ p := by
    exact cert_lt (x := (398365501/420392322 : ℝ)) (y := (23088040/23355129 : ℝ)) (X := (1587075297449/6250000000000 : ℝ)) (Y := (37303398183029/50000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (930861843/1000000000 : ℝ)) (n' := (210196161/250000000 : ℝ)) (Ab := (398365501/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (29089433/31250000 : ℝ) ^ p + (993118743/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (29089433/31250000 : ℝ)) (y := (993118743/1000000000 : ℝ)) (X := (16126711527689/100000000000000 : ℝ)) (Y := (83873305876731/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993118743/1000000000 : ℝ) ^ p + (29089433/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (993118743/1000000000 : ℝ)) (y := (29089433/31250000 : ℝ)) (X := (83873305876731/100000000000000 : ℝ)) (Y := (16126711527689/100000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1923980599/1000000000 : ℝ)) (τ := (29089433/31250000 : ℝ)) (σ := (993118743/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (796731016/840784659 : ℝ) ^ p + (277056485/280261553 : ℝ) ^ p := by
    exact cert_lt (x := (796731016/840784659 : ℝ)) (y := (277056485/280261553 : ℝ)) (X := (25393204585423/100000000000000 : ℝ)) (Y := (9325849594777/12500000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (29089433/31250000 : ℝ)) (n' := (840784659/1000000000 : ℝ)) (Ab := (99591377/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1923980599/1000000000 : ℝ)) (τ := (29089433/31250000 : ℝ)) (σ := (993118743/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (29089433/31250000 : ℝ)) (n' := (840784659/1000000000 : ℝ)) (Ab := (99591377/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1923980599/1000000000 : ℝ)) (τ := (29089433/31250000 : ℝ)) (σ := (993118743/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (29089433/31250000 : ℝ)) (n' := (840784659/1000000000 : ℝ)) (Ab := (99591377/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1923980599/1000000000 : ℝ)) (τ := (29089433/31250000 : ℝ)) (σ := (993118743/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (29089433/31250000 : ℝ)) (n' := (840784659/1000000000 : ℝ)) (Ab := (99591377/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1923980599/1000000000 : ℝ)) (τ := (29089433/31250000 : ℝ)) (σ := (993118743/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (29089433/31250000 : ℝ)) (n' := (840784659/1000000000 : ℝ)) (Ab := (99591377/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1923980599/1000000000 : ℝ)) (τ := (29089433/31250000 : ℝ)) (σ := (993118743/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (832674035/902911639 : ℝ) ^ p + (898104037/902911639 : ℝ) ^ p := by
    exact cert_lt (x := (832674035/902911639 : ℝ)) (y := (898104037/902911639 : ℝ)) (X := (12713298142833/100000000000000 : ℝ)) (Y := (17457340430359/20000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1117878445/1194176722 : ℝ) ^ p + (592280759/597088361 : ℝ) ^ p := by
    exact cert_lt (x := (1117878445/1194176722 : ℝ)) (y := (592280759/597088361 : ℝ)) (X := (1163023775339/6250000000000 : ℝ)) (Y := (20347905066473/25000000000000 : ℝ)) 815 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993118743/1000000000 : ℝ)) (U := (597088361/500000000 : ℝ)) (Ab := (166534807/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (29089433/31250000 : ℝ)) (σ := (993118743/1000000000 : ℝ)) (Ab := (223575689/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab142
