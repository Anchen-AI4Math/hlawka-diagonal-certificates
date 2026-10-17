import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 24, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab024 (p : ℝ) (hpa : (55/2 : ℝ) ≤ p) (hpb : p ≤ (441/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (4516007633/304562500000 : ℝ) (1900793/250000000 : ℝ) (80000014619/487300000000 : ℝ) (591/500 : ℝ) (195033077/100000000 : ℝ) (19502193/20000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578160757/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2167/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(69/125 : ℝ)
      else (327/400 : ℝ) ≤ X j i ∧ X j i ≤ (5739/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (4516007633/304562500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1900793/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (937036741/1000000000 : ℝ) ^ p + (993412089/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937036741/1000000000 : ℝ)) (y := (993412089/1000000000 : ℝ)) (X := (8327446243759/50000000000000 : ℝ)) (Y := (41672563158969/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993412089/1000000000 : ℝ) ^ p + (937036741/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993412089/1000000000 : ℝ)) (y := (937036741/1000000000 : ℝ)) (X := (41672563158969/50000000000000 : ℝ)) (Y := (8327446243759/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193044883/100000000 : ℝ)) (τ := (937036741/1000000000 : ℝ)) (σ := (993412089/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (818393467/865191870 : ℝ) ^ p + (428794349/432595935 : ℝ) ^ p := by
    exact cert_lt (x := (818393467/865191870 : ℝ)) (y := (428794349/432595935 : ℝ)) (X := (21595239204723/100000000000000 : ℝ)) (Y := (4900297596061/6250000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (937036741/1000000000 : ℝ)) (n' := (86519187/100000000 : ℝ)) (Ab := (818393467/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940431629/1000000000 : ℝ) ^ p + (992649447/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940431629/1000000000 : ℝ)) (y := (992649447/1000000000 : ℝ)) (X := (18400587787189/100000000000000 : ℝ)) (Y := (40799715553491/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992649447/1000000000 : ℝ) ^ p + (940431629/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992649447/1000000000 : ℝ)) (y := (940431629/1000000000 : ℝ)) (X := (40799715553491/50000000000000 : ℝ)) (Y := (18400587787189/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (483270269/250000000 : ℝ)) (τ := (940431629/1000000000 : ℝ)) (σ := (992649447/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821968283/869097118 : ℝ) ^ p + (430746973/434548559 : ℝ) ^ p := by
    exact cert_lt (x := (821968283/869097118 : ℝ)) (y := (430746973/434548559 : ℝ)) (X := (10754551527619/50000000000000 : ℝ)) (Y := (78490897977533/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940431629/1000000000 : ℝ)) (n' := (434548559/500000000 : ℝ)) (Ab := (821968283/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (3762131/4000000 : ℝ) ^ p + (124078167/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (3762131/4000000 : ℝ)) (y := (124078167/125000000 : ℝ)) (X := (4613799842541/25000000000000 : ℝ)) (Y := (81544819499411/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124078167/125000000 : ℝ) ^ p + (3762131/4000000 : ℝ) ^ p := by
    exact cert_lt (x := (124078167/125000000 : ℝ)) (y := (3762131/4000000 : ℝ)) (X := (81544819499411/100000000000000 : ℝ)) (Y := (4613799842541/25000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (966579043/500000000 : ℝ)) (τ := (3762131/4000000 : ℝ)) (σ := (124078167/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822074559/869213227 : ℝ) ^ p + (861610055/869213227 : ℝ) ^ p := by
    exact cert_lt (x := (822074559/869213227 : ℝ)) (y := (861610055/869213227 : ℝ)) (X := (4301310536971/20000000000000 : ℝ)) (Y := (78493448486461/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (3762131/4000000 : ℝ)) (n' := (869213227/1000000000 : ℝ)) (Ab := (822074559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (188107149/200000000 : ℝ) ^ p + (49631231/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (188107149/200000000 : ℝ)) (y := (49631231/50000000 : ℝ)) (X := (1845681923441/10000000000000 : ℝ)) (Y := (81543198292343/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49631231/50000000 : ℝ) ^ p + (188107149/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (49631231/50000000 : ℝ)) (y := (188107149/200000000 : ℝ)) (X := (81543198292343/100000000000000 : ℝ)) (Y := (1845681923441/10000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (386632073/200000000 : ℝ)) (τ := (188107149/200000000 : ℝ)) (σ := (49631231/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822077706/869216665 : ℝ) ^ p + (861613493/869216665 : ℝ) ^ p := by
    exact cert_lt (x := (822077706/869216665 : ℝ)) (y := (861613493/869216665 : ℝ)) (X := (4301295459113/20000000000000 : ℝ)) (Y := (9811690499767/12500000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (188107149/200000000 : ℝ)) (n' := (173843333/200000000 : ℝ)) (Ab := (411038853/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (940535833/1000000000 : ℝ) ^ p + (992624599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (940535833/1000000000 : ℝ)) (y := (992624599/1000000000 : ℝ)) (X := (9228433415913/50000000000000 : ℝ)) (Y := (81543150743443/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992624599/1000000000 : ℝ) ^ p + (940535833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992624599/1000000000 : ℝ)) (y := (940535833/1000000000 : ℝ)) (X := (81543150743443/100000000000000 : ℝ)) (Y := (9228433415913/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (120822527/62500000 : ℝ)) (τ := (940535833/1000000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (411038899/434608383 : ℝ) ^ p + (430806797/434608383 : ℝ) ^ p := by
    exact cert_lt (x := (411038899/434608383 : ℝ)) (y := (430806797/434608383 : ℝ)) (X := (2688309344441/12500000000000 : ℝ)) (Y := (3139741048659/4000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (940535833/1000000000 : ℝ)) (n' := (434608383/500000000 : ℝ)) (Ab := (411038899/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (188107167/200000000 : ℝ) ^ p + (992624599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188107167/200000000 : ℝ)) (y := (992624599/1000000000 : ℝ)) (X := (18456867913587/100000000000000 : ℝ)) (Y := (81543150743443/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992624599/1000000000 : ℝ) ^ p + (188107167/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992624599/1000000000 : ℝ)) (y := (188107167/200000000 : ℝ)) (X := (81543150743443/100000000000000 : ℝ)) (Y := (18456867913587/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (822077801/869216769 : ℝ) ^ p + (861613597/869216769 : ℝ) ^ p := by
    exact cert_lt (x := (822077801/869216769 : ℝ)) (y := (861613597/869216769 : ℝ)) (X := (21506474872841/100000000000000 : ℝ)) (Y := (39246763141183/50000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (n' := (869216769/1000000000 : ℝ)) (Ab := (822077801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (966580217/500000000 : ℝ)) (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (130804483/141821422 : ℝ) ^ p + (918037657/921839243 : ℝ) ^ p := by
    exact cert_lt (x := (130804483/141821422 : ℝ)) (y := (918037657/921839243 : ℝ)) (X := (10765317859677/100000000000000 : ℝ)) (Y := (89234682356723/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083446851/1156321514 : ℝ) ^ p + (574359171/578160757 : ℝ) ^ p := by
    exact cert_lt (x := (1083446851/1156321514 : ℝ)) (y := (574359171/578160757 : ℝ)) (X := (519554056383/3125000000000 : ℝ)) (Y := (83374271038847/100000000000000 : ℝ)) 441 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992624599/1000000000 : ℝ)) (U := (578160757/500000000 : ℝ)) (Ab := (1700458279/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (188107167/200000000 : ℝ)) (σ := (992624599/1000000000 : ℝ)) (Ab := (1083446851/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab024
