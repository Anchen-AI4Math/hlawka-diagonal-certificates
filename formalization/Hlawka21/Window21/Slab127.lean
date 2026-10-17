import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 127, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab127 (p : ℝ) (hpa : (799/32 : ℝ) ≤ p) (hpb : p ≤ (25 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1041917392981/54531750000000 : ℝ) (9822231/1000000000 : ℝ) (4000000654381/21812700000000 : ℝ) (3033/2500 : ℝ) (243163737/125000000 : ℝ) (243155299/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193987109/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2233/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2327/5000 : ℝ)
      else (7803/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11857/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1041917392981/54531750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9822231/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (461890999/500000000 : ℝ) ^ p + (994087013/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461890999/500000000 : ℝ)) (y := (994087013/1000000000 : ℝ)) (X := (8612265041/62500000000 : ℝ)) (Y := (3448815755821/4000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994087013/1000000000 : ℝ) ^ p + (461890999/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (994087013/1000000000 : ℝ)) (y := (461890999/500000000 : ℝ)) (X := (3448815755821/4000000000000 : ℝ)) (Y := (8612265041/62500000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1917869011/1000000000 : ℝ)) (τ := (461890999/500000000 : ℝ)) (σ := (994087013/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (157752599/166572377 : ℝ) ^ p + (823039654/832861885 : ℝ) ^ p := by
    exact cert_lt (x := (157752599/166572377 : ℝ)) (y := (823039654/832861885 : ℝ)) (X := (12832418082873/50000000000000 : ℝ)) (Y := (74335165312339/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (461890999/500000000 : ℝ)) (n' := (166572377/200000000 : ℝ)) (Ab := (157752599/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (5807713/6250000 : ℝ) ^ p + (99306739/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (5807713/6250000 : ℝ)) (y := (99306739/100000000 : ℝ)) (X := (3990876071871/25000000000000 : ℝ)) (Y := (10504564108309/12500000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99306739/100000000 : ℝ) ^ p + (5807713/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (99306739/100000000 : ℝ)) (y := (5807713/6250000 : ℝ)) (X := (10504564108309/12500000000000 : ℝ)) (Y := (3990876071871/25000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (192230147/100000000 : ℝ)) (τ := (5807713/6250000 : ℝ)) (σ := (99306739/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (794622443/839271428 : ℝ) ^ p + (829449197/839271428 : ℝ) ^ p := by
    exact cert_lt (x := (794622443/839271428 : ℝ)) (y := (829449197/839271428 : ℝ)) (X := (2549527584837/10000000000000 : ℝ)) (Y := (74504725304517/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (5807713/6250000 : ℝ)) (n' := (209817857/250000000 : ℝ)) (Ab := (794622443/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (58090881/62500000 : ℝ) ^ p + (496511287/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (58090881/62500000 : ℝ)) (y := (496511287/500000000 : ℝ)) (X := (16058265761151/100000000000000 : ℝ)) (Y := (83941752391431/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496511287/500000000 : ℝ) ^ p + (58090881/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (496511287/500000000 : ℝ)) (y := (58090881/62500000 : ℝ)) (X := (83941752391431/100000000000000 : ℝ)) (Y := (16058265761151/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192247667/100000000 : ℝ)) (τ := (58090881/62500000 : ℝ)) (σ := (496511287/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (264952717/279843102 : ℝ) ^ p + (92189675/93281034 : ℝ) ^ p := by
    exact cert_lt (x := (264952717/279843102 : ℝ)) (y := (92189675/93281034 : ℝ)) (X := (12744250055517/50000000000000 : ℝ)) (Y := (74511500807931/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (58090881/62500000 : ℝ)) (n' := (419764653/500000000 : ℝ)) (Ab := (794858151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (464731443/500000000 : ℝ) ^ p + (993020777/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464731443/500000000 : ℝ)) (y := (993020777/1000000000 : ℝ)) (X := (16062062833449/100000000000000 : ℝ)) (Y := (83937954893333/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993020777/1000000000 : ℝ) ^ p + (464731443/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993020777/1000000000 : ℝ)) (y := (464731443/500000000 : ℝ)) (X := (83937954893333/100000000000000 : ℝ)) (Y := (16062062833449/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1922483663/1000000000 : ℝ)) (τ := (464731443/500000000 : ℝ)) (σ := (993020777/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (33119482/34980817 : ℝ) ^ p + (276572459/279846536 : ℝ) ^ p := by
    exact cert_lt (x := (33119482/34980817 : ℝ)) (y := (276572459/279846536 : ℝ)) (X := (5097646017479/20000000000000 : ℝ)) (Y := (74511771409171/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (464731443/500000000 : ℝ)) (n' := (104942451/125000000 : ℝ)) (Ab := (49679223/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (929463237/1000000000 : ℝ) ^ p + (198604141/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (929463237/1000000000 : ℝ)) (y := (198604141/200000000 : ℝ)) (X := (321244289501/2000000000000 : ℝ)) (Y := (10492225342907/12500000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198604141/200000000 : ℝ) ^ p + (929463237/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198604141/200000000 : ℝ)) (y := (929463237/1000000000 : ℝ)) (X := (10492225342907/12500000000000 : ℝ)) (Y := (321244289501/2000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961241971/500000000 : ℝ)) (τ := (929463237/1000000000 : ℝ)) (σ := (198604141/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (264955981/279846673 : ℝ) ^ p + (276572596/279846673 : ℝ) ^ p := by
    exact cert_lt (x := (264955981/279846673 : ℝ)) (y := (276572596/279846673 : ℝ)) (X := (12744109379793/50000000000000 : ℝ)) (Y := (37255891102367/50000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (929463237/1000000000 : ℝ)) (n' := (839540019/1000000000 : ℝ)) (Ab := (794867943/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232365813/250000000 : ℝ) ^ p + (496510351/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232365813/250000000 : ℝ)) (y := (496510351/500000000 : ℝ)) (X := (16062220955491/100000000000000 : ℝ)) (Y := (3357511856147/4000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496510351/500000000 : ℝ) ^ p + (232365813/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496510351/500000000 : ℝ)) (y := (232365813/250000000 : ℝ)) (X := (3357511856147/4000000000000 : ℝ)) (Y := (16062220955491/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (961241977/500000000 : ℝ)) (τ := (232365813/250000000 : ℝ)) (σ := (496510351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (794867960/839540037 : ℝ) ^ p + (276572602/279846679 : ℝ) ^ p := by
    exact cert_lt (x := (794867960/839540037 : ℝ)) (y := (276572602/279846679 : ℝ)) (X := (25488218725743/100000000000000 : ℝ)) (Y := (18627945669383/25000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232365813/250000000 : ℝ)) (n' := (839540037/1000000000 : ℝ)) (Ab := (19871699/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (961241977/500000000 : ℝ)) (τ := (232365813/250000000 : ℝ)) (σ := (496510351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (232365813/250000000 : ℝ)) (n' := (839540037/1000000000 : ℝ)) (Ab := (19871699/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (961241977/500000000 : ℝ)) (τ := (232365813/250000000 : ℝ)) (σ := (496510351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (232365813/250000000 : ℝ)) (n' := (839540037/1000000000 : ℝ)) (Ab := (19871699/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (961241977/500000000 : ℝ)) (τ := (232365813/250000000 : ℝ)) (σ := (496510351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (232365813/250000000 : ℝ)) (n' := (839540037/1000000000 : ℝ)) (Ab := (19871699/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (961241977/500000000 : ℝ)) (τ := (232365813/250000000 : ℝ)) (σ := (496510351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (232365813/250000000 : ℝ)) (n' := (839540037/1000000000 : ℝ)) (Ab := (19871699/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (961241977/500000000 : ℝ)) (τ := (232365813/250000000 : ℝ)) (σ := (496510351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (554387407/602004297 : ℝ) ^ p + (199576740/200668099 : ℝ) ^ p := by
    exact cert_lt (x := (554387407/602004297 : ℝ)) (y := (199576740/200668099 : ℝ)) (X := (2549025218691/20000000000000 : ℝ)) (Y := (87254874200249/100000000000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1116437680/1193987109 : ℝ) ^ p + (394721626/397995703 : ℝ) ^ p := by
    exact cert_lt (x := (1116437680/1193987109 : ℝ)) (y := (394721626/397995703 : ℝ)) (X := (9329131101901/50000000000000 : ℝ)) (Y := (1270964661017/1562500000000 : ℝ)) 25 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496510351/500000000 : ℝ)) (U := (1193987109/1000000000 : ℝ)) (Ab := (1663162221/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (232365813/250000000 : ℝ)) (σ := (496510351/500000000 : ℝ)) (Ab := (13955471/12500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab127
