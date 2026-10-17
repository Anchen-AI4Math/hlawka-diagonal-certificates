import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 93, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab093 (p : ℝ) (hpa : (509/16 : ℝ) ≤ p) (hpb : p ≤ (255/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (177541684673/14092937500000 : ℝ) (6437711/1000000000 : ℝ) (3200000676461/22548700000000 : ℝ) (591/500 : ℝ) (489244471/250000000 : ℝ) (489223569/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (46352987/40000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10947/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5653/10000 : ℝ)
      else (1039/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11513/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (177541684673/14092937500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6437711/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (189185097/200000000 : ℝ) ^ p + (198834313/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (189185097/200000000 : ℝ)) (y := (198834313/200000000 : ℝ)) (X := (8499816130941/50000000000000 : ℝ)) (Y := (16600077892623/20000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198834313/200000000 : ℝ) ^ p + (189185097/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198834313/200000000 : ℝ)) (y := (189185097/200000000 : ℝ)) (X := (16600077892623/20000000000000 : ℝ)) (Y := (8499816130941/50000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (38801941/20000000 : ℝ)) (τ := (189185097/200000000 : ℝ)) (σ := (198834313/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (138441969/145382215 : ℝ) ^ p + (865855579/872293290 : ℝ) ^ p := by
    exact cert_lt (x := (138441969/145382215 : ℝ)) (y := (865855579/872293290 : ℝ)) (X := (5257787177767/25000000000000 : ℝ)) (Y := (789688521973/1000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (189185097/200000000 : ℝ)) (n' := (87229329/100000000 : ℝ)) (Ab := (415325907/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (474489549/500000000 : ℝ) ^ p + (12418411/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (474489549/500000000 : ℝ)) (y := (12418411/12500000 : ℝ)) (X := (18838903376851/100000000000000 : ℝ)) (Y := (81161116923713/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (12418411/12500000 : ℝ) ^ p + (474489549/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (12418411/12500000 : ℝ)) (y := (474489549/500000000 : ℝ)) (X := (81161116923713/100000000000000 : ℝ)) (Y := (18838903376851/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (971225989/500000000 : ℝ)) (τ := (474489549/500000000 : ℝ)) (σ := (12418411/12500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (138976655/145959867 : ℝ) ^ p + (869321491/875759202 : ℝ) ^ p := by
    exact cert_lt (x := (138976655/145959867 : ℝ)) (y := (869321491/875759202 : ℝ)) (X := (4191409605669/20000000000000 : ℝ)) (Y := (79042952869911/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (474489549/500000000 : ℝ)) (n' := (437879601/500000000 : ℝ)) (Ab := (83385993/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (949054639/1000000000 : ℝ) ^ p + (31045453/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (949054639/1000000000 : ℝ)) (y := (31045453/31250000 : ℝ)) (X := (3777352520729/20000000000000 : ℝ)) (Y := (40556629263521/50000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31045453/31250000 : ℝ) ^ p + (949054639/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31045453/31250000 : ℝ)) (y := (949054639/1000000000 : ℝ)) (X := (40556629263521/50000000000000 : ℝ)) (Y := (3777352520729/20000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (388501827/200000000 : ℝ)) (τ := (949054639/1000000000 : ℝ)) (σ := (31045453/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (416969579/437922401 : ℝ) ^ p + (368549/371278 : ℝ) ^ p := by
    exact cert_lt (x := (416969579/437922401 : ℝ)) (y := (368549/371278 : ℝ)) (X := (4191044898247/20000000000000 : ℝ)) (Y := (7904477641233/10000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (949054639/1000000000 : ℝ)) (n' := (437922401/500000000 : ℝ)) (Ab := (416969579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (474528249/500000000 : ℝ) ^ p + (993454043/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474528249/500000000 : ℝ)) (y := (993454043/1000000000 : ℝ)) (X := (18887941862161/100000000000000 : ℝ)) (Y := (81112079593817/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993454043/1000000000 : ℝ) ^ p + (474528249/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993454043/1000000000 : ℝ)) (y := (474528249/500000000 : ℝ)) (X := (81112079593817/100000000000000 : ℝ)) (Y := (18887941862161/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1942510541/1000000000 : ℝ)) (τ := (474528249/500000000 : ℝ)) (σ := (993454043/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (208485277/218961727 : ℝ) ^ p + (869409197/875846908 : ℝ) ^ p := by
    exact cert_lt (x := (208485277/218961727 : ℝ)) (y := (869409197/875846908 : ℝ)) (X := (20955180249523/100000000000000 : ℝ)) (Y := (79044821272607/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (474528249/500000000 : ℝ)) (n' := (218961727/250000000 : ℝ)) (Ab := (208485277/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (189811309/200000000 : ℝ) ^ p + (993454031/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (189811309/200000000 : ℝ)) (y := (993454031/1000000000 : ℝ)) (X := (9443985838791/50000000000000 : ℝ)) (Y := (10139006045503/12500000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993454031/1000000000 : ℝ) ^ p + (189811309/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993454031/1000000000 : ℝ)) (y := (189811309/200000000 : ℝ)) (X := (10139006045503/12500000000000 : ℝ)) (Y := (9443985838791/50000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (121406911/62500000 : ℝ)) (τ := (189811309/200000000 : ℝ)) (σ := (993454031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (833941157/875846961 : ℝ) ^ p + (869409250/875846961 : ℝ) ^ p := by
    exact cert_lt (x := (833941157/875846961 : ℝ)) (y := (869409250/875846961 : ℝ)) (X := (10477589538401/50000000000000 : ℝ)) (Y := (79044822401567/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (189811309/200000000 : ℝ)) (n' := (875846961/1000000000 : ℝ)) (Ab := (833941157/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (474528273/500000000 : ℝ) ^ p + (993454031/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474528273/500000000 : ℝ)) (y := (993454031/1000000000 : ℝ)) (X := (9443986155977/50000000000000 : ℝ)) (Y := (10139006045503/12500000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993454031/1000000000 : ℝ) ^ p + (474528273/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993454031/1000000000 : ℝ)) (y := (474528273/500000000 : ℝ)) (X := (10139006045503/12500000000000 : ℝ)) (Y := (9443986155977/50000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1942510577/1000000000 : ℝ)) (τ := (474528273/500000000 : ℝ)) (σ := (993454031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (833941159/875846963 : ℝ) ^ p + (869409252/875846963 : ℝ) ^ p := by
    exact cert_lt (x := (833941159/875846963 : ℝ)) (y := (869409252/875846963 : ℝ)) (X := (10477589576723/50000000000000 : ℝ)) (Y := (79044822444169/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (474528273/500000000 : ℝ)) (n' := (875846963/1000000000 : ℝ)) (Ab := (833941159/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1942510577/1000000000 : ℝ)) (τ := (474528273/500000000 : ℝ)) (σ := (993454031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (474528273/500000000 : ℝ)) (n' := (875846963/1000000000 : ℝ)) (Ab := (833941159/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1942510577/1000000000 : ℝ)) (τ := (474528273/500000000 : ℝ)) (σ := (993454031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (474528273/500000000 : ℝ)) (n' := (875846963/1000000000 : ℝ)) (Ab := (833941159/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1942510577/1000000000 : ℝ)) (τ := (474528273/500000000 : ℝ)) (σ := (993454031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (474528273/500000000 : ℝ)) (n' := (875846963/1000000000 : ℝ)) (Ab := (833941159/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1942510577/1000000000 : ℝ)) (τ := (474528273/500000000 : ℝ)) (σ := (993454031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (474528273/500000000 : ℝ)) (n' := (875846963/1000000000 : ℝ)) (Ab := (833941159/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1942510577/1000000000 : ℝ)) (τ := (474528273/500000000 : ℝ)) (σ := (993454031/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1715813819/1841175325 : ℝ) ^ p + (1834737614/1841175325 : ℝ) ^ p := by
    exact cert_lt (x := (1715813819/1841175325 : ℝ)) (y := (1834737614/1841175325 : ℝ)) (X := (10564005372431/100000000000000 : ℝ)) (Y := (22358998720077/25000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1094653959/1158824675 : ℝ) ^ p + (1152386964/1158824675 : ℝ) ^ p := by
    exact cert_lt (x := (1094653959/1158824675 : ℝ)) (y := (1152386964/1158824675 : ℝ)) (X := (1016867584139/6250000000000 : ℝ)) (Y := (83730119534293/100000000000000 : ℝ)) 255 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993454031/1000000000 : ℝ)) (U := (46352987/40000000 : ℝ)) (Ab := (1715813819/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (474528273/500000000 : ℝ)) (σ := (993454031/1000000000 : ℝ)) (Ab := (1094653959/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab093
