import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 86, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab086 (p : ℝ) (hpa : (251/8 : ℝ) ≤ p) (hpb : p ≤ (503/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (355635081103/27798250000000 : ℝ) (6539609/1000000000 : ℝ) (1600000333579/11119300000000 : ℝ) (591/500 : ℝ) (978192871/500000000 : ℝ) (244537477/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (579294931/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10937/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2821/5000 : ℝ)
      else (83/100 : ℝ) ≤ X j i ∧ X j i ≤ (1151/1000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (355635081103/27798250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6539609/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (945139487/1000000000 : ℝ) ^ p + (62131401/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (945139487/1000000000 : ℝ)) (y := (62131401/62500000 : ℝ)) (X := (530276800949/3125000000000 : ℝ)) (Y := (41515582042167/50000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (62131401/62500000 : ℝ) ^ p + (945139487/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62131401/62500000 : ℝ)) (y := (945139487/1000000000 : ℝ)) (X := (41515582042167/50000000000000 : ℝ)) (Y := (530276800949/3125000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1939241903/1000000000 : ℝ)) (τ := (945139487/1000000000 : ℝ)) (σ := (62131401/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (829562023/871676894 : ℝ) ^ p + (865137285/871676894 : ℝ) ^ p := by
    exact cert_lt (x := (829562023/871676894 : ℝ)) (y := (865137285/871676894 : ℝ)) (X := (21080649987603/100000000000000 : ℝ)) (Y := (39459675618393/50000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (945139487/1000000000 : ℝ)) (n' := (435838447/500000000 : ℝ)) (Ab := (829562023/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (948225559/1000000000 : ℝ) ^ p + (993397449/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (948225559/1000000000 : ℝ)) (y := (993397449/1000000000 : ℝ)) (X := (940005148911/5000000000000 : ℝ)) (Y := (81199916557011/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993397449/1000000000 : ℝ) ^ p + (948225559/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993397449/1000000000 : ℝ)) (y := (948225559/1000000000 : ℝ)) (X := (81199916557011/100000000000000 : ℝ)) (Y := (940005148911/5000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60675719/31250000 : ℝ)) (τ := (948225559/1000000000 : ℝ)) (σ := (993397449/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (832804841/875183801 : ℝ) ^ p + (868644192/875183801 : ℝ) ^ p := by
    exact cert_lt (x := (832804841/875183801 : ℝ)) (y := (868644192/875183801 : ℝ)) (X := (21005465967887/100000000000000 : ℝ)) (Y := (78994534894401/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (948225559/1000000000 : ℝ)) (n' := (875183801/1000000000 : ℝ)) (Ab := (832804841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (948303241/1000000000 : ℝ) ^ p + (496689289/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (948303241/1000000000 : ℝ)) (y := (496689289/500000000 : ℝ)) (X := (2356072815419/12500000000000 : ℝ)) (Y := (81151437974869/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496689289/500000000 : ℝ) ^ p + (948303241/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496689289/500000000 : ℝ)) (y := (948303241/1000000000 : ℝ)) (X := (81151437974869/100000000000000 : ℝ)) (Y := (2356072815419/12500000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1941681819/1000000000 : ℝ)) (τ := (948303241/1000000000 : ℝ)) (σ := (496689289/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (832886329/875271930 : ℝ) ^ p + (868732321/875271930 : ℝ) ^ p := by
    exact cert_lt (x := (832886329/875271930 : ℝ)) (y := (868732321/875271930 : ℝ)) (X := (21003584181429/100000000000000 : ℝ)) (Y := (39498208698887/50000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (948303241/1000000000 : ℝ)) (n' := (87527193/100000000 : ℝ)) (Ab := (832886329/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (189661037/200000000 : ℝ) ^ p + (198675621/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (189661037/200000000 : ℝ)) (y := (198675621/200000000 : ℝ)) (X := (18849797279967/100000000000000 : ℝ)) (Y := (81150223223421/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198675621/200000000 : ℝ) ^ p + (189661037/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198675621/200000000 : ℝ)) (y := (189661037/200000000 : ℝ)) (X := (81150223223421/100000000000000 : ℝ)) (Y := (18849797279967/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (194168329/100000000 : ℝ)) (τ := (189661037/200000000 : ℝ)) (σ := (198675621/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (832888367/875274135 : ℝ) ^ p + (868734526/875274135 : ℝ) ^ p := by
    exact cert_lt (x := (832888367/875274135 : ℝ)) (y := (868734526/875274135 : ℝ)) (X := (1312721027431/6250000000000 : ℝ)) (Y := (78996464493969/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (189661037/200000000 : ℝ)) (n' := (175054827/200000000 : ℝ)) (Ab := (832888367/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (474152617/500000000 : ℝ) ^ p + (993378093/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474152617/500000000 : ℝ)) (y := (993378093/1000000000 : ℝ)) (X := (4712456974953/25000000000000 : ℝ)) (Y := (81150192405431/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993378093/1000000000 : ℝ) ^ p + (474152617/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993378093/1000000000 : ℝ)) (y := (474152617/500000000 : ℝ)) (X := (81150192405431/100000000000000 : ℝ)) (Y := (4712456974953/25000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1941683327/1000000000 : ℝ)) (τ := (474152617/500000000 : ℝ)) (σ := (993378093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (75717129/79570381 : ℝ) ^ p + (868734582/875274191 : ℝ) ^ p := by
    exact cert_lt (x := (75717129/79570381 : ℝ)) (y := (868734582/875274191 : ℝ)) (X := (10501767708833/50000000000000 : ℝ)) (Y := (3949823284503/5000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (474152617/500000000 : ℝ)) (n' := (875274191/1000000000 : ℝ)) (Ab := (832888419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (189661047/200000000 : ℝ) ^ p + (993378093/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (189661047/200000000 : ℝ)) (y := (993378093/1000000000 : ℝ)) (X := (18849828524707/100000000000000 : ℝ)) (Y := (81150192405431/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993378093/1000000000 : ℝ) ^ p + (189661047/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993378093/1000000000 : ℝ)) (y := (189661047/200000000 : ℝ)) (X := (81150192405431/100000000000000 : ℝ)) (Y := (18849828524707/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (15169401/7812500 : ℝ)) (τ := (189661047/200000000 : ℝ)) (σ := (993378093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (16017085/16832196 : ℝ) ^ p + (868734583/875274192 : ℝ) ^ p := by
    exact cert_lt (x := (16017085/16832196 : ℝ)) (y := (868734583/875274192 : ℝ)) (X := (21003535456057/100000000000000 : ℝ)) (Y := (78996465711419/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (189661047/200000000 : ℝ)) (n' := (54704637/62500000 : ℝ)) (Ab := (41644421/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (15169401/7812500 : ℝ)) (τ := (189661047/200000000 : ℝ)) (σ := (993378093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (189661047/200000000 : ℝ)) (n' := (54704637/62500000 : ℝ)) (Ab := (41644421/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (15169401/7812500 : ℝ)) (τ := (189661047/200000000 : ℝ)) (σ := (993378093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (189661047/200000000 : ℝ)) (n' := (54704637/62500000 : ℝ)) (Ab := (41644421/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (15169401/7812500 : ℝ)) (τ := (189661047/200000000 : ℝ)) (σ := (993378093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (189661047/200000000 : ℝ)) (n' := (54704637/62500000 : ℝ)) (Ab := (41644421/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (15169401/7812500 : ℝ)) (τ := (189661047/200000000 : ℝ)) (σ := (993378093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (189661047/200000000 : ℝ)) (n' := (54704637/62500000 : ℝ)) (Ab := (41644421/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (15169401/7812500 : ℝ)) (τ := (189661047/200000000 : ℝ)) (σ := (993378093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (857220696/920705069 : ℝ) ^ p + (1834870529/1841410138 : ℝ) ^ p := by
    exact cert_lt (x := (857220696/920705069 : ℝ)) (y := (1834870529/1841410138 : ℝ)) (X := (10581830952133/100000000000000 : ℝ)) (Y := (17883633851671/20000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (546816287/579294931 : ℝ) ^ p + (1152050253/1158589862 : ℝ) ^ p := by
    exact cert_lt (x := (546816287/579294931 : ℝ)) (y := (1152050253/1158589862 : ℝ)) (X := (4075398868117/25000000000000 : ℝ)) (Y := (83698405240627/100000000000000 : ℝ)) 503 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993378093/1000000000 : ℝ)) (U := (579294931/500000000 : ℝ)) (Ab := (107152587/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (189661047/200000000 : ℝ)) (σ := (993378093/1000000000 : ℝ)) (Ab := (546816287/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab086
