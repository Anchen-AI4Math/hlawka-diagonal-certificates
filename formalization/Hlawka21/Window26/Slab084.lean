import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 84, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab084 (p : ℝ) (hpa : (125/4 : ℝ) ≤ p) (hpb : p ≤ (501/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2846363591/221500000000 : ℝ) (1642327/250000000 : ℝ) (6400001329/44300000000 : ℝ) (591/500 : ℝ) (978106777/500000000 : ℝ) (978063473/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231704401/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5467/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2819/5000 : ℝ)
      else (1037/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11509/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2846363591/221500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1642327/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (944910717/1000000000 : ℝ) ^ p + (497041181/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (944910717/1000000000 : ℝ)) (y := (497041181/500000000 : ℝ)) (X := (84799567501/500000000000 : ℝ)) (Y := (16608021535289/20000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497041181/500000000 : ℝ) ^ p + (944910717/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497041181/500000000 : ℝ)) (y := (944910717/1000000000 : ℝ)) (X := (16608021535289/20000000000000 : ℝ)) (Y := (84799567501/500000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1938993079/1000000000 : ℝ)) (τ := (944910717/1000000000 : ℝ)) (σ := (497041181/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (829245044/871497069 : ℝ) ^ p + (864927761/871497069 : ℝ) ^ p := by
    exact cert_lt (x := (829245044/871497069 : ℝ)) (y := (864927761/871497069 : ℝ)) (X := (21095064886547/100000000000000 : ℝ)) (Y := (9863117041733/12500000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (944910717/1000000000 : ℝ)) (n' := (871497069/1000000000 : ℝ)) (Ab := (207311261/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (474003077/500000000 : ℝ) ^ p + (99337559/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (474003077/500000000 : ℝ)) (y := (99337559/100000000 : ℝ)) (X := (18788812841047/100000000000000 : ℝ)) (Y := (3248448291223/4000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99337559/100000000 : ℝ) ^ p + (474003077/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99337559/100000000 : ℝ)) (y := (474003077/500000000 : ℝ)) (X := (3248448291223/4000000000000 : ℝ)) (Y := (18788812841047/100000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (121336359/62500000 : ℝ)) (τ := (474003077/500000000 : ℝ)) (σ := (99337559/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (832497881/875015832 : ℝ) ^ p + (217111631/218753958 : ℝ) ^ p := by
    exact cert_lt (x := (832497881/875015832 : ℝ)) (y := (217111631/218753958 : ℝ)) (X := (525489165751/2500000000000 : ℝ)) (Y := (39490217290373/50000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (474003077/500000000 : ℝ)) (n' := (109376979/125000000 : ℝ)) (Ab := (832497881/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (59255279/62500000 : ℝ) ^ p + (31042393/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (59255279/62500000 : ℝ)) (y := (31042393/31250000 : ℝ)) (X := (3767494453329/20000000000000 : ℝ)) (Y := (129860076433/160000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31042393/31250000 : ℝ) ^ p + (59255279/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (31042393/31250000 : ℝ)) (y := (59255279/62500000 : ℝ)) (X := (129860076433/160000000000 : ℝ)) (Y := (3767494453329/20000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (24268013/12500000 : ℝ)) (τ := (59255279/62500000 : ℝ)) (σ := (31042393/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (277526677/291701568 : ℝ) ^ p + (217133849/218776176 : ℝ) ^ p := by
    exact cert_lt (x := (277526677/291701568 : ℝ)) (y := (217133849/218776176 : ℝ)) (X := (21017666601433/100000000000000 : ℝ)) (Y := (39491167225181/50000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (59255279/62500000 : ℝ)) (n' := (13673511/15625000 : ℝ)) (Ab := (832580031/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (474043217/500000000 : ℝ) ^ p + (993356097/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474043217/500000000 : ℝ)) (y := (993356097/1000000000 : ℝ)) (X := (235483724197/1250000000000 : ℝ)) (Y := (40580661153277/50000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993356097/1000000000 : ℝ) ^ p + (474043217/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993356097/1000000000 : ℝ)) (y := (474043217/500000000 : ℝ)) (X := (40580661153277/50000000000000 : ℝ)) (Y := (235483724197/1250000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1941442531/1000000000 : ℝ)) (τ := (474043217/500000000 : ℝ)) (σ := (993356097/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (416291049/437553470 : ℝ) ^ p + (217134408/218776735 : ℝ) ^ p := by
    exact cert_lt (x := (416291049/437553470 : ℝ)) (y := (217134408/218776735 : ℝ)) (X := (10508809451151/50000000000000 : ℝ)) (Y := (39491191123129/50000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (474043217/500000000 : ℝ)) (n' := (43755347/50000000 : ℝ)) (Ab := (416291049/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (237021621/250000000 : ℝ) ^ p + (198671217/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (237021621/250000000 : ℝ)) (y := (198671217/200000000 : ℝ)) (X := (18838729045117/100000000000000 : ℝ)) (Y := (81161291606223/100000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198671217/200000000 : ℝ) ^ p + (237021621/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198671217/200000000 : ℝ)) (y := (237021621/250000000 : ℝ)) (X := (81161291606223/100000000000000 : ℝ)) (Y := (18838729045117/100000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1941442569/1000000000 : ℝ)) (τ := (237021621/250000000 : ℝ)) (σ := (198671217/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (416291075/437553498 : ℝ) ^ p + (217134422/218776749 : ℝ) ^ p := by
    exact cert_lt (x := (416291075/437553498 : ℝ)) (y := (217134422/218776749 : ℝ)) (X := (65680055911/312500000000 : ℝ)) (Y := (7898238344329/10000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (237021621/250000000 : ℝ)) (n' := (218776749/250000000 : ℝ)) (Ab := (16651643/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (189617297/200000000 : ℝ) ^ p + (198671217/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (189617297/200000000 : ℝ)) (y := (198671217/200000000 : ℝ)) (X := (3767745933461/20000000000000 : ℝ)) (Y := (81161291606223/100000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198671217/200000000 : ℝ) ^ p + (189617297/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198671217/200000000 : ℝ)) (y := (189617297/200000000 : ℝ)) (X := (81161291606223/100000000000000 : ℝ)) (Y := (3767745933461/20000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (194144257/100000000 : ℝ)) (τ := (189617297/200000000 : ℝ)) (σ := (198671217/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (832582151/875106997 : ℝ) ^ p + (868537689/875106997 : ℝ) ^ p := by
    exact cert_lt (x := (832582151/875106997 : ℝ)) (y := (868537689/875106997 : ℝ)) (X := (21017617929931/100000000000000 : ℝ)) (Y := (39491191732333/50000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (189617297/200000000 : ℝ)) (n' := (875106997/1000000000 : ℝ)) (Ab := (832582151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (194144257/100000000 : ℝ)) (τ := (189617297/200000000 : ℝ)) (σ := (198671217/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (189617297/200000000 : ℝ)) (n' := (875106997/1000000000 : ℝ)) (Ab := (832582151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (194144257/100000000 : ℝ)) (τ := (189617297/200000000 : ℝ)) (σ := (198671217/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (189617297/200000000 : ℝ)) (n' := (875106997/1000000000 : ℝ)) (Ab := (832582151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (194144257/100000000 : ℝ)) (τ := (189617297/200000000 : ℝ)) (σ := (198671217/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (189617297/200000000 : ℝ)) (n' := (875106997/1000000000 : ℝ)) (Ab := (832582151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (194144257/100000000 : ℝ)) (τ := (189617297/200000000 : ℝ)) (σ := (198671217/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (189617297/200000000 : ℝ)) (n' := (875106997/1000000000 : ℝ)) (Ab := (832582151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (194144257/100000000 : ℝ)) (τ := (189617297/200000000 : ℝ)) (σ := (198671217/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1714042462/1841477995 : ℝ) ^ p + (1834908687/1841477995 : ℝ) ^ p := by
    exact cert_lt (x := (1714042462/1841477995 : ℝ)) (y := (1834908687/1841477995 : ℝ)) (X := (5293507546577/50000000000000 : ℝ)) (Y := (89412985247127/100000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (218667280/231704401 : ℝ) ^ p + (1151952697/1158522005 : ℝ) ^ p := by
    exact cert_lt (x := (218667280/231704401 : ℝ)) (y := (1151952697/1158522005 : ℝ)) (X := (16310812401571/100000000000000 : ℝ)) (Y := (83689188365471/100000000000000 : ℝ)) 501 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198671217/200000000 : ℝ)) (U := (231704401/200000000 : ℝ)) (Ab := (857021231/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (189617297/200000000 : ℝ)) (σ := (198671217/200000000 : ℝ)) (Ab := (2733341/2500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab084
