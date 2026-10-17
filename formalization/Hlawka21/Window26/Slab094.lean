import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 94, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab094 (p : ℝ) (hpa : (255/8 : ℝ) ≤ p) (hpb : p ≤ (511/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (142002338713/11296500000000 : ℝ) (6423411/1000000000 : ℝ) (320000067779/2259300000000 : ℝ) (591/500 : ℝ) (978530583/500000000 : ℝ) (978488941/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158857893/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2737/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(1131/2000 : ℝ)
      else (8313/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11513/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (142002338713/11296500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6423411/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (946035937/1000000000 : ℝ) ^ p + (198836263/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (946035937/1000000000 : ℝ)) (y := (198836263/200000000 : ℝ)) (X := (4250989936549/25000000000000 : ℝ)) (Y := (16599212581931/20000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198836263/200000000 : ℝ) ^ p + (946035937/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198836263/200000000 : ℝ)) (y := (946035937/1000000000 : ℝ)) (X := (16599212581931/20000000000000 : ℝ)) (Y := (4250989936549/25000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (485054313/250000000 : ℝ)) (τ := (946035937/1000000000 : ℝ)) (σ := (198836263/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (415402527/436189862 : ℝ) ^ p + (865956313/872379724 : ℝ) ^ p := by
    exact cert_lt (x := (415402527/436189862 : ℝ)) (y := (865956313/872379724 : ℝ)) (X := (10512101399321/50000000000000 : ℝ)) (Y := (39487899240193/50000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (946035937/1000000000 : ℝ)) (n' := (218094931/250000000 : ℝ)) (Ab := (415402527/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (189816991/200000000 : ℝ) ^ p + (496741761/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (189816991/200000000 : ℝ)) (y := (496741761/500000000 : ℝ)) (X := (2355544384629/12500000000000 : ℝ)) (Y := (10144458167747/12500000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496741761/500000000 : ℝ) ^ p + (189816991/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496741761/500000000 : ℝ)) (y := (189816991/200000000 : ℝ)) (X := (10144458167747/12500000000000 : ℝ)) (Y := (2355544384629/12500000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1942568477/1000000000 : ℝ)) (τ := (189816991/200000000 : ℝ)) (σ := (496741761/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (208502065/218959961 : ℝ) ^ p + (869416433/875839844 : ℝ) ^ p := by
    exact cert_lt (x := (208502065/218959961 : ℝ)) (y := (869416433/875839844 : ℝ)) (X := (20950254810493/100000000000000 : ℝ)) (Y := (988121834373/1250000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (189816991/200000000 : ℝ)) (n' := (218959961/250000000 : ℝ)) (Ab := (41700413/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (949160197/1000000000 : ℝ) ^ p + (496732603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (949160197/1000000000 : ℝ)) (y := (496732603/500000000 : ℝ)) (X := (18892126714221/100000000000000 : ℝ)) (Y := (81107894171987/100000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496732603/500000000 : ℝ) ^ p + (949160197/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496732603/500000000 : ℝ)) (y := (949160197/1000000000 : ℝ)) (X := (81107894171987/100000000000000 : ℝ)) (Y := (18892126714221/100000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1942625403/1000000000 : ℝ)) (τ := (949160197/1000000000 : ℝ)) (σ := (496732603/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (834087172/875925091 : ℝ) ^ p + (869501680/875925091 : ℝ) ^ p := by
    exact cert_lt (x := (834087172/875925091 : ℝ)) (y := (869501680/875925091 : ℝ)) (X := (20948439160293/100000000000000 : ℝ)) (Y := (19762890520639/25000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (949160197/1000000000 : ℝ)) (n' := (875925091/1000000000 : ℝ)) (Ab := (208521793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (189832409/200000000 : ℝ) ^ p + (198692951/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (189832409/200000000 : ℝ)) (y := (198692951/200000000 : ℝ)) (X := (3778660299251/20000000000000 : ℝ)) (Y := (8110671823277/10000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198692951/200000000 : ℝ) ^ p + (189832409/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198692951/200000000 : ℝ)) (y := (189832409/200000000 : ℝ)) (X := (8110671823277/10000000000000 : ℝ)) (Y := (3778660299251/20000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (4856567/2500000 : ℝ)) (τ := (189832409/200000000 : ℝ)) (σ := (198692951/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (166817822/175185437 : ℝ) ^ p + (869503774/875927185 : ℝ) ^ p := by
    exact cert_lt (x := (166817822/175185437 : ℝ)) (y := (869503774/875927185 : ℝ)) (X := (10474197128139/50000000000000 : ℝ)) (Y := (15810321334059/20000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (189832409/200000000 : ℝ)) (n' := (175185437/200000000 : ℝ)) (Ab := (83408911/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (949162091/1000000000 : ℝ) ^ p + (124183093/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (949162091/1000000000 : ℝ)) (y := (124183093/125000000 : ℝ)) (X := (1180833171223/6250000000000 : ℝ)) (Y := (20276672387883/25000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124183093/125000000 : ℝ) ^ p + (949162091/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124183093/125000000 : ℝ)) (y := (949162091/1000000000 : ℝ)) (X := (20276672387883/25000000000000 : ℝ)) (Y := (1180833171223/6250000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (388525367/200000000 : ℝ)) (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (834089158/875927237 : ℝ) ^ p + (869503826/875927237 : ℝ) ^ p := by
    exact cert_lt (x := (834089158/875927237 : ℝ)) (y := (869503826/875927237 : ℝ)) (X := (1047419652003/5000000000000 : ℝ)) (Y := (39525803888767/50000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (949162091/1000000000 : ℝ)) (n' := (875927237/1000000000 : ℝ)) (Ab := (417044579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (388525367/200000000 : ℝ)) (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (949162091/1000000000 : ℝ)) (n' := (875927237/1000000000 : ℝ)) (Ab := (417044579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (388525367/200000000 : ℝ)) (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (949162091/1000000000 : ℝ)) (n' := (875927237/1000000000 : ℝ)) (Ab := (417044579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (388525367/200000000 : ℝ)) (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (949162091/1000000000 : ℝ)) (n' := (875927237/1000000000 : ℝ)) (Ab := (417044579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (388525367/200000000 : ℝ)) (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (949162091/1000000000 : ℝ)) (n' := (875927237/1000000000 : ℝ)) (Ab := (417044579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (388525367/200000000 : ℝ)) (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (949162091/1000000000 : ℝ)) (n' := (875927237/1000000000 : ℝ)) (Ab := (417044579/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (388525367/200000000 : ℝ)) (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc15 : 1 < (1716006920/1841142107 : ℝ) ^ p + (1834718696/1841142107 : ℝ) ^ p := by
    exact cert_lt (x := (1716006920/1841142107 : ℝ)) (y := (1834718696/1841142107 : ℝ)) (X := (5280751154399/50000000000000 : ℝ)) (Y := (89438498044313/100000000000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (1094797990/1158857893 : ℝ) ^ p + (1152434482/1158857893 : ℝ) ^ p := by
    exact cert_lt (x := (1094797990/1158857893 : ℝ)) (y := (1152434482/1158857893 : ℝ)) (X := (16265423574457/100000000000000 : ℝ)) (Y := (1308352765149/1562500000000 : ℝ)) 511 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124183093/125000000 : ℝ)) (U := (1158857893/1000000000 : ℝ)) (Ab := (42900173/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc15.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (949162091/1000000000 : ℝ)) (σ := (124183093/125000000 : ℝ)) (Ab := (109479799/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc16.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab094
