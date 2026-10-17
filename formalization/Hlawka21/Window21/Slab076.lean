import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 76, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab076 (p : ℝ) (hpa : (187/8 : ℝ) ≤ p) (hpb : p ≤ (749/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (525175186541/25525500000000 : ℝ) (5298443/500000000 : ℝ) (1000000153153/5105100000000 : ℝ) (3033/2500 : ℝ) (970820427/500000000 : ℝ) (970781991/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193338769/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11113/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2283/5000 : ℝ)
      else (1929/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5923/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (525175186541/25525500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5298443/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (918317617/1000000000 : ℝ) ^ p + (993769959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918317617/1000000000 : ℝ)) (y := (993769959/1000000000 : ℝ)) (X := (13608270636301/100000000000000 : ℝ)) (Y := (86391747409849/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993769959/1000000000 : ℝ) ^ p + (918317617/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993769959/1000000000 : ℝ)) (y := (918317617/1000000000 : ℝ)) (X := (86391747409849/100000000000000 : ℝ)) (Y := (13608270636301/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (239010947/125000000 : ℝ)) (τ := (918317617/1000000000 : ℝ)) (σ := (993769959/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (781558180/827812159 : ℝ) ^ p + (817215273/827812159 : ℝ) ^ p := by
    exact cert_lt (x := (781558180/827812159 : ℝ)) (y := (817215273/827812159 : ℝ)) (X := (13016808484659/50000000000000 : ℝ)) (Y := (36983192150249/50000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (918317617/1000000000 : ℝ)) (n' := (827812159/1000000000 : ℝ)) (Ab := (39077909/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (230997221/250000000 : ℝ) ^ p + (31022531/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (230997221/250000000 : ℝ)) (y := (31022531/31250000 : ℝ)) (X := (15717638109123/100000000000000 : ℝ)) (Y := (10535297224113/12500000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (31022531/31250000 : ℝ) ^ p + (230997221/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (31022531/31250000 : ℝ)) (y := (230997221/250000000 : ℝ)) (X := (10535297224113/12500000000000 : ℝ)) (Y := (15717638109123/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (479177469/250000000 : ℝ)) (τ := (230997221/250000000 : ℝ)) (σ := (31022531/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (22504799/23843778 : ℝ) ^ p + (411967672/417266115 : ℝ) ^ p := by
    exact cert_lt (x := (22504799/23843778 : ℝ)) (y := (411967672/417266115 : ℝ)) (X := (3231578783171/12500000000000 : ℝ)) (Y := (18536842773247/25000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (230997221/250000000 : ℝ)) (n' := (83453223/100000000 : ℝ)) (Ab := (157533593/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184847879/200000000 : ℝ) ^ p + (992670619/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184847879/200000000 : ℝ)) (y := (992670619/1000000000 : ℝ)) (X := (7908841952647/50000000000000 : ℝ)) (Y := (84182333489583/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992670619/1000000000 : ℝ) ^ p + (184847879/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992670619/1000000000 : ℝ)) (y := (184847879/200000000 : ℝ)) (X := (84182333489583/100000000000000 : ℝ)) (Y := (7908841952647/50000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958455007/500000000 : ℝ)) (τ := (184847879/200000000 : ℝ)) (σ := (992670619/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (787936950/834828137 : ℝ) ^ p + (824231251/834828137 : ℝ) ^ p := by
    exact cert_lt (x := (787936950/834828137 : ℝ)) (y := (824231251/834828137 : ℝ)) (X := (25844717620531/100000000000000 : ℝ)) (Y := (74155283216673/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184847879/200000000 : ℝ)) (n' := (834828137/1000000000 : ℝ)) (Ab := (15758739/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (924250343/1000000000 : ℝ) ^ p + (992668409/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924250343/1000000000 : ℝ)) (y := (992668409/1000000000 : ℝ)) (X := (7911035023603/50000000000000 : ℝ)) (Y := (84177946879089/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992668409/1000000000 : ℝ) ^ p + (924250343/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992668409/1000000000 : ℝ)) (y := (924250343/1000000000 : ℝ)) (X := (84177946879089/100000000000000 : ℝ)) (Y := (7911035023603/50000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (59903711/31250000 : ℝ)) (τ := (924250343/1000000000 : ℝ)) (σ := (992668409/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (787948704/834841067 : ℝ) ^ p + (824244181/834841067 : ℝ) ^ p := by
    exact cert_lt (x := (787948704/834841067 : ℝ)) (y := (824244181/834841067 : ℝ)) (X := (25844372346997/100000000000000 : ℝ)) (Y := (7415562883663/10000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (924250343/1000000000 : ℝ)) (n' := (834841067/1000000000 : ℝ)) (Ab := (24623397/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (462125411/500000000 : ℝ) ^ p + (124083539/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (462125411/500000000 : ℝ)) (y := (124083539/125000000 : ℝ)) (X := (15822261977513/100000000000000 : ℝ)) (Y := (42088877174807/50000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124083539/125000000 : ℝ) ^ p + (462125411/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124083539/125000000 : ℝ)) (y := (462125411/500000000 : ℝ)) (X := (42088877174807/50000000000000 : ℝ)) (Y := (15822261977513/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (958459567/500000000 : ℝ)) (τ := (462125411/500000000 : ℝ)) (σ := (124083539/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (787949218/834841633 : ℝ) ^ p + (824244747/834841633 : ℝ) ^ p := by
    exact cert_lt (x := (787949218/834841633 : ℝ)) (y := (824244747/834841633 : ℝ)) (X := (25844356832857/100000000000000 : ℝ)) (Y := (74155643965647/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (462125411/500000000 : ℝ)) (n' := (834841633/1000000000 : ℝ)) (Ab := (393974609/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924250843/1000000000 : ℝ) ^ p + (248167077/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (924250843/1000000000 : ℝ)) (y := (248167077/250000000 : ℝ)) (X := (3164454078409/20000000000000 : ℝ)) (Y := (10522218301283/12500000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248167077/250000000 : ℝ) ^ p + (924250843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248167077/250000000 : ℝ)) (y := (924250843/1000000000 : ℝ)) (X := (10522218301283/12500000000000 : ℝ)) (Y := (3164454078409/20000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1916919151/1000000000 : ℝ)) (τ := (924250843/1000000000 : ℝ)) (σ := (248167077/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (60611480/64218589 : ℝ) ^ p + (824244771/834841657 : ℝ) ^ p := by
    exact cert_lt (x := (60611480/64218589 : ℝ)) (y := (824244771/834841657 : ℝ)) (X := (5168871266471/20000000000000 : ℝ)) (Y := (74155644607159/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924250843/1000000000 : ℝ)) (n' := (834841657/1000000000 : ℝ)) (Ab := (19698731/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1916919151/1000000000 : ℝ)) (τ := (924250843/1000000000 : ℝ)) (σ := (248167077/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (924250843/1000000000 : ℝ)) (n' := (834841657/1000000000 : ℝ)) (Ab := (19698731/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1916919151/1000000000 : ℝ)) (τ := (924250843/1000000000 : ℝ)) (σ := (248167077/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (924250843/1000000000 : ℝ)) (n' := (834841657/1000000000 : ℝ)) (Ab := (19698731/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1916919151/1000000000 : ℝ)) (τ := (924250843/1000000000 : ℝ)) (σ := (248167077/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (924250843/1000000000 : ℝ)) (n' := (834841657/1000000000 : ℝ)) (Ab := (19698731/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1916919151/1000000000 : ℝ)) (τ := (924250843/1000000000 : ℝ)) (σ := (248167077/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (924250843/1000000000 : ℝ)) (n' := (834841657/1000000000 : ℝ)) (Ab := (19698731/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1916919151/1000000000 : ℝ)) (τ := (924250843/1000000000 : ℝ)) (σ := (248167077/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1655103203/1806661231 : ℝ) ^ p + (1796064345/1806661231 : ℝ) ^ p := by
    exact cert_lt (x := (1655103203/1806661231 : ℝ)) (y := (1796064345/1806661231 : ℝ)) (X := (3215834342157/25000000000000 : ℝ)) (Y := (17427332568219/20000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1111206787/1193338769 : ℝ) ^ p + (1182741883/1193338769 : ℝ) ^ p := by
    exact cert_lt (x := (1111206787/1193338769 : ℝ)) (y := (1182741883/1193338769 : ℝ)) (X := (3768469486943/20000000000000 : ℝ)) (Y := (81157653013323/100000000000000 : ℝ)) 749 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248167077/250000000 : ℝ)) (U := (1193338769/1000000000 : ℝ)) (Ab := (1655103203/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (924250843/1000000000 : ℝ)) (σ := (248167077/250000000 : ℝ)) (Ab := (1111206787/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab076
