import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 96, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab096 (p : ℝ) (hpa : (24 : ℝ) ≤ p) (hpb : p ≤ (769/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (8178993779/409500000000 : ℝ) (1027919/100000000 : ℝ) (15625002457/81900000000 : ℝ) (3033/2500 : ℝ) (97156843/50000000 : ℝ) (971531941/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298398291/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5567/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2301/5000 : ℝ)
      else (7751/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11851/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (8178993779/409500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1027919/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (460275517/500000000 : ℝ) ^ p + (496949029/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460275517/500000000 : ℝ)) (y := (496949029/500000000 : ℝ)) (X := (427440236423/3125000000000 : ℝ)) (Y := (86321929869257/100000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496949029/500000000 : ℝ) ^ p + (460275517/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496949029/500000000 : ℝ)) (y := (460275517/500000000 : ℝ)) (X := (86321929869257/100000000000000 : ℝ)) (Y := (427440236423/3125000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (478612273/250000000 : ℝ)) (τ := (460275517/500000000 : ℝ)) (σ := (496949029/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (196124860/207471789 : ℝ) ^ p + (409803983/414943578 : ℝ) ^ p := by
    exact cert_lt (x := (196124860/207471789 : ℝ)) (y := (409803983/414943578 : ℝ)) (X := (6470576226521/25000000000000 : ℝ)) (Y := (74117696061111/100000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (460275517/500000000 : ℝ)) (n' := (207471789/250000000 : ℝ)) (Ab := (9806243/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (463068143/500000000 : ℝ) ^ p + (6205377/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (463068143/500000000 : ℝ)) (y := (6205377/6250000 : ℝ)) (X := (3954542102879/25000000000000 : ℝ)) (Y := (42090924295593/50000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (6205377/6250000 : ℝ) ^ p + (463068143/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (6205377/6250000 : ℝ)) (y := (463068143/500000000 : ℝ)) (X := (42090924295593/50000000000000 : ℝ)) (Y := (3954542102879/25000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (959498303/500000000 : ℝ)) (τ := (463068143/500000000 : ℝ)) (σ := (6205377/6250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (790510513/836483974 : ℝ) ^ p + (413102392/418241987 : ℝ) ^ p := by
    exact cert_lt (x := (790510513/836483974 : ℝ)) (y := (413102392/418241987 : ℝ)) (X := (25705935710783/100000000000000 : ℝ)) (Y := (2971762608159/4000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (463068143/500000000 : ℝ)) (n' := (418241987/500000000 : ℝ)) (Ab := (790510513/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (46318709/50000000 : ℝ) ^ p + (992812229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46318709/50000000 : ℝ)) (y := (992812229/1000000000 : ℝ)) (X := (7958050395319/50000000000000 : ℝ)) (Y := (10510489471657/12500000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992812229/1000000000 : ℝ) ^ p + (46318709/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992812229/1000000000 : ℝ)) (y := (46318709/50000000 : ℝ)) (X := (10510489471657/12500000000000 : ℝ)) (Y := (7958050395319/50000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1919186409/1000000000 : ℝ)) (τ := (46318709/50000000 : ℝ)) (σ := (992812229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (98845714/104595511 : ℝ) ^ p + (413242449/418382044 : ℝ) ^ p := by
    exact cert_lt (x := (98845714/104595511 : ℝ)) (y := (413242449/418382044 : ℝ)) (X := (25698499942167/100000000000000 : ℝ)) (Y := (18575375364787/25000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (46318709/50000000 : ℝ)) (n' := (104595511/125000000 : ℝ)) (Ab := (49422857/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (57899013/62500000 : ℝ) ^ p + (198562039/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (57899013/62500000 : ℝ)) (y := (198562039/200000000 : ℝ)) (X := (1990030211713/12500000000000 : ℝ)) (Y := (42039888065199/50000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198562039/200000000 : ℝ) ^ p + (57899013/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (198562039/200000000 : ℝ)) (y := (57899013/62500000 : ℝ)) (X := (42039888065199/50000000000000 : ℝ)) (Y := (1990030211713/12500000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1919194403/1000000000 : ℝ)) (τ := (57899013/62500000 : ℝ)) (σ := (198562039/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (131796078/139462649 : ℝ) ^ p + (413248352/418387947 : ℝ) ^ p := by
    exact cert_lt (x := (131796078/139462649 : ℝ)) (y := (413248352/418387947 : ℝ)) (X := (25698186775173/100000000000000 : ℝ)) (Y := (74301814782251/100000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (57899013/62500000 : ℝ)) (n' := (418387947/500000000 : ℝ)) (Ab := (197694117/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (92638463/100000000 : ℝ) ^ p + (992810109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92638463/100000000 : ℝ)) (y := (992810109/1000000000 : ℝ)) (X := (124378249801/781250000000 : ℝ)) (Y := (42039800552777/50000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992810109/1000000000 : ℝ) ^ p + (92638463/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992810109/1000000000 : ℝ)) (y := (92638463/100000000 : ℝ)) (X := (42039800552777/50000000000000 : ℝ)) (Y := (124378249801/781250000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1919194739/1000000000 : ℝ)) (τ := (92638463/100000000 : ℝ)) (σ := (992810109/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (790776920/836776391 : ℝ) ^ p + (826497201/836776391 : ℝ) ^ p := by
    exact cert_lt (x := (790776920/836776391 : ℝ)) (y := (826497201/836776391 : ℝ)) (X := (1284908648443/5000000000000 : ℝ)) (Y := (37150913986061/50000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (92638463/100000000 : ℝ)) (n' := (836776391/1000000000 : ℝ)) (Ab := (19769423/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926384649/1000000000 : ℝ) ^ p + (198562021/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (926384649/1000000000 : ℝ)) (y := (198562021/200000000 : ℝ)) (X := (7960211910669/50000000000000 : ℝ)) (Y := (10509949120609/12500000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198562021/200000000 : ℝ) ^ p + (926384649/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198562021/200000000 : ℝ)) (y := (926384649/1000000000 : ℝ)) (X := (10509949120609/12500000000000 : ℝ)) (Y := (7960211910669/50000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (959597377/500000000 : ℝ)) (τ := (926384649/1000000000 : ℝ)) (σ := (198562021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (790776940/836776413 : ℝ) ^ p + (826497223/836776413 : ℝ) ^ p := by
    exact cert_lt (x := (790776940/836776413 : ℝ)) (y := (826497223/836776413 : ℝ)) (X := (25698172351431/100000000000000 : ℝ)) (Y := (3715091427799/5000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926384649/1000000000 : ℝ)) (n' := (836776413/1000000000 : ℝ)) (Ab := (39538847/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (959597377/500000000 : ℝ)) (τ := (926384649/1000000000 : ℝ)) (σ := (198562021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (926384649/1000000000 : ℝ)) (n' := (836776413/1000000000 : ℝ)) (Ab := (39538847/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (959597377/500000000 : ℝ)) (τ := (926384649/1000000000 : ℝ)) (σ := (198562021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (926384649/1000000000 : ℝ)) (n' := (836776413/1000000000 : ℝ)) (Ab := (39538847/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (959597377/500000000 : ℝ)) (τ := (926384649/1000000000 : ℝ)) (σ := (198562021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (926384649/1000000000 : ℝ)) (n' := (836776413/1000000000 : ℝ)) (Ab := (39538847/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (959597377/500000000 : ℝ)) (τ := (926384649/1000000000 : ℝ)) (σ := (198562021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (926384649/1000000000 : ℝ)) (n' := (836776413/1000000000 : ℝ)) (Ab := (39538847/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (959597377/500000000 : ℝ)) (τ := (926384649/1000000000 : ℝ)) (σ := (198562021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (138198812/150533903 : ℝ) ^ p + (47266517/47537022 : ℝ) ^ p := by
    exact cert_lt (x := (138198812/150533903 : ℝ)) (y := (47266517/47537022 : ℝ)) (X := (12815023045227/100000000000000 : ℝ)) (Y := (87184977274567/100000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1113322025/1193593164 : ℝ) ^ p + (591656987/596796582 : ℝ) ^ p := by
    exact cert_lt (x := (1113322025/1193593164 : ℝ)) (y := (591656987/596796582 : ℝ)) (X := (9383667640029/50000000000000 : ℝ)) (Y := (81232665524331/100000000000000 : ℝ)) 769 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198562021/200000000 : ℝ)) (U := (298398291/250000000 : ℝ)) (Ab := (103649109/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (926384649/1000000000 : ℝ)) (σ := (198562021/200000000 : ℝ)) (Ab := (44532881/40000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab096
