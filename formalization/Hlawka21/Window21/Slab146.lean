import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 146, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab146 (p : ℝ) (hpa : (409/16 : ℝ) ≤ p) (hpb : p ≤ (819/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (259760512969/13957125000000 : ℝ) (9561443/1000000000 : ℝ) (2000000334971/11165700000000 : ℝ) (3033/2500 : ℝ) (486640387/250000000 : ℝ) (19464971/20000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194227119/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11183/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4683/10000 : ℝ)
      else (979/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11861/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (259760512969/13957125000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9561443/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (462817957/500000000 : ℝ) ^ p + (248549351/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (462817957/500000000 : ℝ)) (y := (248549351/250000000 : ℝ)) (X := (13838173813581/100000000000000 : ℝ)) (Y := (43080922584053/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248549351/250000000 : ℝ) ^ p + (462817957/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248549351/250000000 : ℝ)) (y := (462817957/500000000 : ℝ)) (X := (43080922584053/50000000000000 : ℝ)) (Y := (13838173813581/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (959916659/500000000 : ℝ)) (τ := (462817957/500000000 : ℝ)) (σ := (248549351/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (791214137/834554289 : ℝ) ^ p + (824992846/834554289 : ℝ) ^ p := by
    exact cert_lt (x := (791214137/834554289 : ℝ)) (y := (824992846/834554289 : ℝ)) (X := (12770401421363/50000000000000 : ℝ)) (Y := (37229599388819/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462817957/500000000 : ℝ)) (n' := (834554289/1000000000 : ℝ)) (Ab := (791214137/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931007021/1000000000 : ℝ) ^ p + (993189169/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931007021/1000000000 : ℝ)) (y := (993189169/1000000000 : ℝ)) (X := (4011711836071/25000000000000 : ℝ)) (Y := (16790634226977/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993189169/1000000000 : ℝ) ^ p + (931007021/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993189169/1000000000 : ℝ)) (y := (931007021/1000000000 : ℝ)) (X := (16790634226977/20000000000000 : ℝ)) (Y := (4011711836071/25000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (192419619/100000000 : ℝ)) (τ := (931007021/1000000000 : ℝ)) (σ := (993189169/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (796981990/840851757 : ℝ) ^ p + (831290314/840851757 : ℝ) ^ p := by
    exact cert_lt (x := (796981990/840851757 : ℝ)) (y := (831290314/840851757 : ℝ)) (X := (25375211569649/100000000000000 : ℝ)) (Y := (14924957876669/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931007021/1000000000 : ℝ)) (n' := (840851757/1000000000 : ℝ)) (Ab := (79698199/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (931216999/1000000000 : ℝ) ^ p + (993146211/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931216999/1000000000 : ℝ)) (y := (993146211/1000000000 : ℝ)) (X := (16139733166597/100000000000000 : ℝ)) (Y := (83860284733917/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993146211/1000000000 : ℝ) ^ p + (931216999/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993146211/1000000000 : ℝ)) (y := (931216999/1000000000 : ℝ)) (X := (83860284733917/100000000000000 : ℝ)) (Y := (16139733166597/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192436321/100000000 : ℝ)) (τ := (931216999/1000000000 : ℝ)) (σ := (993146211/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797206779/841097224 : ℝ) ^ p + (831535781/841097224 : ℝ) ^ p := by
    exact cert_lt (x := (797206779/841097224 : ℝ)) (y := (831535781/841097224 : ℝ)) (X := (25368800076523/100000000000000 : ℝ)) (Y := (37315600389687/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (931216999/1000000000 : ℝ)) (n' := (105137153/125000000 : ℝ)) (Ab := (797206779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (116403141/125000000 : ℝ) ^ p + (496572271/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (116403141/125000000 : ℝ)) (y := (496572271/500000000 : ℝ)) (X := (3228667895429/20000000000000 : ℝ)) (Y := (83856677914259/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496572271/500000000 : ℝ) ^ p + (116403141/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496572271/500000000 : ℝ)) (y := (116403141/125000000 : ℝ)) (X := (83856677914259/100000000000000 : ℝ)) (Y := (3228667895429/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (192436967/100000000 : ℝ)) (τ := (116403141/125000000 : ℝ)) (σ := (496572271/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (797215481/841106726 : ℝ) ^ p + (831545283/841106726 : ℝ) ^ p := by
    exact cert_lt (x := (797215481/841106726 : ℝ)) (y := (831545283/841106726 : ℝ)) (X := (25368552355707/100000000000000 : ℝ)) (Y := (74631448899199/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (116403141/125000000 : ℝ)) (n' := (420553363/500000000 : ℝ)) (Ab := (797215481/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465612721/500000000 : ℝ) ^ p + (496572239/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465612721/500000000 : ℝ)) (y := (496572239/500000000 : ℝ)) (X := (16143478794129/100000000000000 : ℝ)) (Y := (83856539608983/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496572239/500000000 : ℝ) ^ p + (465612721/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496572239/500000000 : ℝ)) (y := (465612721/500000000 : ℝ)) (X := (83856539608983/100000000000000 : ℝ)) (Y := (16143478794129/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (751707/390625 : ℝ)) (τ := (465612721/500000000 : ℝ)) (σ := (496572239/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797215817/841107093 : ℝ) ^ p + (831545650/841107093 : ℝ) ^ p := by
    exact cert_lt (x := (797215817/841107093 : ℝ)) (y := (831545650/841107093 : ℝ)) (X := (1268427135279/5000000000000 : ℝ)) (Y := (14926291696469/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465612721/500000000 : ℝ)) (n' := (841107093/1000000000 : ℝ)) (Ab := (797215817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186245091/200000000 : ℝ) ^ p + (39725779/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (186245091/200000000 : ℝ)) (y := (39725779/40000000 : ℝ)) (X := (3228696912411/20000000000000 : ℝ)) (Y := (83856533125929/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (39725779/40000000 : ℝ) ^ p + (186245091/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (39725779/40000000 : ℝ)) (y := (186245091/200000000 : ℝ)) (X := (83856533125929/100000000000000 : ℝ)) (Y := (3228696912411/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797215831/841107108 : ℝ) ^ p + (831545665/841107108 : ℝ) ^ p := by
    exact cert_lt (x := (797215831/841107108 : ℝ)) (y := (831545665/841107108 : ℝ)) (X := (12684271264319/50000000000000 : ℝ)) (Y := (74631458874027/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1665917969/1805772881 : ℝ) ^ p + (1796211438/1805772881 : ℝ) ^ p := by
    exact cert_lt (x := (1665917969/1805772881 : ℝ)) (y := (1796211438/1805772881 : ℝ)) (X := (3176254272729/25000000000000 : ℝ)) (Y := (43647491577929/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1118255634/1194227119 : ℝ) ^ p + (1184665676/1194227119 : ℝ) ^ p := by
    exact cert_lt (x := (1118255634/1194227119 : ℝ)) (y := (1184665676/1194227119 : ℝ)) (X := (18595379946951/100000000000000 : ℝ)) (Y := (16280924152189/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (39725779/40000000 : ℝ)) (U := (1194227119/1000000000 : ℝ)) (Ab := (1665917969/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ)) (Ab := (559127817/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab146
