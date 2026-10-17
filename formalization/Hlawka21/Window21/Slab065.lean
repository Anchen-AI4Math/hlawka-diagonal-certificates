import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 65, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab065 (p : ℝ) (hpa : (737/32 : ℝ) ≤ p) (hpb : p ≤ (369/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (526160356727/25150125000000 : ℝ) (5389997/500000000 : ℝ) (4000000603603/20120100000000 : ℝ) (3033/2500 : ℝ) (242598001/125000000 : ℝ) (97035243/100000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298299813/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11101/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(909/2000 : ℝ)
      else (1539/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2961/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (526160356727/25150125000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5389997/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (917035071/1000000000 : ℝ) ^ p + (993697317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917035071/1000000000 : ℝ)) (y := (993697317/1000000000 : ℝ)) (X := (6784156584661/50000000000000 : ℝ)) (Y := (17286340926151/20000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993697317/1000000000 : ℝ) ^ p + (917035071/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993697317/1000000000 : ℝ)) (y := (917035071/1000000000 : ℝ)) (X := (17286340926151/20000000000000 : ℝ)) (Y := (6784156584661/50000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (477683097/250000000 : ℝ)) (τ := (917035071/1000000000 : ℝ)) (σ := (993697317/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779871287/826613690 : ℝ) ^ p + (407916848/413306845 : ℝ) ^ p := by
    exact cert_lt (x := (779871287/826613690 : ℝ)) (y := (407916848/413306845 : ℝ)) (X := (13060439285813/50000000000000 : ℝ)) (Y := (18469780708531/25000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (917035071/1000000000 : ℝ)) (n' := (82661369/100000000 : ℝ)) (Ab := (779871287/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (230688363/250000000 : ℝ) ^ p + (62040149/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (230688363/250000000 : ℝ)) (y := (62040149/62500000 : ℝ)) (X := (15659881151373/100000000000000 : ℝ)) (Y := (42170067519671/50000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (62040149/62500000 : ℝ) ^ p + (230688363/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (62040149/62500000 : ℝ)) (y := (230688363/250000000 : ℝ)) (X := (42170067519671/50000000000000 : ℝ)) (Y := (15659881151373/100000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (478848959/250000000 : ℝ)) (τ := (230688363/250000000 : ℝ)) (σ := (62040149/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (786035447/833402167 : ℝ) ^ p + (822622173/833402167 : ℝ) ^ p := by
    exact cert_lt (x := (786035447/833402167 : ℝ)) (y := (822622173/833402167 : ℝ)) (X := (25937275660497/100000000000000 : ℝ)) (Y := (4628920329403/6250000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (230688363/250000000 : ℝ)) (n' := (833402167/1000000000 : ℝ)) (Ab := (786035447/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (923011297/1000000000 : ℝ) ^ p + (496295347/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (923011297/1000000000 : ℝ)) (y := (496295347/500000000 : ℝ)) (X := (15761110662637/100000000000000 : ℝ)) (Y := (42119453020459/50000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496295347/500000000 : ℝ) ^ p + (923011297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496295347/500000000 : ℝ)) (y := (923011297/1000000000 : ℝ)) (X := (42119453020459/50000000000000 : ℝ)) (Y := (15761110662637/100000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1915601991/1000000000 : ℝ)) (τ := (923011297/1000000000 : ℝ)) (σ := (496295347/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (196578115/208426823 : ℝ) ^ p + (411463649/416853646 : ℝ) ^ p := by
    exact cert_lt (x := (196578115/208426823 : ℝ)) (y := (411463649/416853646 : ℝ)) (X := (6482270942809/25000000000000 : ℝ)) (Y := (74070917674229/100000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (923011297/1000000000 : ℝ)) (n' := (208426823/250000000 : ℝ)) (Ab := (39315623/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (923022799/1000000000 : ℝ) ^ p + (992588379/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (923022799/1000000000 : ℝ)) (y := (992588379/1000000000 : ℝ)) (X := (7882820441093/50000000000000 : ℝ)) (Y := (16846875019321/20000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992588379/1000000000 : ℝ) ^ p + (923022799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992588379/1000000000 : ℝ)) (y := (923022799/1000000000 : ℝ)) (X := (16846875019321/20000000000000 : ℝ)) (Y := (7882820441093/50000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957805589/500000000 : ℝ)) (τ := (923022799/1000000000 : ℝ)) (σ := (992588379/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (786324815/833720901 : ℝ) ^ p + (822940907/833720901 : ℝ) ^ p := by
    exact cert_lt (x := (786324815/833720901 : ℝ)) (y := (822940907/833720901 : ℝ)) (X := (648217961823/2500000000000 : ℝ)) (Y := (4629455184209/6250000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (923022799/1000000000 : ℝ)) (n' := (833720901/1000000000 : ℝ)) (Ab := (157264963/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (57688957/62500000 : ℝ) ^ p + (248147069/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (57688957/62500000 : ℝ)) (y := (248147069/250000000 : ℝ)) (X := (15765842963247/100000000000000 : ℝ)) (Y := (21058543377313/25000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248147069/250000000 : ℝ) ^ p + (57688957/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248147069/250000000 : ℝ)) (y := (57688957/62500000 : ℝ)) (X := (21058543377313/25000000000000 : ℝ)) (Y := (15765842963247/100000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (478902897/250000000 : ℝ)) (τ := (57688957/62500000 : ℝ)) (σ := (248147069/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (393162683/416860754 : ℝ) ^ p + (411470757/416860754 : ℝ) ^ p := by
    exact cert_lt (x := (393162683/416860754 : ℝ)) (y := (411470757/416860754 : ℝ)) (X := (25928702128227/100000000000000 : ℝ)) (Y := (18517824809831/25000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (57688957/62500000 : ℝ)) (n' := (208430377/250000000 : ℝ)) (Ab := (393162683/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (184604667/200000000 : ℝ) ^ p + (992588271/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184604667/200000000 : ℝ)) (y := (992588271/1000000000 : ℝ)) (X := (1576585202347/10000000000000 : ℝ)) (Y := (8423416372347/10000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992588271/1000000000 : ℝ) ^ p + (184604667/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992588271/1000000000 : ℝ)) (y := (184604667/200000000 : ℝ)) (X := (8423416372347/10000000000000 : ℝ)) (Y := (1576585202347/10000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (957805803/500000000 : ℝ)) (τ := (184604667/200000000 : ℝ)) (σ := (992588271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (157265078/166744307 : ℝ) ^ p + (822941541/833721535 : ℝ) ^ p := by
    exact cert_lt (x := (157265078/166744307 : ℝ)) (y := (822941541/833721535 : ℝ)) (X := (2592870101407/10000000000000 : ℝ)) (Y := (9258912495501/12500000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (184604667/200000000 : ℝ)) (n' := (166744307/200000000 : ℝ)) (Ab := (78632539/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (115377917/125000000 : ℝ) ^ p + (992588271/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115377917/125000000 : ℝ)) (y := (992588271/1000000000 : ℝ)) (X := (985365776087/6250000000000 : ℝ)) (Y := (8423416372347/10000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992588271/1000000000 : ℝ) ^ p + (115377917/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992588271/1000000000 : ℝ)) (y := (115377917/125000000 : ℝ)) (X := (8423416372347/10000000000000 : ℝ)) (Y := (985365776087/6250000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1915611607/1000000000 : ℝ)) (τ := (115377917/125000000 : ℝ)) (σ := (992588271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (262108464/277907179 : ℝ) ^ p + (822941543/833721537 : ℝ) ^ p := by
    exact cert_lt (x := (262108464/277907179 : ℝ)) (y := (822941543/833721537 : ℝ)) (X := (12964350550267/50000000000000 : ℝ)) (Y := (9258912502211/12500000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115377917/125000000 : ℝ)) (n' := (833721537/1000000000 : ℝ)) (Ab := (49145337/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1915611607/1000000000 : ℝ)) (τ := (115377917/125000000 : ℝ)) (σ := (992588271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115377917/125000000 : ℝ)) (n' := (833721537/1000000000 : ℝ)) (Ab := (49145337/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1915611607/1000000000 : ℝ)) (τ := (115377917/125000000 : ℝ)) (σ := (992588271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115377917/125000000 : ℝ)) (n' := (833721537/1000000000 : ℝ)) (Ab := (49145337/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1915611607/1000000000 : ℝ)) (τ := (115377917/125000000 : ℝ)) (σ := (992588271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115377917/125000000 : ℝ)) (n' := (833721537/1000000000 : ℝ)) (Ab := (49145337/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1915611607/1000000000 : ℝ)) (τ := (115377917/125000000 : ℝ)) (σ := (992588271/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (826612613/903400374 : ℝ) ^ p + (898010377/903400374 : ℝ) ^ p := by
    exact cert_lt (x := (826612613/903400374 : ℝ)) (y := (898010377/903400374 : ℝ)) (X := (6445541132083/50000000000000 : ℝ)) (Y := (87108918012421/100000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1110006119/1193199252 : ℝ) ^ p + (591209629/596599626 : ℝ) ^ p := by
    exact cert_lt (x := (1110006119/1193199252 : ℝ)) (y := (591209629/596599626 : ℝ)) (X := (9442641237953/50000000000000 : ℝ)) (Y := (3244588727577/4000000000000 : ℝ)) 369 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992588271/1000000000 : ℝ)) (U := (298299813/250000000 : ℝ)) (Ab := (826612613/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115377917/125000000 : ℝ)) (σ := (992588271/1000000000 : ℝ)) (Ab := (1110006119/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab065
