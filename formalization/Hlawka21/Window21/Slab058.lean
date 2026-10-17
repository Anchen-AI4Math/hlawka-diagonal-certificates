import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 58, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab058 (p : ℝ) (hpa : (365/16 : ℝ) ≤ p) (hpb : p ≤ (731/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (105360544927/4982250000000 : ℝ) (2724949/250000000 : ℝ) (400000059787/1992900000000 : ℝ) (3033/2500 : ℝ) (970112759/500000000 : ℝ) (242518109/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298277689/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11093/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4531/10000 : ℝ)
      else (7681/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (105360544927/4982250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2724949/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (183239559/200000000 : ℝ) ^ p + (198730051/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (183239559/200000000 : ℝ)) (y := (198730051/200000000 : ℝ)) (X := (1354227885233/10000000000000 : ℝ)) (Y := (432288690767/500000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198730051/200000000 : ℝ) ^ p + (183239559/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198730051/200000000 : ℝ)) (y := (183239559/200000000 : ℝ)) (X := (432288690767/500000000000 : ℝ)) (Y := (1354227885233/10000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (38196961/20000000 : ℝ)) (τ := (183239559/200000000 : ℝ)) (σ := (198730051/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (389385437/412914293 : ℝ) ^ p + (407464395/412914293 : ℝ) ^ p := by
    exact cert_lt (x := (389385437/412914293 : ℝ)) (y := (407464395/412914293 : ℝ)) (X := (13088998774773/50000000000000 : ℝ)) (Y := (73822003931519/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (183239559/200000000 : ℝ)) (n' := (412914293/500000000 : ℝ)) (Ab := (389385437/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (36877841/40000000 : ℝ) ^ p + (496295809/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (36877841/40000000 : ℝ)) (y := (496295809/500000000 : ℝ)) (X := (15622163487477/100000000000000 : ℝ)) (Y := (42188926698479/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496295809/500000000 : ℝ) ^ p + (36877841/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496295809/500000000 : ℝ)) (y := (36877841/40000000 : ℝ)) (X := (42188926698479/50000000000000 : ℝ)) (Y := (15622163487477/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1914537643/1000000000 : ℝ)) (τ := (36877841/40000000 : ℝ)) (σ := (496295809/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784969609/832660766 : ℝ) ^ p + (410880485/416330383 : ℝ) ^ p := by
    exact cert_lt (x := (784969609/832660766 : ℝ)) (y := (410880485/416330383 : ℝ)) (X := (6498175549631/25000000000000 : ℝ)) (Y := (3700364948301/5000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (36877841/40000000 : ℝ)) (n' := (416330383/500000000 : ℝ)) (Ab := (784969609/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922208689/1000000000 : ℝ) ^ p + (992539067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922208689/1000000000 : ℝ)) (y := (992539067/1000000000 : ℝ)) (X := (15724153015973/100000000000000 : ℝ)) (Y := (42137931985651/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992539067/1000000000 : ℝ) ^ p + (922208689/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992539067/1000000000 : ℝ)) (y := (922208689/1000000000 : ℝ)) (X := (42137931985651/50000000000000 : ℝ)) (Y := (15724153015973/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478686939/250000000 : ℝ)) (τ := (922208689/1000000000 : ℝ)) (σ := (992539067/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785251901/832971964 : ℝ) ^ p + (205518042/208242991 : ℝ) ^ p := by
    exact cert_lt (x := (785251901/832971964 : ℝ)) (y := (205518042/208242991 : ℝ)) (X := (25984323960559/100000000000000 : ℝ)) (Y := (37007838525203/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922208689/1000000000 : ℝ)) (n' := (208242991/250000000 : ℝ)) (Ab := (785251901/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922220563/1000000000 : ℝ) ^ p + (496268341/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922220563/1000000000 : ℝ)) (y := (496268341/500000000 : ℝ)) (X := (3932194641997/25000000000000 : ℝ)) (Y := (10533904753923/12500000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496268341/500000000 : ℝ) ^ p + (922220563/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496268341/500000000 : ℝ)) (y := (922220563/1000000000 : ℝ)) (X := (10533904753923/12500000000000 : ℝ)) (Y := (3932194641997/25000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (382951449/200000000 : ℝ)) (τ := (922220563/1000000000 : ℝ)) (σ := (496268341/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (13776573/14613790 : ℝ) ^ p + (411043117/416493015 : ℝ) ^ p := by
    exact cert_lt (x := (13776573/14613790 : ℝ)) (y := (411043117/416493015 : ℝ)) (X := (25983945883223/100000000000000 : ℝ)) (Y := (74016055609337/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922220563/1000000000 : ℝ)) (n' := (83298603/100000000 : ℝ)) (Ab := (785264661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922221099/1000000000 : ℝ) ^ p + (496268287/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922221099/1000000000 : ℝ)) (y := (496268287/500000000 : ℝ)) (X := (15728987399071/100000000000000 : ℝ)) (Y := (42135514280303/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496268287/500000000 : ℝ) ^ p + (922221099/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496268287/500000000 : ℝ)) (y := (922221099/1000000000 : ℝ)) (X := (42135514280303/50000000000000 : ℝ)) (Y := (15728987399071/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1914757673/1000000000 : ℝ)) (τ := (922221099/1000000000 : ℝ)) (σ := (496268287/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785265237/832986665 : ℝ) ^ p + (822086869/832986665 : ℝ) ^ p := by
    exact cert_lt (x := (785265237/832986665 : ℝ)) (y := (822086869/832986665 : ℝ)) (X := (25983928784221/100000000000000 : ℝ)) (Y := (4626004543679/6250000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922221099/1000000000 : ℝ)) (n' := (166597333/200000000 : ℝ)) (Ab := (785265237/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (230555281/250000000 : ℝ) ^ p + (992536569/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230555281/250000000 : ℝ)) (y := (992536569/1000000000 : ℝ)) (X := (245765580303/1562500000000 : ℝ)) (Y := (84271018862897/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992536569/1000000000 : ℝ) ^ p + (230555281/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992536569/1000000000 : ℝ)) (y := (230555281/250000000 : ℝ)) (X := (84271018862897/100000000000000 : ℝ)) (Y := (245765580303/1562500000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1914757693/1000000000 : ℝ)) (τ := (230555281/250000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (785265264/832986695 : ℝ) ^ p + (822086899/832986695 : ℝ) ^ p := by
    exact cert_lt (x := (785265264/832986695 : ℝ)) (y := (822086899/832986695 : ℝ)) (X := (5196785563139/20000000000000 : ℝ)) (Y := (74016073506243/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (230555281/250000000 : ℝ)) (n' := (166597339/200000000 : ℝ)) (Ab := (49079079/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (7377769/8000000 : ℝ) ^ p + (992536569/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7377769/8000000 : ℝ)) (y := (992536569/1000000000 : ℝ)) (X := (3145799505801/20000000000000 : ℝ)) (Y := (84271018862897/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992536569/1000000000 : ℝ) ^ p + (7377769/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992536569/1000000000 : ℝ)) (y := (7377769/8000000 : ℝ)) (X := (84271018862897/100000000000000 : ℝ)) (Y := (3145799505801/20000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785265265/832986696 : ℝ) ^ p + (205521725/208246674 : ℝ) ^ p := by
    exact cert_lt (x := (785265265/832986696 : ℝ)) (y := (205521725/208246674 : ℝ)) (X := (25983927858999/100000000000000 : ℝ)) (Y := (14803214706631/20000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (n' := (104123337/125000000 : ℝ)) (Ab := (157053053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (957378847/500000000 : ℝ)) (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (413000501/451722311 : ℝ) ^ p + (448997362/451722311 : ℝ) ^ p := by
    exact cert_lt (x := (413000501/451722311 : ℝ)) (y := (448997362/451722311 : ℝ)) (X := (12909197804557/100000000000000 : ℝ)) (Y := (87090802442723/100000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (277306946/298277689 : ℝ) ^ p + (295552740/298277689 : ℝ) ^ p := by
    exact cert_lt (x := (277306946/298277689 : ℝ)) (y := (295552740/298277689 : ℝ)) (X := (4728314864483/25000000000000 : ℝ)) (Y := (40543370522091/50000000000000 : ℝ)) 731 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992536569/1000000000 : ℝ)) (U := (298277689/250000000 : ℝ)) (Ab := (413000501/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (7377769/8000000 : ℝ)) (σ := (992536569/1000000000 : ℝ)) (Ab := (138653473/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab058
