import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 41, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab041 (p : ℝ) (hpa : (713/32 : ℝ) ≤ p) (hpb : p ≤ (357/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2113657258187/97324500000000 : ℝ) (1120193/100000000 : ℝ) (4000000583947/19464900000000 : ℝ) (3033/2500 : ℝ) (969412153/500000000 : ℝ) (193873983/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149112143/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11073/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(281/625 : ℝ)
      else (478/625 : ℝ) ≤ X j i ∧ X j i ≤ (11839/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2113657258187/97324500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1120193/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (182818517/200000000 : ℝ) ^ p + (198706633/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (182818517/200000000 : ℝ)) (y := (198706633/200000000 : ℝ)) (X := (1347700922027/10000000000000 : ℝ)) (Y := (86523006957029/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198706633/200000000 : ℝ) ^ p + (182818517/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198706633/200000000 : ℝ)) (y := (182818517/200000000 : ℝ)) (X := (86523006957029/100000000000000 : ℝ)) (Y := (1347700922027/10000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (7630503/4000000 : ℝ)) (τ := (182818517/200000000 : ℝ)) (σ := (198706633/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (776006851/823845128 : ℝ) ^ p + (406321599/411922564 : ℝ) ^ p := by
    exact cert_lt (x := (776006851/823845128 : ℝ)) (y := (406321599/411922564 : ℝ)) (X := (2632211321201/10000000000000 : ℝ)) (Y := (71951062351/97656250000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (182818517/200000000 : ℝ)) (n' := (102980641/125000000 : ℝ)) (Ab := (776006851/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (229978163/250000000 : ℝ) ^ p + (992465879/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229978163/250000000 : ℝ)) (y := (992465879/1000000000 : ℝ)) (X := (7763648017243/50000000000000 : ℝ)) (Y := (84472720708659/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992465879/1000000000 : ℝ) ^ p + (229978163/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992465879/1000000000 : ℝ)) (y := (229978163/250000000 : ℝ)) (X := (84472720708659/100000000000000 : ℝ)) (Y := (7763648017243/50000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1912378531/1000000000 : ℝ)) (τ := (229978163/250000000 : ℝ)) (σ := (992465879/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (391144625/415391897 : ℝ) ^ p + (409790932/415391897 : ℝ) ^ p := by
    exact cert_lt (x := (391144625/415391897 : ℝ)) (y := (409790932/415391897 : ℝ)) (X := (26132617408587/100000000000000 : ℝ)) (Y := (9233422935401/12500000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (229978163/250000000 : ℝ)) (n' := (415391897/500000000 : ℝ)) (Ab := (3129157/4000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (46009377/50000000 : ℝ) ^ p + (992411159/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46009377/50000000 : ℝ)) (y := (992411159/1000000000 : ℝ)) (X := (15631153273939/100000000000000 : ℝ)) (Y := (84368862679709/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992411159/1000000000 : ℝ) ^ p + (46009377/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992411159/1000000000 : ℝ)) (y := (46009377/50000000 : ℝ)) (X := (84368862679709/100000000000000 : ℝ)) (Y := (15631153273939/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1912598699/1000000000 : ℝ)) (τ := (46009377/50000000 : ℝ)) (σ := (992411159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (782584955/831110453 : ℝ) ^ p + (819908523/831110453 : ℝ) ^ p := by
    exact cert_lt (x := (782584955/831110453 : ℝ)) (y := (819908523/831110453 : ℝ)) (X := (26123762836947/100000000000000 : ℝ)) (Y := (36938118972919/50000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (46009377/50000000 : ℝ)) (n' := (831110453/1000000000 : ℝ)) (Ab := (156516991/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (46010019/50000000 : ℝ) ^ p + (992408593/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46010019/50000000 : ℝ)) (y := (992408593/1000000000 : ℝ)) (X := (781801031159/5000000000000 : ℝ)) (Y := (2636374857241/3125000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992408593/1000000000 : ℝ) ^ p + (46010019/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992408593/1000000000 : ℝ)) (y := (46010019/50000000 : ℝ)) (X := (2636374857241/3125000000000 : ℝ)) (Y := (781801031159/5000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1912608973/1000000000 : ℝ)) (τ := (46010019/50000000 : ℝ)) (σ := (992408593/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (21151318/22462857 : ℝ) ^ p + (819923779/831125709 : ℝ) ^ p := by
    exact cert_lt (x := (21151318/22462857 : ℝ)) (y := (819923779/831125709 : ℝ)) (X := (653083750603/2500000000000 : ℝ)) (Y := (14775330266333/20000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (46010019/50000000 : ℝ)) (n' := (831125709/1000000000 : ℝ)) (Ab := (391299383/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (46010049/50000000 : ℝ) ^ p + (992408473/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46010049/50000000 : ℝ)) (y := (992408473/1000000000 : ℝ)) (X := (1954531013101/12500000000000 : ℝ)) (Y := (21090941954877/25000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992408473/1000000000 : ℝ) ^ p + (46010049/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992408473/1000000000 : ℝ)) (y := (46010049/50000000 : ℝ)) (X := (21090941954877/25000000000000 : ℝ)) (Y := (1954531013101/12500000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1912609453/1000000000 : ℝ)) (τ := (46010049/50000000 : ℝ)) (σ := (992408473/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (782599410/831126421 : ℝ) ^ p + (819924491/831126421 : ℝ) ^ p := by
    exact cert_lt (x := (782599410/831126421 : ℝ)) (y := (819924491/831126421 : ℝ)) (X := (26123330340313/100000000000000 : ℝ)) (Y := (18469167656033/25000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (46010049/50000000 : ℝ)) (n' := (831126421/1000000000 : ℝ)) (Ab := (78259941/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (920201007/1000000000 : ℝ) ^ p + (248102117/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (920201007/1000000000 : ℝ)) (y := (248102117/250000000 : ℝ)) (X := (3909064585389/25000000000000 : ℝ)) (Y := (84363758335679/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248102117/250000000 : ℝ) ^ p + (920201007/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248102117/250000000 : ℝ)) (y := (920201007/1000000000 : ℝ)) (X := (84363758335679/100000000000000 : ℝ)) (Y := (3909064585389/25000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (76504379/40000000 : ℝ)) (τ := (920201007/1000000000 : ℝ)) (σ := (248102117/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (782599439/831126453 : ℝ) ^ p + (819924523/831126453 : ℝ) ^ p := by
    exact cert_lt (x := (782599439/831126453 : ℝ)) (y := (819924523/831126453 : ℝ)) (X := (26123329497491/100000000000000 : ℝ)) (Y := (73876671491209/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (920201007/1000000000 : ℝ)) (n' := (831126453/1000000000 : ℝ)) (Ab := (782599439/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (920201009/1000000000 : ℝ) ^ p + (992408467/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920201009/1000000000 : ℝ)) (y := (992408467/1000000000 : ℝ)) (X := (15636259099833/100000000000000 : ℝ)) (Y := (84363756438913/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992408467/1000000000 : ℝ) ^ p + (920201009/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992408467/1000000000 : ℝ)) (y := (920201009/1000000000 : ℝ)) (X := (84363756438913/100000000000000 : ℝ)) (Y := (15636259099833/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478152369/250000000 : ℝ)) (τ := (920201009/1000000000 : ℝ)) (σ := (992408467/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (391299721/415563228 : ℝ) ^ p + (409962263/415563228 : ℝ) ^ p := by
    exact cert_lt (x := (391299721/415563228 : ℝ)) (y := (409962263/415563228 : ℝ)) (X := (522466592559/2000000000000 : ℝ)) (Y := (73876671572497/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (920201009/1000000000 : ℝ)) (n' := (103890807/125000000 : ℝ)) (Ab := (391299721/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478152369/250000000 : ℝ)) (τ := (920201009/1000000000 : ℝ)) (σ := (992408467/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (920201009/1000000000 : ℝ)) (n' := (103890807/125000000 : ℝ)) (Ab := (391299721/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478152369/250000000 : ℝ)) (τ := (920201009/1000000000 : ℝ)) (σ := (992408467/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (920201009/1000000000 : ℝ)) (n' := (103890807/125000000 : ℝ)) (Ab := (391299721/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478152369/250000000 : ℝ)) (τ := (920201009/1000000000 : ℝ)) (σ := (992408467/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (920201009/1000000000 : ℝ)) (n' := (103890807/125000000 : ℝ)) (Ab := (391299721/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478152369/250000000 : ℝ)) (τ := (920201009/1000000000 : ℝ)) (σ := (992408467/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (96996227/106300168 : ℝ) ^ p + (897950463/903551428 : ℝ) ^ p := by
    exact cert_lt (x := (96996227/106300168 : ℝ)) (y := (897950463/903551428 : ℝ)) (X := (12954737443757/100000000000000 : ℝ)) (Y := (87045262790583/100000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1107289581/1192897144 : ℝ) ^ p + (590847607/596448572 : ℝ) ^ p := by
    exact cert_lt (x := (1107289581/1192897144 : ℝ)) (y := (590847607/596448572 : ℝ)) (X := (18983396304121/100000000000000 : ℝ)) (Y := (40508302067339/50000000000000 : ℝ)) 357 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992408467/1000000000 : ℝ)) (U := (149112143/125000000 : ℝ)) (Ab := (1648935859/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (920201009/1000000000 : ℝ)) (σ := (992408467/1000000000 : ℝ)) (Ab := (1107289581/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab041
