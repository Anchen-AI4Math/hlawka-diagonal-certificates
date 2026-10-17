import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 62, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab062 (p : ℝ) (hpa : (367/16 : ℝ) ≤ p) (hpb : p ≤ (735/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1052868456559/50095500000000 : ℝ) (541551/50000000 : ℝ) (2000000300573/10019100000000 : ℝ) (3033/2500 : ℝ) (970272969/500000000 : ℝ) (970233077/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596580649/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11097/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4539/10000 : ℝ)
      else (7689/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1052868456559/50095500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (541551/50000000 : ℝ) := by norm_num
  have pc0 : 1 < (183335657/200000000 : ℝ) ^ p + (993677229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183335657/200000000 : ℝ)) (y := (993677229/1000000000 : ℝ)) (X := (6778606547207/50000000000000 : ℝ)) (Y := (17288560963723/20000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993677229/1000000000 : ℝ) ^ p + (183335657/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993677229/1000000000 : ℝ)) (y := (183335657/200000000 : ℝ)) (X := (17288560963723/20000000000000 : ℝ)) (Y := (6778606547207/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (955177757/500000000 : ℝ)) (τ := (183335657/200000000 : ℝ)) (σ := (993677229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779402294/826279395 : ℝ) ^ p + (54363225/55085293 : ℝ) ^ p := by
    exact cert_lt (x := (779402294/826279395 : ℝ)) (y := (54363225/55085293 : ℝ)) (X := (5229041242497/20000000000000 : ℝ)) (Y := (36927397596271/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (183335657/200000000 : ℝ)) (n' := (165255879/200000000 : ℝ)) (Ab := (389701147/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (461204737/500000000 : ℝ) ^ p + (992620699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461204737/500000000 : ℝ)) (y := (992620699/1000000000 : ℝ)) (X := (312876173411/2000000000000 : ℝ)) (Y := (84356207745457/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992620699/1000000000 : ℝ) ^ p + (461204737/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992620699/1000000000 : ℝ)) (y := (461204737/500000000 : ℝ)) (X := (84356207745457/100000000000000 : ℝ)) (Y := (312876173411/2000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1915030173/1000000000 : ℝ)) (τ := (461204737/500000000 : ℝ)) (σ := (992620699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785581277/833086588 : ℝ) ^ p + (205563892/208271647 : ℝ) ^ p := by
    exact cert_lt (x := (785581277/833086588 : ℝ)) (y := (205563892/208271647 : ℝ)) (X := (25960880518743/100000000000000 : ℝ)) (Y := (74039120382019/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (461204737/500000000 : ℝ)) (n' := (208271647/250000000 : ℝ)) (Ab := (785581277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (92266937/100000000 : ℝ) ^ p + (496284321/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (92266937/100000000 : ℝ)) (y := (496284321/500000000 : ℝ)) (X := (393634086301/2500000000000 : ℝ)) (Y := (21063663259721/25000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496284321/500000000 : ℝ) ^ p + (92266937/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496284321/500000000 : ℝ)) (y := (92266937/100000000 : ℝ)) (X := (21063663259721/25000000000000 : ℝ)) (Y := (393634086301/2500000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478809503/250000000 : ℝ)) (τ := (92266937/100000000 : ℝ)) (σ := (496284321/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785860537/833394297 : ℝ) ^ p + (274187759/277798099 : ℝ) ^ p := by
    exact cert_lt (x := (785860537/833394297 : ℝ)) (y := (274187759/277798099 : ℝ)) (X := (25952609434967/100000000000000 : ℝ)) (Y := (18511847921691/25000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (92266937/100000000 : ℝ)) (n' := (833394297/1000000000 : ℝ)) (Ab := (785860537/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922681029/1000000000 : ℝ) ^ p + (496283149/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (922681029/1000000000 : ℝ)) (y := (496283149/500000000 : ℝ)) (X := (492185436599/3125000000000 : ℝ)) (Y := (84250083029977/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496283149/500000000 : ℝ) ^ p + (922681029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496283149/500000000 : ℝ)) (y := (922681029/1000000000 : ℝ)) (X := (84250083029977/100000000000000 : ℝ)) (Y := (492185436599/3125000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1915247327/1000000000 : ℝ)) (τ := (922681029/1000000000 : ℝ)) (σ := (496283149/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (785873063/833408099 : ℝ) ^ p + (822577079/833408099 : ℝ) ^ p := by
    exact cert_lt (x := (785873063/833408099 : ℝ)) (y := (822577079/833408099 : ℝ)) (X := (25952238685849/100000000000000 : ℝ)) (Y := (14809552513199/20000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922681029/1000000000 : ℝ)) (n' := (833408099/1000000000 : ℝ)) (Ab := (785873063/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922681553/1000000000 : ℝ) ^ p + (62035387/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (922681553/1000000000 : ℝ)) (y := (62035387/62500000 : ℝ)) (X := (15750139417553/100000000000000 : ℝ)) (Y := (16849975274271/20000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62035387/62500000 : ℝ) ^ p + (922681553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62035387/62500000 : ℝ)) (y := (922681553/1000000000 : ℝ)) (X := (16849975274271/20000000000000 : ℝ)) (Y := (15750139417553/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383049549/200000000 : ℝ)) (τ := (922681553/1000000000 : ℝ)) (σ := (62035387/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (785873626/833408719 : ℝ) ^ p + (822577699/833408719 : ℝ) ^ p := by
    exact cert_lt (x := (785873626/833408719 : ℝ)) (y := (822577699/833408719 : ℝ)) (X := (25952222273963/100000000000000 : ℝ)) (Y := (9255972403253/12500000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922681553/1000000000 : ℝ)) (n' := (833408719/1000000000 : ℝ)) (Ab := (392936813/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (36907263/40000000 : ℝ) ^ p + (248141547/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (36907263/40000000 : ℝ)) (y := (248141547/250000000 : ℝ)) (X := (787507402161/5000000000000 : ℝ)) (Y := (42124934286463/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248141547/250000000 : ℝ) ^ p + (36907263/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (248141547/250000000 : ℝ)) (y := (36907263/40000000 : ℝ)) (X := (42124934286463/50000000000000 : ℝ)) (Y := (787507402161/5000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1915247763/1000000000 : ℝ)) (τ := (36907263/40000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (261957883/277802915 : ℝ) ^ p + (54838515/55560583 : ℝ) ^ p := by
    exact cert_lt (x := (261957883/277802915 : ℝ)) (y := (54838515/55560583 : ℝ)) (X := (25952221123279/100000000000000 : ℝ)) (Y := (74047779924669/100000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (36907263/40000000 : ℝ)) (n' := (166681749/200000000 : ℝ)) (Ab := (785873649/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (115335197/125000000 : ℝ) ^ p + (248141547/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115335197/125000000 : ℝ)) (y := (248141547/250000000 : ℝ)) (X := (492192138603/3125000000000 : ℝ)) (Y := (42124934286463/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248141547/250000000 : ℝ) ^ p + (115335197/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248141547/250000000 : ℝ)) (y := (115335197/125000000 : ℝ)) (X := (42124934286463/50000000000000 : ℝ)) (Y := (492192138603/3125000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (392936825/416704373 : ℝ) ^ p + (411288863/416704373 : ℝ) ^ p := by
    exact cert_lt (x := (392936825/416704373 : ℝ)) (y := (411288863/416704373 : ℝ)) (X := (12976110583271/50000000000000 : ℝ)) (Y := (3702388997577/5000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (n' := (416704373/500000000 : ℝ)) (Ab := (15717473/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478811941/250000000 : ℝ)) (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652703721/1806838702 : ℝ) ^ p + (898003841/903419351 : ℝ) ^ p := by
    exact cert_lt (x := (1652703721/1806838702 : ℝ)) (y := (898003841/903419351 : ℝ)) (X := (6449401453137/50000000000000 : ℝ)) (Y := (1360956209959/1562500000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (554836967/596580649 : ℝ) ^ p + (591165139/596580649 : ℝ) ^ p := by
    exact cert_lt (x := (554836967/596580649 : ℝ)) (y := (591165139/596580649 : ℝ)) (X := (18897210825433/100000000000000 : ℝ)) (Y := (40551394805833/50000000000000 : ℝ)) 735 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248141547/250000000 : ℝ)) (U := (596580649/500000000 : ℝ)) (Ab := (1652703721/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115335197/125000000 : ℝ)) (σ := (248141547/250000000 : ℝ)) (Ab := (554836967/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab062
