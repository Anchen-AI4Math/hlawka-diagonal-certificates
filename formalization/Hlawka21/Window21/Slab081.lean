import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 81, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab081 (p : ℝ) (hpa : (753/32 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (524736762737/25696125000000 : ℝ) (10515663/1000000000 : ℝ) (4000000616707/20556900000000 : ℝ) (3033/2500 : ℝ) (971011093/500000000 : ℝ) (485486579/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193402307/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5559/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(183/400 : ℝ)
      else (309/400 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (524736762737/25696125000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10515663/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (114860953/125000000 : ℝ) ^ p + (993802457/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114860953/125000000 : ℝ)) (y := (993802457/1000000000 : ℝ)) (X := (2725212357493/20000000000000 : ℝ)) (Y := (269918610639/312500000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993802457/1000000000 : ℝ) ^ p + (114860953/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993802457/1000000000 : ℝ)) (y := (114860953/125000000 : ℝ)) (X := (269918610639/312500000000 : ℝ)) (Y := (2725212357493/20000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1912690081/1000000000 : ℝ)) (τ := (114860953/125000000 : ℝ)) (σ := (993802457/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782308386/828343187 : ℝ) ^ p + (817827524/828343187 : ℝ) ^ p := by
    exact cert_lt (x := (782308386/828343187 : ℝ)) (y := (817827524/828343187 : ℝ)) (X := (25994920080693/100000000000000 : ℝ)) (Y := (37002540486539/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (114860953/125000000 : ℝ)) (n' := (828343187/1000000000 : ℝ)) (Ab := (391154193/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924537413/1000000000 : ℝ) ^ p + (31023633/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (924537413/1000000000 : ℝ)) (y := (31023633/31250000 : ℝ)) (X := (1967912644871/12500000000000 : ℝ)) (Y := (21064179030813/25000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (31023633/31250000 : ℝ) ^ p + (924537413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31023633/31250000 : ℝ)) (y := (924537413/1000000000 : ℝ)) (X := (21064179030813/25000000000000 : ℝ)) (Y := (1967912644871/12500000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917293669/1000000000 : ℝ)) (τ := (924537413/1000000000 : ℝ)) (σ := (31023633/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (788393459/835032294 : ℝ) ^ p + (30537653/30927122 : ℝ) ^ p := by
    exact cert_lt (x := (788393459/835032294 : ℝ)) (y := (30537653/30927122 : ℝ)) (X := (12907552371539/50000000000000 : ℝ)) (Y := (18546224150263/25000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924537413/1000000000 : ℝ)) (n' := (417516147/500000000 : ℝ)) (Ab := (788393459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184956937/200000000 : ℝ) ^ p + (496353233/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184956937/200000000 : ℝ)) (y := (496353233/500000000 : ℝ)) (X := (15842813863173/100000000000000 : ℝ)) (Y := (10519650394139/12500000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496353233/500000000 : ℝ) ^ p + (184956937/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496353233/500000000 : ℝ)) (y := (184956937/200000000 : ℝ)) (X := (10519650394139/12500000000000 : ℝ)) (Y := (15842813863173/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1917491151/1000000000 : ℝ)) (τ := (184956937/200000000 : ℝ)) (σ := (496353233/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (394329451/417662069 : ℝ) ^ p + (824808475/835324138 : ℝ) ^ p := by
    exact cert_lt (x := (394329451/417662069 : ℝ)) (y := (824808475/835324138 : ℝ)) (X := (25807315596639/100000000000000 : ℝ)) (Y := (7419268577983/10000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184956937/200000000 : ℝ)) (n' := (417662069/500000000 : ℝ)) (Ab := (394329451/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (924795393/1000000000 : ℝ) ^ p + (496352151/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924795393/1000000000 : ℝ)) (y := (496352151/500000000 : ℝ)) (X := (15847136792657/100000000000000 : ℝ)) (Y := (4207644030971/5000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496352151/500000000 : ℝ) ^ p + (924795393/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496352151/500000000 : ℝ)) (y := (924795393/1000000000 : ℝ)) (X := (4207644030971/5000000000000 : ℝ)) (Y := (15847136792657/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (383499939/200000000 : ℝ)) (τ := (924795393/1000000000 : ℝ)) (σ := (496352151/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (157734079/167067355 : ℝ) ^ p + (824821112/835336775 : ℝ) ^ p := by
    exact cert_lt (x := (157734079/167067355 : ℝ)) (y := (824821112/835336775 : ℝ)) (X := (2580697786191/10000000000000 : ℝ)) (Y := (18548255737537/25000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (924795393/1000000000 : ℝ)) (n' := (33413471/40000000 : ℝ)) (Ab := (157734079/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (924795857/1000000000 : ℝ) ^ p + (62044013/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (924795857/1000000000 : ℝ)) (y := (62044013/62500000 : ℝ)) (X := (15847324139749/100000000000000 : ℝ)) (Y := (84152692861683/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62044013/62500000 : ℝ) ^ p + (924795857/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62044013/62500000 : ℝ)) (y := (924795857/1000000000 : ℝ)) (X := (84152692861683/100000000000000 : ℝ)) (Y := (15847324139749/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383500013/200000000 : ℝ)) (τ := (924795857/1000000000 : ℝ)) (σ := (62044013/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (788670893/835337322 : ℝ) ^ p + (91646851/92815258 : ℝ) ^ p := by
    exact cert_lt (x := (788670893/835337322 : ℝ)) (y := (91646851/92815258 : ℝ)) (X := (12903481821563/50000000000000 : ℝ)) (Y := (37096518772283/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (924795857/1000000000 : ℝ)) (n' := (417668661/500000000 : ℝ)) (Ab := (788670893/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924795877/1000000000 : ℝ) ^ p + (248176051/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (924795877/1000000000 : ℝ)) (y := (248176051/250000000 : ℝ)) (X := (7923666107551/50000000000000 : ℝ)) (Y := (84152684872001/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248176051/250000000 : ℝ) ^ p + (924795877/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248176051/250000000 : ℝ)) (y := (924795877/1000000000 : ℝ)) (X := (84152684872001/100000000000000 : ℝ)) (Y := (7923666107551/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917500081/1000000000 : ℝ)) (τ := (924795877/1000000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (262890305/278445782 : ℝ) ^ p + (274940561/278445782 : ℝ) ^ p := by
    exact cert_lt (x := (262890305/278445782 : ℝ)) (y := (274940561/278445782 : ℝ)) (X := (516139262697/2000000000000 : ℝ)) (Y := (37096519092453/50000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924795877/1000000000 : ℝ)) (n' := (417668673/500000000 : ℝ)) (Ab := (157734183/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (462397939/500000000 : ℝ) ^ p + (248176051/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (462397939/500000000 : ℝ)) (y := (248176051/250000000 : ℝ)) (X := (1584733261887/10000000000000 : ℝ)) (Y := (84152684872001/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248176051/250000000 : ℝ) ^ p + (462397939/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248176051/250000000 : ℝ)) (y := (462397939/500000000 : ℝ)) (X := (84152684872001/100000000000000 : ℝ)) (Y := (1584733261887/10000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (788670916/835337347 : ℝ) ^ p + (824821684/835337347 : ℝ) ^ p := by
    exact cert_lt (x := (788670916/835337347 : ℝ)) (y := (824821684/835337347 : ℝ)) (X := (25806963177923/100000000000000 : ℝ)) (Y := (74193038211587/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (n' := (835337347/1000000000 : ℝ)) (Ab := (197167729/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (958750041/500000000 : ℝ)) (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (183993275/200733077 : ℝ) ^ p + (199564670/200733077 : ℝ) ^ p := by
    exact cert_lt (x := (183993275/200733077 : ℝ)) (y := (199564670/200733077 : ℝ)) (X := (1285100589099/10000000000000 : ℝ)) (Y := (87148994457979/100000000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1111743665/1193402307 : ℝ) ^ p + (394295548/397800769 : ℝ) ^ p := by
    exact cert_lt (x := (1111743665/1193402307 : ℝ)) (y := (394295548/397800769 : ℝ)) (X := (1176451973209/6250000000000 : ℝ)) (Y := (10147096127623/12500000000000 : ℝ)) 377 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248176051/250000000 : ℝ)) (U := (1193402307/1000000000 : ℝ)) (Ab := (66237579/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (462397939/500000000 : ℝ)) (σ := (248176051/250000000 : ℝ)) (Ab := (222348733/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab081
