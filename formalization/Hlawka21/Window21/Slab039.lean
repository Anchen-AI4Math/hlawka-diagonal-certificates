import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 39, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab039 (p : ℝ) (hpa : (711/32 : ℝ) ≤ p) (hpb : p ≤ (89/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1057218065641/48525750000000 : ℝ) (2809641/250000000 : ℝ) (4000000582309/19410300000000 : ℝ) (3033/2500 : ℝ) (969327563/500000000 : ℝ) (242321273/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192872183/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11071/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1123/2500 : ℝ)
      else (7643/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5919/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1057218065641/48525750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2809641/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (913837959/1000000000 : ℝ) ^ p + (7948153/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (913837959/1000000000 : ℝ)) (y := (7948153/8000000 : ℝ)) (X := (13469130553101/100000000000000 : ℝ)) (Y := (10816360807781/12500000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (7948153/8000000 : ℝ) ^ p + (913837959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7948153/8000000 : ℝ)) (y := (913837959/1000000000 : ℝ)) (X := (10816360807781/12500000000000 : ℝ)) (Y := (13469130553101/100000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (476839271/250000000 : ℝ)) (τ := (913837959/1000000000 : ℝ)) (σ := (7948153/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (775672817/823604306 : ℝ) ^ p + (406182871/411802153 : ℝ) ^ p := by
    exact cert_lt (x := (775672817/823604306 : ℝ)) (y := (406182871/411802153 : ℝ)) (X := (26339600849901/100000000000000 : ℝ)) (Y := (73660400176259/100000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (913837959/1000000000 : ℝ)) (n' := (411802153/500000000 : ℝ)) (Ab := (775672817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (919666401/1000000000 : ℝ) ^ p + (992450857/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919666401/1000000000 : ℝ)) (y := (992450857/1000000000 : ℝ)) (X := (3878954053931/25000000000000 : ℝ)) (Y := (10560525018587/12500000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992450857/1000000000 : ℝ) ^ p + (919666401/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992450857/1000000000 : ℝ)) (y := (919666401/1000000000 : ℝ)) (X := (10560525018587/12500000000000 : ℝ)) (Y := (3878954053931/25000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956058629/500000000 : ℝ)) (τ := (919666401/1000000000 : ℝ)) (σ := (992450857/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (390982508/415277759 : ℝ) ^ p + (409658477/415277759 : ℝ) ^ p := by
    exact cert_lt (x := (390982508/415277759 : ℝ)) (y := (409658477/415277759 : ℝ)) (X := (13074801289691/50000000000000 : ℝ)) (Y := (18462599600019/25000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (919666401/1000000000 : ℝ)) (n' := (415277759/500000000 : ℝ)) (Ab := (97745627/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (919942777/1000000000 : ℝ) ^ p + (7939167/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (919942777/1000000000 : ℝ)) (y := (7939167/8000000 : ℝ)) (X := (195248686719/1250000000000 : ℝ)) (Y := (21095030388643/25000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (7939167/8000000 : ℝ) ^ p + (919942777/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7939167/8000000 : ℝ)) (y := (919942777/1000000000 : ℝ)) (X := (21095030388643/25000000000000 : ℝ)) (Y := (195248686719/1250000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (478084663/250000000 : ℝ)) (τ := (919942777/1000000000 : ℝ)) (σ := (7939167/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (195565589/207721016 : ℝ) ^ p + (2302375/2333944 : ℝ) ^ p := by
    exact cert_lt (x := (195565589/207721016 : ℝ)) (y := (2302375/2333944 : ℝ)) (X := (26140690097097/100000000000000 : ℝ)) (Y := (4616206960729/6250000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (919942777/1000000000 : ℝ)) (n' := (25965127/31250000 : ℝ)) (Ab := (195565589/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (459977869/500000000 : ℝ) ^ p + (496196643/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (459977869/500000000 : ℝ)) (y := (496196643/500000000 : ℝ)) (X := (3124958434253/20000000000000 : ℝ)) (Y := (16875044741493/20000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496196643/500000000 : ℝ) ^ p + (459977869/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496196643/500000000 : ℝ)) (y := (459977869/500000000 : ℝ)) (X := (16875044741493/20000000000000 : ℝ)) (Y := (3124958434253/20000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (59760907/31250000 : ℝ)) (τ := (459977869/500000000 : ℝ)) (σ := (496196643/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (782276297/830899469 : ℝ) ^ p + (819660905/830899469 : ℝ) ^ p := by
    exact cert_lt (x := (782276297/830899469 : ℝ)) (y := (819660905/830899469 : ℝ)) (X := (5228054370831/20000000000000 : ℝ)) (Y := (73859729138949/100000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (459977869/500000000 : ℝ)) (n' := (830899469/1000000000 : ℝ)) (Ab := (782276297/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (183991269/200000000 : ℝ) ^ p + (198478633/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (183991269/200000000 : ℝ)) (y := (198478633/200000000 : ℝ)) (X := (7812510779203/50000000000000 : ℝ)) (Y := (42187497403693/50000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198478633/200000000 : ℝ) ^ p + (183991269/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198478633/200000000 : ℝ)) (y := (183991269/200000000 : ℝ)) (X := (42187497403693/50000000000000 : ℝ)) (Y := (7812510779203/50000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (191234951/100000000 : ℝ)) (τ := (183991269/200000000 : ℝ)) (σ := (198478633/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (782276951/830900191 : ℝ) ^ p + (819661627/830900191 : ℝ) ^ p := by
    exact cert_lt (x := (782276951/830900191 : ℝ)) (y := (819661627/830900191 : ℝ)) (X := (26140252709481/100000000000000 : ℝ)) (Y := (147719497437/200000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (183991269/200000000 : ℝ)) (n' := (830900191/1000000000 : ℝ)) (Ab := (782276951/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (459978187/500000000 : ℝ) ^ p + (992393159/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459978187/500000000 : ℝ)) (y := (992393159/1000000000 : ℝ)) (X := (7812516258837/50000000000000 : ℝ)) (Y := (10546872932123/12500000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992393159/1000000000 : ℝ) ^ p + (459978187/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992393159/1000000000 : ℝ)) (y := (459978187/500000000 : ℝ)) (X := (10546872932123/12500000000000 : ℝ)) (Y := (7812516258837/50000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1912349533/1000000000 : ℝ)) (τ := (459978187/500000000 : ℝ)) (σ := (992393159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (782276981/830900225 : ℝ) ^ p + (819661661/830900225 : ℝ) ^ p := by
    exact cert_lt (x := (782276981/830900225 : ℝ)) (y := (819661661/830900225 : ℝ)) (X := (26140251214783/100000000000000 : ℝ)) (Y := (4616234352533/6250000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (459978187/500000000 : ℝ)) (n' := (33236009/40000000 : ℝ)) (Ab := (782276981/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (7359651/8000000 : ℝ) ^ p + (992393159/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7359651/8000000 : ℝ)) (y := (992393159/1000000000 : ℝ)) (X := (781251644779/5000000000000 : ℝ)) (Y := (10546872932123/12500000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992393159/1000000000 : ℝ) ^ p + (7359651/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992393159/1000000000 : ℝ)) (y := (7359651/8000000 : ℝ)) (X := (10546872932123/12500000000000 : ℝ)) (Y := (781251644779/5000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (956174767/500000000 : ℝ)) (τ := (7359651/8000000 : ℝ)) (σ := (992393159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (782276983/830900227 : ℝ) ^ p + (819661663/830900227 : ℝ) ^ p := by
    exact cert_lt (x := (782276983/830900227 : ℝ)) (y := (819661663/830900227 : ℝ)) (X := (130701256509/500000000000 : ℝ)) (Y := (14771949938953/20000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (7359651/8000000 : ℝ)) (n' := (830900227/1000000000 : ℝ)) (Ab := (782276983/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (956174767/500000000 : ℝ)) (τ := (7359651/8000000 : ℝ)) (σ := (992393159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (7359651/8000000 : ℝ)) (n' := (830900227/1000000000 : ℝ)) (Ab := (782276983/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (956174767/500000000 : ℝ)) (τ := (7359651/8000000 : ℝ)) (σ := (992393159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (7359651/8000000 : ℝ)) (n' := (830900227/1000000000 : ℝ)) (Ab := (782276983/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (956174767/500000000 : ℝ)) (τ := (7359651/8000000 : ℝ)) (σ := (992393159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (7359651/8000000 : ℝ)) (n' := (830900227/1000000000 : ℝ)) (Ab := (782276983/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (956174767/500000000 : ℝ)) (τ := (7359651/8000000 : ℝ)) (σ := (992393159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1648565947/1807127817 : ℝ) ^ p + (598629751/602375939 : ℝ) ^ p := by
    exact cert_lt (x := (1648565947/1807127817 : ℝ)) (y := (598629751/602375939 : ℝ)) (X := (12960249002339/100000000000000 : ℝ)) (Y := (87039751346193/100000000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1107057004/1192872183 : ℝ) ^ p + (393877873/397624061 : ℝ) ^ p := by
    exact cert_lt (x := (1107057004/1192872183 : ℝ)) (y := (393877873/397624061 : ℝ)) (X := (18991865114587/100000000000000 : ℝ)) (Y := (10126016936203/12500000000000 : ℝ)) 89 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992393159/1000000000 : ℝ)) (U := (1192872183/1000000000 : ℝ)) (Ab := (1648565947/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (7359651/8000000 : ℝ)) (σ := (992393159/1000000000 : ℝ)) (Ab := (276764251/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab039
