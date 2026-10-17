import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 80, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab080 (p : ℝ) (hpa : (47/2 : ℝ) ≤ p) (hpb : p ≤ (753/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (131205997583/6415500000000 : ℝ) (10531809/1000000000 : ℝ) (250000038493/1283100000000 : ℝ) (3033/2500 : ℝ) (970973159/500000000 : ℝ) (7767481/8000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149173699/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11117/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4573/10000 : ℝ)
      else (7723/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (131205997583/6415500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10531809/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (918774257/1000000000 : ℝ) ^ p + (993795983/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918774257/1000000000 : ℝ)) (y := (993795983/1000000000 : ℝ)) (X := (13622521584217/100000000000000 : ℝ)) (Y := (21594373857181/25000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993795983/1000000000 : ℝ) ^ p + (918774257/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993795983/1000000000 : ℝ)) (y := (918774257/1000000000 : ℝ)) (X := (21594373857181/25000000000000 : ℝ)) (Y := (13622521584217/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (2988391/1562500 : ℝ)) (τ := (918774257/1000000000 : ℝ)) (σ := (993795983/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782159155/828237652 : ℝ) ^ p + (817705843/828237652 : ℝ) ^ p := by
    exact cert_lt (x := (782159155/828237652 : ℝ)) (y := (817705843/828237652 : ℝ)) (X := (5200522270717/20000000000000 : ℝ)) (Y := (73997389864723/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (918774257/1000000000 : ℝ)) (n' := (207059413/250000000 : ℝ)) (Ab := (156431831/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (184885669/200000000 : ℝ) ^ p + (496374613/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184885669/200000000 : ℝ)) (y := (496374613/500000000 : ℝ)) (X := (1573819763849/10000000000000 : ℝ)) (Y := (16852363748263/20000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496374613/500000000 : ℝ) ^ p + (184885669/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496374613/500000000 : ℝ)) (y := (184885669/200000000 : ℝ)) (X := (16852363748263/20000000000000 : ℝ)) (Y := (1573819763849/10000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917177571/1000000000 : ℝ)) (τ := (184885669/200000000 : ℝ)) (σ := (496374613/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394124585/417466473 : ℝ) ^ p + (274800379/278310982 : ℝ) ^ p := by
    exact cert_lt (x := (394124585/417466473 : ℝ)) (y := (274800379/278310982 : ℝ)) (X := (129112810263/500000000000 : ℝ)) (Y := (18544359717167/25000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (184885669/200000000 : ℝ)) (n' := (417466473/500000000 : ℝ)) (Ab := (78824917/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (46233813/50000000 : ℝ) ^ p + (24817483/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (46233813/50000000 : ℝ)) (y := (24817483/25000000 : ℝ)) (X := (15837816642099/100000000000000 : ℝ)) (Y := (42081099765173/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24817483/25000000 : ℝ) ^ p + (46233813/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (24817483/25000000 : ℝ)) (y := (46233813/50000000 : ℝ)) (X := (42081099765173/50000000000000 : ℝ)) (Y := (15837816642099/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (95868779/50000000 : ℝ)) (τ := (46233813/50000000 : ℝ)) (σ := (24817483/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (197128829/208806399 : ℝ) ^ p + (91632643/92802844 : ℝ) ^ p := by
    exact cert_lt (x := (197128829/208806399 : ℝ)) (y := (91632643/92802844 : ℝ)) (X := (5162949707309/20000000000000 : ℝ)) (Y := (74185252408999/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (46233813/50000000 : ℝ)) (n' := (208806399/250000000 : ℝ)) (Ab := (197128829/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (115585877/125000000 : ℝ) ^ p + (992697147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115585877/125000000 : ℝ)) (y := (992697147/1000000000 : ℝ)) (X := (792107616647/5000000000000 : ℝ)) (Y := (21039466121943/25000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992697147/1000000000 : ℝ) ^ p + (115585877/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992697147/1000000000 : ℝ)) (y := (115585877/125000000 : ℝ)) (X := (21039466121943/25000000000000 : ℝ)) (Y := (792107616647/5000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1917384163/1000000000 : ℝ)) (τ := (115585877/125000000 : ℝ)) (σ := (992697147/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (788526861/835238291 : ℝ) ^ p + (824706482/835238291 : ℝ) ^ p := by
    exact cert_lt (x := (788526861/835238291 : ℝ)) (y := (824706482/835238291 : ℝ)) (X := (6453602389251/25000000000000 : ℝ)) (Y := (74185591250103/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (115585877/125000000 : ℝ)) (n' := (835238291/1000000000 : ℝ)) (Ab := (788526861/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (462343741/500000000 : ℝ) ^ p + (992697053/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462343741/500000000 : ℝ)) (y := (992697053/1000000000 : ℝ)) (X := (7921170100469/50000000000000 : ℝ)) (Y := (42078838483297/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992697053/1000000000 : ℝ) ^ p + (462343741/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992697053/1000000000 : ℝ)) (y := (462343741/500000000 : ℝ)) (X := (42078838483297/50000000000000 : ℝ)) (Y := (7921170100469/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (383476907/200000000 : ℝ)) (τ := (462343741/500000000 : ℝ)) (σ := (992697053/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (262842454/278412947 : ℝ) ^ p + (274902344/278412947 : ℝ) ^ p := by
    exact cert_lt (x := (262842454/278412947 : ℝ)) (y := (274902344/278412947 : ℝ)) (X := (5162879101031/20000000000000 : ℝ)) (Y := (4636600370619/6250000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (462343741/500000000 : ℝ)) (n' := (835238841/1000000000 : ℝ)) (Ab := (394263681/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (462343751/500000000 : ℝ) ^ p + (992697049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462343751/500000000 : ℝ)) (y := (992697049/1000000000 : ℝ)) (X := (1584234826399/10000000000000 : ℝ)) (Y := (42078834493489/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992697049/1000000000 : ℝ) ^ p + (462343751/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992697049/1000000000 : ℝ)) (y := (462343751/500000000 : ℝ)) (X := (42078834493489/50000000000000 : ℝ)) (Y := (1584234826399/10000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917384551/1000000000 : ℝ)) (τ := (462343751/500000000 : ℝ)) (σ := (992697049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (262842461/278412955 : ℝ) ^ p + (274902352/278412955 : ℝ) ^ p := by
    exact cert_lt (x := (262842461/278412955 : ℝ)) (y := (274902352/278412955 : ℝ)) (X := (25814394228079/100000000000000 : ℝ)) (Y := (74185606570477/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (462343751/500000000 : ℝ)) (n' := (167047773/200000000 : ℝ)) (Ab := (788527383/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (57792969/62500000 : ℝ) ^ p + (124087131/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (57792969/62500000 : ℝ)) (y := (124087131/125000000 : ℝ)) (X := (3168469814059/20000000000000 : ℝ)) (Y := (3366306679683/4000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124087131/125000000 : ℝ) ^ p + (57792969/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (124087131/125000000 : ℝ)) (y := (57792969/62500000 : ℝ)) (X := (3366306679683/4000000000000 : ℝ)) (Y := (3168469814059/20000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (788527385/835238867 : ℝ) ^ p + (824707058/835238867 : ℝ) ^ p := by
    exact cert_lt (x := (788527385/835238867 : ℝ)) (y := (824707058/835238867 : ℝ)) (X := (6453598578561/25000000000000 : ℝ)) (Y := (37092803311929/50000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (n' := (835238867/1000000000 : ℝ)) (Ab := (157705477/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (239673069/125000000 : ℝ)) (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1655773071/1806610408 : ℝ) ^ p + (1796078599/1806610408 : ℝ) ^ p := by
    exact cert_lt (x := (1655773071/1806610408 : ℝ)) (y := (1796078599/1806610408 : ℝ)) (X := (2570691573043/20000000000000 : ℝ)) (Y := (87146542359111/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1111636723/1193389592 : ℝ) ^ p + (1182857783/1193389592 : ℝ) ^ p := by
    exact cert_lt (x := (1111636723/1193389592 : ℝ)) (y := (1182857783/1193389592 : ℝ)) (X := (30123255391/160000000000 : ℝ)) (Y := (81172966114103/100000000000000 : ℝ)) 753 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124087131/125000000 : ℝ)) (U := (149173699/125000000 : ℝ)) (Ab := (1655773071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (57792969/62500000 : ℝ)) (σ := (124087131/125000000 : ℝ)) (Ab := (1111636723/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab080
