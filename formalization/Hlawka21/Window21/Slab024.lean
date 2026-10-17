import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 24, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab024 (p : ℝ) (hpa : (87/4 : ℝ) ≤ p) (hpb : p ≤ (697/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (265051967137/11875500000000 : ℝ) (2304197/200000000 : ℝ) (500000071253/2375100000000 : ℝ) (3033/2500 : ℝ) (484338957/250000000 : ℝ) (968633623/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192686289/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11053/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(223/500 : ℝ)
      else (1903/2500 : ℝ) ≤ X j i ∧ X j i ≤ (2367/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (265051967137/11875500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2304197/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (455939653/500000000 : ℝ) ^ p + (993411971/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (455939653/500000000 : ℝ)) (y := (993411971/1000000000 : ℝ)) (X := (6704333775377/50000000000000 : ℝ)) (Y := (17318269838661/20000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993411971/1000000000 : ℝ) ^ p + (455939653/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993411971/1000000000 : ℝ)) (y := (455939653/500000000 : ℝ)) (X := (17318269838661/20000000000000 : ℝ)) (Y := (6704333775377/50000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1905291277/1000000000 : ℝ)) (τ := (455939653/500000000 : ℝ)) (σ := (993411971/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (257701737/273915097 : ℝ) ^ p + (810224306/821745291 : ℝ) ^ p := by
    exact cert_lt (x := (257701737/273915097 : ℝ)) (y := (810224306/821745291 : ℝ)) (X := (26474444583147/100000000000000 : ℝ)) (Y := (1470511133363/2000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (455939653/500000000 : ℝ)) (n' := (821745291/1000000000 : ℝ)) (Ab := (773105211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (917769863/1000000000 : ℝ) ^ p + (992336623/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917769863/1000000000 : ℝ)) (y := (992336623/1000000000 : ℝ)) (X := (7713747592007/50000000000000 : ℝ)) (Y := (42286260025237/50000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992336623/1000000000 : ℝ) ^ p + (917769863/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992336623/1000000000 : ℝ)) (y := (917769863/1000000000 : ℝ)) (X := (42286260025237/50000000000000 : ℝ)) (Y := (7713747592007/50000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (955053243/500000000 : ℝ)) (τ := (917769863/1000000000 : ℝ)) (σ := (992336623/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (86607826/92087837 : ℝ) ^ p + (817269548/828790533 : ℝ) ^ p := by
    exact cert_lt (x := (86607826/92087837 : ℝ)) (y := (817269548/828790533 : ℝ)) (X := (3285077858729/12500000000000 : ℝ)) (Y := (14743875651363/20000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (917769863/1000000000 : ℝ)) (n' := (828790533/1000000000 : ℝ)) (Ab := (389735217/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (229514437/250000000 : ℝ) ^ p + (496139811/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (229514437/250000000 : ℝ)) (y := (496139811/500000000 : ℝ)) (X := (15533244992311/100000000000000 : ℝ)) (Y := (84466771033527/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496139811/500000000 : ℝ) ^ p + (229514437/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496139811/500000000 : ℝ)) (y := (229514437/250000000 : ℝ)) (X := (84466771033527/100000000000000 : ℝ)) (Y := (15533244992311/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (191033737/100000000 : ℝ)) (τ := (229514437/250000000 : ℝ)) (σ := (496139811/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (779780430/829133717 : ℝ) ^ p + (817612732/829133717 : ℝ) ^ p := by
    exact cert_lt (x := (779780430/829133717 : ℝ)) (y := (817612732/829133717 : ℝ)) (X := (26271253566189/100000000000000 : ℝ)) (Y := (73728747781151/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (229514437/250000000 : ℝ)) (n' := (829133717/1000000000 : ℝ)) (Ab := (77978043/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (45903583/50000000 : ℝ) ^ p + (124034607/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (45903583/50000000 : ℝ)) (y := (124034607/125000000 : ℝ)) (X := (15538372814351/100000000000000 : ℝ)) (Y := (84461642724157/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124034607/125000000 : ℝ) ^ p + (45903583/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (124034607/125000000 : ℝ)) (y := (45903583/50000000 : ℝ)) (X := (84461642724157/100000000000000 : ℝ)) (Y := (15538372814351/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (477587129/250000000 : ℝ)) (τ := (45903583/50000000 : ℝ)) (σ := (124034607/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (779795408/829150299 : ℝ) ^ p + (48095842/48773547 : ℝ) ^ p := by
    exact cert_lt (x := (779795408/829150299 : ℝ)) (y := (48095842/48773547 : ℝ)) (X := (13135400414509/50000000000000 : ℝ)) (Y := (589833602649/800000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (45903583/50000000 : ℝ)) (n' := (829150299/1000000000 : ℝ)) (Ab := (48737213/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (918072333/1000000000 : ℝ) ^ p + (496138361/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (918072333/1000000000 : ℝ)) (y := (496138361/500000000 : ℝ)) (X := (15538620916273/100000000000000 : ℝ)) (Y := (84461394288659/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496138361/500000000 : ℝ) ^ p + (918072333/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496138361/500000000 : ℝ)) (y := (918072333/1000000000 : ℝ)) (X := (84461394288659/100000000000000 : ℝ)) (Y := (15538620916273/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (382069811/200000000 : ℝ)) (τ := (918072333/1000000000 : ℝ)) (σ := (496138361/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (779796132/829151101 : ℝ) ^ p + (817630116/829151101 : ℝ) ^ p := by
    exact cert_lt (x := (779796132/829151101 : ℝ)) (y := (817630116/829151101 : ℝ)) (X := (656769465587/2500000000000 : ℝ)) (Y := (18432305554657/25000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (918072333/1000000000 : ℝ)) (n' := (829151101/1000000000 : ℝ)) (Ab := (194949033/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (183614473/200000000 : ℝ) ^ p + (248069179/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (183614473/200000000 : ℝ)) (y := (248069179/250000000 : ℝ)) (X := (15538632713189/100000000000000 : ℝ)) (Y := (42230691582349/50000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248069179/250000000 : ℝ) ^ p + (183614473/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248069179/250000000 : ℝ)) (y := (183614473/200000000 : ℝ)) (X := (42230691582349/50000000000000 : ℝ)) (Y := (15538632713189/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1910349081/1000000000 : ℝ)) (τ := (183614473/200000000 : ℝ)) (σ := (248069179/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (779796167/829151139 : ℝ) ^ p + (817630154/829151139 : ℝ) ^ p := by
    exact cert_lt (x := (779796167/829151139 : ℝ)) (y := (817630154/829151139 : ℝ)) (X := (5254155616379/20000000000000 : ℝ)) (Y := (73729223255691/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (183614473/200000000 : ℝ)) (n' := (829151139/1000000000 : ℝ)) (Ab := (779796167/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (459036183/500000000 : ℝ) ^ p + (248069179/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (459036183/500000000 : ℝ)) (y := (248069179/250000000 : ℝ)) (X := (15538633081843/100000000000000 : ℝ)) (Y := (42230691582349/50000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248069179/250000000 : ℝ) ^ p + (459036183/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248069179/250000000 : ℝ)) (y := (459036183/500000000 : ℝ)) (X := (42230691582349/50000000000000 : ℝ)) (Y := (15538633081843/100000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (955174541/500000000 : ℝ)) (τ := (459036183/500000000 : ℝ)) (σ := (248069179/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (194949042/207287785 : ℝ) ^ p + (163526031/165830228 : ℝ) ^ p := by
    exact cert_lt (x := (194949042/207287785 : ℝ)) (y := (163526031/165830228 : ℝ)) (X := (13135389062787/50000000000000 : ℝ)) (Y := (36864611641491/50000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (459036183/500000000 : ℝ)) (n' := (41457557/50000000 : ℝ)) (Ab := (97474521/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (955174541/500000000 : ℝ)) (τ := (459036183/500000000 : ℝ)) (σ := (248069179/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (459036183/500000000 : ℝ)) (n' := (41457557/50000000 : ℝ)) (Ab := (97474521/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (955174541/500000000 : ℝ)) (τ := (459036183/500000000 : ℝ)) (σ := (248069179/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (459036183/500000000 : ℝ)) (n' := (41457557/50000000 : ℝ)) (Ab := (97474521/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (955174541/500000000 : ℝ)) (τ := (459036183/500000000 : ℝ)) (σ := (248069179/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (459036183/500000000 : ℝ)) (n' := (41457557/50000000 : ℝ)) (Ab := (97474521/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (955174541/500000000 : ℝ)) (τ := (459036183/500000000 : ℝ)) (σ := (248069179/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1645726928/1807313711 : ℝ) ^ p + (256541818/258187673 : ℝ) ^ p := by
    exact cert_lt (x := (1645726928/1807313711 : ℝ)) (y := (256541818/258187673 : ℝ)) (X := (13002621695453/100000000000000 : ℝ)) (Y := (17399475713687/20000000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1105280759/1192686289 : ℝ) ^ p + (69480312/70158017 : ℝ) ^ p := by
    exact cert_lt (x := (1105280759/1192686289 : ℝ)) (y := (69480312/70158017 : ℝ)) (X := (19056840848497/100000000000000 : ℝ)) (Y := (10117894957561/12500000000000 : ℝ)) 697 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248069179/250000000 : ℝ)) (U := (1192686289/1000000000 : ℝ)) (Ab := (102857933/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (459036183/500000000 : ℝ)) (σ := (248069179/250000000 : ℝ)) (Ab := (1105280759/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab024
