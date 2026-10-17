import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 100, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab100 (p : ℝ) (hpa : (193/8 : ℝ) ≤ p) (hpb : p ≤ (773/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (523122259847/26344500000000 : ℝ) (10217889/1000000000 : ℝ) (1000000158067/5268900000000 : ℝ) (3033/2500 : ℝ) (242928363/125000000 : ℝ) (194335467/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596822037/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5569/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4609/10000 : ℝ)
      else (3879/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11851/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (523122259847/26344500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10217889/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (92098319/100000000 : ℝ) ^ p + (993923081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92098319/100000000 : ℝ)) (y := (993923081/1000000000 : ℝ)) (X := (6845815891043/50000000000000 : ℝ)) (Y := (8630838580031/10000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993923081/1000000000 : ℝ) ^ p + (92098319/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993923081/1000000000 : ℝ)) (y := (92098319/100000000 : ℝ)) (X := (8630838580031/10000000000000 : ℝ)) (Y := (6845815891043/50000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1914906271/1000000000 : ℝ)) (τ := (92098319/100000000 : ℝ)) (σ := (993923081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (392534557/415143447 : ℝ) ^ p + (273356335/276762298 : ℝ) ^ p := by
    exact cert_lt (x := (392534557/415143447 : ℝ)) (y := (273356335/276762298 : ℝ)) (X := (25853120660321/100000000000000 : ℝ)) (Y := (14829376082777/20000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (92098319/100000000 : ℝ)) (n' := (415143447/500000000 : ℝ)) (Ab := (392534557/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (115818903/125000000 : ℝ) ^ p + (496443819/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115818903/125000000 : ℝ)) (y := (496443819/500000000 : ℝ)) (X := (1979701812517/12500000000000 : ℝ)) (Y := (84162402765231/100000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496443819/500000000 : ℝ) ^ p + (115818903/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496443819/500000000 : ℝ)) (y := (115818903/125000000 : ℝ)) (X := (84162402765231/100000000000000 : ℝ)) (Y := (1979701812517/12500000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (959719431/500000000 : ℝ)) (τ := (115818903/125000000 : ℝ)) (σ := (496443819/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (791060507/836859271 : ℝ) ^ p + (826641382/836859271 : ℝ) ^ p := by
    exact cert_lt (x := (791060507/836859271 : ℝ)) (y := (826641382/836859271 : ℝ)) (X := (25677653880677/100000000000000 : ℝ)) (Y := (2322573355253/3125000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (115818903/125000000 : ℝ)) (n' := (836859271/1000000000 : ℝ)) (Ab := (791060507/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (9267867/10000000 : ℝ) ^ p + (992839987/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (9267867/10000000 : ℝ)) (y := (992839987/1000000000 : ℝ)) (X := (3983782571549/25000000000000 : ℝ)) (Y := (42032443115851/50000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992839987/1000000000 : ℝ) ^ p + (9267867/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (992839987/1000000000 : ℝ)) (y := (9267867/10000000 : ℝ)) (X := (42032443115851/50000000000000 : ℝ)) (Y := (3983782571549/25000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1919626687/1000000000 : ℝ)) (τ := (9267867/10000000 : ℝ)) (σ := (992839987/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (791313065/837136367 : ℝ) ^ p + (826918478/837136367 : ℝ) ^ p := by
    exact cert_lt (x := (791313065/837136367 : ℝ)) (y := (826918478/837136367 : ℝ)) (X := (25670307592551/100000000000000 : ℝ)) (Y := (74329693311741/100000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (9267867/10000000 : ℝ)) (n' := (837136367/1000000000 : ℝ)) (Ab := (158262613/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (185359311/200000000 : ℝ) ^ p + (496418993/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (185359311/200000000 : ℝ)) (y := (496418993/500000000 : ℝ)) (X := (15939223980793/100000000000000 : ℝ)) (Y := (84060793607771/100000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496418993/500000000 : ℝ) ^ p + (185359311/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496418993/500000000 : ℝ)) (y := (185359311/200000000 : ℝ)) (X := (84060793607771/100000000000000 : ℝ)) (Y := (15939223980793/100000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1919634541/1000000000 : ℝ)) (τ := (185359311/200000000 : ℝ)) (σ := (496418993/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (791323634/837147963 : ℝ) ^ p + (275643358/279049321 : ℝ) ^ p := by
    exact cert_lt (x := (791323634/837147963 : ℝ)) (y := (275643358/279049321 : ℝ)) (X := (25670000213897/100000000000000 : ℝ)) (Y := (74330000636241/100000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (185359311/200000000 : ℝ)) (n' := (837147963/1000000000 : ℝ)) (Ab := (395661817/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (115849621/125000000 : ℝ) ^ p + (496418951/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115849621/125000000 : ℝ)) (y := (496418951/500000000 : ℝ)) (X := (7969697779983/50000000000000 : ℝ)) (Y := (16812124361529/20000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496418951/500000000 : ℝ) ^ p + (115849621/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496418951/500000000 : ℝ)) (y := (115849621/125000000 : ℝ)) (X := (16812124361529/20000000000000 : ℝ)) (Y := (7969697779983/50000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (191963487/100000000 : ℝ)) (τ := (115849621/125000000 : ℝ)) (σ := (496418951/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (791324077/837148449 : ℝ) ^ p + (275643520/279049483 : ℝ) ^ p := by
    exact cert_lt (x := (791324077/837148449 : ℝ)) (y := (275643520/279049483 : ℝ)) (X := (5133997472999/20000000000000 : ℝ)) (Y := (1858250337909/2500000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (115849621/125000000 : ℝ)) (n' := (837148449/1000000000 : ℝ)) (Ab := (791324077/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (463398493/500000000 : ℝ) ^ p + (496418949/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (463398493/500000000 : ℝ)) (y := (496418949/500000000 : ℝ)) (X := (15939403038033/100000000000000 : ℝ)) (Y := (16812122725339/20000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496418949/500000000 : ℝ) ^ p + (463398493/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496418949/500000000 : ℝ)) (y := (463398493/500000000 : ℝ)) (X := (16812122725339/20000000000000 : ℝ)) (Y := (15939403038033/100000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (479908721/250000000 : ℝ)) (τ := (463398493/500000000 : ℝ)) (σ := (496418949/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (263774699/279049490 : ℝ) ^ p + (275643527/279049490 : ℝ) ^ p := by
    exact cert_lt (x := (263774699/279049490 : ℝ)) (y := (275643527/279049490 : ℝ)) (X := (12834993741077/50000000000000 : ℝ)) (Y := (18582503518227/25000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (463398493/500000000 : ℝ)) (n' := (83714847/100000000 : ℝ)) (Ab := (791324097/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (479908721/250000000 : ℝ)) (τ := (463398493/500000000 : ℝ)) (σ := (496418949/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (463398493/500000000 : ℝ)) (n' := (83714847/100000000 : ℝ)) (Ab := (791324097/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (479908721/250000000 : ℝ)) (τ := (463398493/500000000 : ℝ)) (σ := (496418949/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (463398493/500000000 : ℝ)) (n' := (83714847/100000000 : ℝ)) (Ab := (791324097/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (479908721/250000000 : ℝ)) (τ := (463398493/500000000 : ℝ)) (σ := (496418949/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (463398493/500000000 : ℝ)) (n' := (83714847/100000000 : ℝ)) (Ab := (791324097/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (479908721/250000000 : ℝ)) (τ := (463398493/500000000 : ℝ)) (σ := (496418949/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (463398493/500000000 : ℝ)) (n' := (83714847/100000000 : ℝ)) (Ab := (791324097/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (479908721/250000000 : ℝ)) (τ := (463398493/500000000 : ℝ)) (σ := (496418949/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (553007569/602118642 : ℝ) ^ p + (199570893/200706214 : ℝ) ^ p := by
    exact cert_lt (x := (553007569/602118642 : ℝ)) (y := (199570893/200706214 : ℝ)) (X := (12805674422743/100000000000000 : ℝ)) (Y := (87194325940779/100000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (185622487/198940679 : ℝ) ^ p + (394475395/397881358 : ℝ) ^ p := by
    exact cert_lt (x := (185622487/198940679 : ℝ)) (y := (394475395/397881358 : ℝ)) (X := (18752784244263/100000000000000 : ℝ)) (Y := (20311804056483/25000000000000 : ℝ)) 773 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496418949/500000000 : ℝ)) (U := (596822037/500000000 : ℝ)) (Ab := (1659022707/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (463398493/500000000 : ℝ)) (σ := (496418949/500000000 : ℝ)) (Ab := (556867461/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab100
