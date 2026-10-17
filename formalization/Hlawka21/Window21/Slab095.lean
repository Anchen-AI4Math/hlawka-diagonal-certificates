import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 95, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab095 (p : ℝ) (hpa : (767/32 : ℝ) ≤ p) (hpb : p ≤ (24 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (418831583629/20939100000000 : ℝ) (10294629/1000000000 : ℝ) (4000000628173/20939100000000 : ℝ) (3033/2500 : ℝ) (485765971/250000000 : ℝ) (971495359/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596790219/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11133/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(23/50 : ℝ)
      else (31/40 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (418831583629/20939100000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10294629/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (460221129/500000000 : ℝ) ^ p + (248472943/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (460221129/500000000 : ℝ)) (y := (248472943/250000000 : ℝ)) (X := (3418670057579/25000000000000 : ℝ)) (Y := (43162668926319/50000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248472943/250000000 : ℝ) ^ p + (460221129/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248472943/250000000 : ℝ)) (y := (460221129/500000000 : ℝ)) (X := (43162668926319/50000000000000 : ℝ)) (Y := (3418670057579/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (191433403/100000000 : ℝ)) (τ := (460221129/500000000 : ℝ)) (σ := (248472943/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784356079/829786449 : ℝ) ^ p + (273163940/276595483 : ℝ) ^ p := by
    exact cert_lt (x := (784356079/829786449 : ℝ)) (y := (273163940/276595483 : ℝ)) (X := (101131470251/390625000000 : ℝ)) (Y := (18527586129919/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (460221129/500000000 : ℝ)) (n' := (829786449/1000000000 : ℝ)) (Ab := (784356079/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185206363/200000000 : ℝ) ^ p + (496426731/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (185206363/200000000 : ℝ)) (y := (496426731/500000000 : ℝ)) (X := (158132735681/1000000000000 : ℝ)) (Y := (84186742993677/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496426731/500000000 : ℝ) ^ p + (185206363/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496426731/500000000 : ℝ)) (y := (185206363/200000000 : ℝ)) (X := (84186742993677/100000000000000 : ℝ)) (Y := (158132735681/1000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918885277/1000000000 : ℝ)) (τ := (185206363/200000000 : ℝ)) (σ := (496426731/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (395186039/418194695 : ℝ) ^ p + (826094761/836389390 : ℝ) ^ p := by
    exact cert_lt (x := (395186039/418194695 : ℝ)) (y := (826094761/836389390 : ℝ)) (X := (25713061173443/100000000000000 : ℝ)) (Y := (74286940348189/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185206363/200000000 : ℝ)) (n' := (83638939/100000000 : ℝ)) (Ab := (395186039/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (463135159/500000000 : ℝ) ^ p + (992805261/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (463135159/500000000 : ℝ)) (y := (992805261/1000000000 : ℝ)) (X := (15911310071239/100000000000000 : ℝ)) (Y := (5255544217977/6250000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992805261/1000000000 : ℝ) ^ p + (463135159/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992805261/1000000000 : ℝ)) (y := (463135159/500000000 : ℝ)) (X := (5255544217977/6250000000000 : ℝ)) (Y := (15911310071239/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1919075579/1000000000 : ℝ)) (τ := (463135159/500000000 : ℝ)) (σ := (992805261/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (790627939/836670263 : ℝ) ^ p + (826375634/836670263 : ℝ) ^ p := by
    exact cert_lt (x := (790627939/836670263 : ℝ)) (y := (826375634/836670263 : ℝ)) (X := (803300044811/3125000000000 : ℝ)) (Y := (9286799919579/12500000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (463135159/500000000 : ℝ)) (n' := (836670263/1000000000 : ℝ)) (Ab := (790627939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (92628039/100000000 : ℝ) ^ p + (496401609/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (92628039/100000000 : ℝ)) (y := (496401609/500000000 : ℝ)) (X := (7957731475987/50000000000000 : ℝ)) (Y := (84084554669251/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496401609/500000000 : ℝ) ^ p + (92628039/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496401609/500000000 : ℝ)) (y := (92628039/100000000 : ℝ)) (X := (84084554669251/100000000000000 : ℝ)) (Y := (7957731475987/50000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239885451/125000000 : ℝ)) (τ := (92628039/100000000 : ℝ)) (σ := (496401609/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (790638743/836682123 : ℝ) ^ p + (275462498/278894041 : ℝ) ^ p := by
    exact cert_lt (x := (790638743/836682123 : ℝ)) (y := (275462498/278894041 : ℝ)) (X := (12852643355477/50000000000000 : ℝ)) (Y := (18573678555627/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (92628039/100000000 : ℝ)) (n' := (836682123/1000000000 : ℝ)) (Ab := (790638743/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (463140407/500000000 : ℝ) ^ p + (248200783/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (463140407/500000000 : ℝ)) (y := (248200783/250000000 : ℝ)) (X := (15915637798171/100000000000000 : ℝ)) (Y := (16816875972169/20000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248200783/250000000 : ℝ) ^ p + (463140407/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248200783/250000000 : ℝ)) (y := (463140407/500000000 : ℝ)) (X := (16816875972169/20000000000000 : ℝ)) (Y := (15915637798171/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (959541973/500000000 : ℝ)) (τ := (463140407/500000000 : ℝ)) (σ := (248200783/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (395319599/418341311 : ℝ) ^ p + (826387993/836682622 : ℝ) ^ p := by
    exact cert_lt (x := (395319599/418341311 : ℝ)) (y := (826387993/836682622 : ℝ)) (X := (25705273805313/100000000000000 : ℝ)) (Y := (74294727470069/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (463140407/500000000 : ℝ)) (n' := (418341311/500000000 : ℝ)) (Ab := (395319599/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926280833/1000000000 : ℝ) ^ p + (124100391/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (926280833/1000000000 : ℝ)) (y := (124100391/125000000 : ℝ)) (X := (15915645633303/100000000000000 : ℝ)) (Y := (8408437173023/10000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124100391/125000000 : ℝ) ^ p + (926280833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124100391/125000000 : ℝ)) (y := (926280833/1000000000 : ℝ)) (X := (8408437173023/10000000000000 : ℝ)) (Y := (15915645633303/100000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (790639219/836682645 : ℝ) ^ p + (275462672/278894215 : ℝ) ^ p := by
    exact cert_lt (x := (790639219/836682645 : ℝ)) (y := (275462672/278894215 : ℝ)) (X := (6426318308089/25000000000000 : ℝ)) (Y := (37147364040339/50000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (n' := (167336529/200000000 : ℝ)) (Ab := (790639219/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1919083961/1000000000 : ℝ)) (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (829112755/903209781 : ℝ) ^ p + (598708311/602139854 : ℝ) ^ p := by
    exact cert_lt (x := (829112755/903209781 : ℝ)) (y := (598708311/602139854 : ℝ)) (X := (12817376591499/100000000000000 : ℝ)) (Y := (21795655918433/25000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1113218285/1193580438 : ℝ) ^ p + (394428603/397860146 : ℝ) ^ p := by
    exact cert_lt (x := (1113218285/1193580438 : ℝ)) (y := (394428603/397860146 : ℝ)) (X := (9385498290157/50000000000000 : ℝ)) (Y := (16245800845341/20000000000000 : ℝ)) 24 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124100391/125000000 : ℝ)) (U := (596790219/500000000 : ℝ)) (Ab := (165822551/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (926280833/1000000000 : ℝ)) (σ := (124100391/125000000 : ℝ)) (Ab := (222643657/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab095
