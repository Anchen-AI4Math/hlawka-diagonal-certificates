import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 22, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab022 (p : ℝ) (hpa : (347/16 : ℝ) ≤ p) (hpb : p ≤ (695/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1060616253889/47365500000000 : ℝ) (11559699/1000000000 : ℝ) (2000000284193/9473100000000 : ℝ) (3033/2500 : ℝ) (968589209/500000000 : ℝ) (968544667/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192661719/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11051/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(557/1250 : ℝ)
      else (7607/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2367/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1060616253889/47365500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11559699/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (911611429/1000000000 : ℝ) ^ p + (496698717/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (911611429/1000000000 : ℝ)) (y := (496698717/500000000 : ℝ)) (X := (2093814873/15625000000 : ℝ)) (Y := (86599601094239/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496698717/500000000 : ℝ) ^ p + (911611429/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496698717/500000000 : ℝ)) (y := (911611429/1000000000 : ℝ)) (X := (86599601094239/100000000000000 : ℝ)) (Y := (2093814873/15625000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1905008863/1000000000 : ℝ)) (τ := (911611429/1000000000 : ℝ)) (σ := (496698717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (45456136/48322949 : ℝ) ^ p + (809930434/821490133 : ℝ) ^ p := by
    exact cert_lt (x := (45456136/48322949 : ℝ)) (y := (809930434/821490133 : ℝ)) (X := (13246469575441/50000000000000 : ℝ)) (Y := (14701412319503/20000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (911611429/1000000000 : ℝ)) (n' := (821490133/1000000000 : ℝ)) (Ab := (96594289/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (458755081/500000000 : ℝ) ^ p + (992321183/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458755081/500000000 : ℝ)) (y := (992321183/1000000000 : ℝ)) (X := (3083082254557/20000000000000 : ℝ)) (Y := (84584604291193/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992321183/1000000000 : ℝ) ^ p + (458755081/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992321183/1000000000 : ℝ)) (y := (458755081/500000000 : ℝ)) (X := (84584604291193/100000000000000 : ℝ)) (Y := (3083082254557/20000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (381966269/200000000 : ℝ)) (τ := (458755081/500000000 : ℝ)) (σ := (992321183/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (155825839/165709578 : ℝ) ^ p + (272329397/276182630 : ℝ) ^ p := by
    exact cert_lt (x := (155825839/165709578 : ℝ)) (y := (272329397/276182630 : ℝ)) (X := (13149300326223/50000000000000 : ℝ)) (Y := (36850700048987/50000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (458755081/500000000 : ℝ)) (n' := (82854789/100000000 : ℝ)) (Ab := (155825839/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (91779963/100000000 : ℝ) ^ p + (198452781/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (91779963/100000000 : ℝ)) (y := (198452781/200000000 : ℝ)) (X := (3880346338031/25000000000000 : ℝ)) (Y := (16895725924723/20000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198452781/200000000 : ℝ) ^ p + (91779963/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198452781/200000000 : ℝ)) (y := (91779963/100000000 : ℝ)) (X := (16895725924723/20000000000000 : ℝ)) (Y := (3880346338031/25000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (382012707/200000000 : ℝ)) (τ := (91779963/100000000 : ℝ)) (σ := (198452781/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (779440934/828893093 : ℝ) ^ p + (817333394/828893093 : ℝ) ^ p := by
    exact cert_lt (x := (779440934/828893093 : ℝ)) (y := (817333394/828893093 : ℝ)) (X := (13144584049463/50000000000000 : ℝ)) (Y := (18427708242067/25000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (91779963/100000000 : ℝ)) (n' := (828893093/1000000000 : ℝ)) (Ab := (389720467/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (36712547/40000000 : ℝ) ^ p + (198452223/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (36712547/40000000 : ℝ)) (y := (198452223/200000000 : ℝ)) (X := (15526544856943/100000000000000 : ℝ)) (Y := (42236735427517/50000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198452223/200000000 : ℝ) ^ p + (36712547/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (198452223/200000000 : ℝ)) (y := (36712547/40000000 : ℝ)) (X := (42236735427517/50000000000000 : ℝ)) (Y := (15526544856943/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (191007479/100000000 : ℝ)) (τ := (36712547/40000000 : ℝ)) (σ := (198452223/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (779456057/828909840 : ℝ) ^ p + (272450047/276303280 : ℝ) ^ p := by
    exact cert_lt (x := (779456057/828909840 : ℝ)) (y := (272450047/276303280 : ℝ)) (X := (26288710375707/100000000000000 : ℝ)) (Y := (73711290419117/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (36712547/40000000 : ℝ)) (n' := (10361373/12500000 : ℝ)) (Ab := (779456057/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (917814357/1000000000 : ℝ) ^ p + (992260979/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917814357/1000000000 : ℝ)) (y := (992260979/1000000000 : ℝ)) (X := (1940849429361/12500000000000 : ℝ)) (Y := (4223660969793/5000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992260979/1000000000 : ℝ) ^ p + (917814357/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992260979/1000000000 : ℝ)) (y := (917814357/1000000000 : ℝ)) (X := (4223660969793/5000000000000 : ℝ)) (Y := (1940849429361/12500000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (238759417/125000000 : ℝ)) (τ := (917814357/1000000000 : ℝ)) (σ := (992260979/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (779456792/828910653 : ℝ) ^ p + (272450318/276303551 : ℝ) ^ p := by
    exact cert_lt (x := (779456792/828910653 : ℝ)) (y := (272450318/276303551 : ℝ)) (X := (13144344385051/50000000000000 : ℝ)) (Y := (73711312626129/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (917814357/1000000000 : ℝ)) (n' := (828910653/1000000000 : ℝ)) (Ab := (97432099/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (917814389/1000000000 : ℝ) ^ p + (992260973/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917814389/1000000000 : ℝ)) (y := (992260973/1000000000 : ℝ)) (X := (3105361438461/20000000000000 : ℝ)) (Y := (84473208302089/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992260973/1000000000 : ℝ) ^ p + (917814389/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992260973/1000000000 : ℝ)) (y := (917814389/1000000000 : ℝ)) (X := (84473208302089/100000000000000 : ℝ)) (Y := (3105361438461/20000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (955037681/500000000 : ℝ)) (τ := (917814389/1000000000 : ℝ)) (σ := (992260973/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (779456826/828910691 : ℝ) ^ p + (817350992/828910691 : ℝ) ^ p := by
    exact cert_lt (x := (779456826/828910691 : ℝ)) (y := (817350992/828910691 : ℝ)) (X := (13144343750381/50000000000000 : ℝ)) (Y := (36855656832047/50000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (917814389/1000000000 : ℝ)) (n' := (828910691/1000000000 : ℝ)) (Ab := (389728413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (917814391/1000000000 : ℝ) ^ p + (992260973/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917814391/1000000000 : ℝ)) (y := (992260973/1000000000 : ℝ)) (X := (1940850990893/12500000000000 : ℝ)) (Y := (84473208302089/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992260973/1000000000 : ℝ) ^ p + (917814391/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992260973/1000000000 : ℝ)) (y := (917814391/1000000000 : ℝ)) (X := (84473208302089/100000000000000 : ℝ)) (Y := (1940850990893/12500000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (477518841/250000000 : ℝ)) (τ := (917814391/1000000000 : ℝ)) (σ := (992260973/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (779456828/828910693 : ℝ) ^ p + (817350994/828910693 : ℝ) ^ p := by
    exact cert_lt (x := (779456828/828910693 : ℝ)) (y := (817350994/828910693 : ℝ)) (X := (13144343794083/50000000000000 : ℝ)) (Y := (18427828429681/25000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (917814391/1000000000 : ℝ)) (n' := (828910693/1000000000 : ℝ)) (Ab := (194864207/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (477518841/250000000 : ℝ)) (τ := (917814391/1000000000 : ℝ)) (σ := (992260973/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (917814391/1000000000 : ℝ)) (n' := (828910693/1000000000 : ℝ)) (Ab := (194864207/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (477518841/250000000 : ℝ)) (τ := (917814391/1000000000 : ℝ)) (σ := (992260973/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (917814391/1000000000 : ℝ)) (n' := (828910693/1000000000 : ℝ)) (Ab := (194864207/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (477518841/250000000 : ℝ)) (τ := (917814391/1000000000 : ℝ)) (σ := (992260973/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (917814391/1000000000 : ℝ)) (n' := (828910693/1000000000 : ℝ)) (Ab := (194864207/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (477518841/250000000 : ℝ)) (τ := (917814391/1000000000 : ℝ)) (σ := (992260973/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1645339557/1807338281 : ℝ) ^ p + (1795778582/1807338281 : ℝ) ^ p := by
    exact cert_lt (x := (1645339557/1807338281 : ℝ)) (y := (1795778582/1807338281 : ℝ)) (X := (6504209101247/50000000000000 : ℝ)) (Y := (8699158211061/10000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1105039619/1192661719 : ℝ) ^ p + (1181102020/1192661719 : ℝ) ^ p := by
    exact cert_lt (x := (1105039619/1192661719 : ℝ)) (y := (1181102020/1192661719 : ℝ)) (X := (4766427545897/25000000000000 : ℝ)) (Y := (80934290316337/100000000000000 : ℝ)) 695 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992260973/1000000000 : ℝ)) (U := (1192661719/1000000000 : ℝ)) (Ab := (1645339557/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (917814391/1000000000 : ℝ)) (σ := (992260973/1000000000 : ℝ)) (Ab := (1105039619/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab022
