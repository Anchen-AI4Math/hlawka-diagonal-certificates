import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 0, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab000 (p : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (673/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (8322394127/358312500000 : ℝ) (3000759/250000000 : ℝ) (125000017199/573300000000 : ℝ) (3033/2500 : ℝ) (30236851/15625000 : ℝ) (483765889/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596197839/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(689/625 : ℝ) ≤ X j i ∧ X j i ≤ -(881/2000 : ℝ)
      else (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (8322394127/358312500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3000759/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (908554063/1000000000 : ℝ) ^ p + (993233509/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (908554063/1000000000 : ℝ)) (y := (993233509/1000000000 : ℝ)) (X := (106452219507/800000000000 : ℝ)) (Y := (86693488493779/100000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993233509/1000000000 : ℝ) ^ p + (908554063/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993233509/1000000000 : ℝ)) (y := (908554063/1000000000 : ℝ)) (X := (86693488493779/100000000000000 : ℝ)) (Y := (106452219507/800000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (475446893/250000000 : ℝ)) (τ := (908554063/1000000000 : ℝ)) (σ := (993233509/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (69886701/74414774 : ℝ) ^ p + (403279739/409281257 : ℝ) ^ p := by
    exact cert_lt (x := (69886701/74414774 : ℝ)) (y := (403279739/409281257 : ℝ)) (X := (3338111398769/12500000000000 : ℝ)) (Y := (4580944349379/6250000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (908554063/1000000000 : ℝ)) (n' := (409281257/500000000 : ℝ)) (Ab := (768753711/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (914540593/1000000000 : ℝ) ^ p + (496074027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (914540593/1000000000 : ℝ)) (y := (496074027/500000000 : ℝ)) (X := (381935764417/2500000000000 : ℝ)) (Y := (4236129247143/5000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496074027/500000000 : ℝ) ^ p + (914540593/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496074027/500000000 : ℝ)) (y := (914540593/1000000000 : ℝ)) (X := (4236129247143/5000000000000 : ℝ)) (Y := (381935764417/2500000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1906688647/1000000000 : ℝ)) (τ := (914540593/1000000000 : ℝ)) (σ := (496074027/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (193808299/206439279 : ℝ) ^ p + (67812840/68813093 : ℝ) ^ p := by
    exact cert_lt (x := (193808299/206439279 : ℝ)) (y := (67812840/68813093 : ℝ)) (X := (26504760738349/100000000000000 : ℝ)) (Y := (7349524011341/10000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (914540593/1000000000 : ℝ)) (n' := (206439279/250000000 : ℝ)) (Ab := (193808299/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (11435603/12500000 : ℝ) ^ p + (99208763/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (11435603/12500000 : ℝ)) (y := (99208763/100000000 : ℝ)) (X := (3846470108679/25000000000000 : ℝ)) (Y := (338456536947/400000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99208763/100000000 : ℝ) ^ p + (11435603/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (99208763/100000000 : ℝ)) (y := (11435603/12500000 : ℝ)) (X := (338456536947/400000000000 : ℝ)) (Y := (3846470108679/25000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (190693587/100000000 : ℝ)) (τ := (11435603/12500000 : ℝ)) (σ := (99208763/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (775564985/826125603 : ℝ) ^ p + (271374189/275375201 : ℝ) ^ p := by
    exact cert_lt (x := (775564985/826125603 : ℝ)) (y := (271374189/275375201 : ℝ)) (X := (331182388759/1250000000000 : ℝ)) (Y := (7350541025351/10000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (11435603/12500000 : ℝ)) (n' := (826125603/1000000000 : ℝ)) (Ab := (155112997/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (228715967/250000000 : ℝ) ^ p + (248021137/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (228715967/250000000 : ℝ)) (y := (248021137/250000000 : ℝ)) (X := (307828180929/2000000000000 : ℝ)) (Y := (42304303060753/50000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248021137/250000000 : ℝ) ^ p + (228715967/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248021137/250000000 : ℝ)) (y := (228715967/250000000 : ℝ)) (X := (42304303060753/50000000000000 : ℝ)) (Y := (307828180929/2000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (29796069/15625000 : ℝ)) (τ := (228715967/250000000 : ℝ)) (σ := (248021137/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (775581836/826144319 : ℝ) ^ p + (814141283/826144319 : ℝ) ^ p := by
    exact cert_lt (x := (775581836/826144319 : ℝ)) (y := (814141283/826144319 : ℝ)) (X := (26494074153581/100000000000000 : ℝ)) (Y := (36752963301811/50000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (228715967/250000000 : ℝ)) (n' := (826144319/1000000000 : ℝ)) (Ab := (193895459/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (457432331/500000000 : ℝ) ^ p + (992084391/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (457432331/500000000 : ℝ)) (y := (992084391/1000000000 : ℝ)) (X := (3847922496239/25000000000000 : ℝ)) (Y := (42304162261643/50000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992084391/1000000000 : ℝ) ^ p + (457432331/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992084391/1000000000 : ℝ)) (y := (457432331/500000000 : ℝ)) (X := (42304162261643/50000000000000 : ℝ)) (Y := (3847922496239/25000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1906949053/1000000000 : ℝ)) (τ := (457432331/500000000 : ℝ)) (σ := (992084391/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (775582693/826145270 : ℝ) ^ p + (407071117/413072635 : ℝ) ^ p := by
    exact cert_lt (x := (775582693/826145270 : ℝ)) (y := (407071117/413072635 : ℝ)) (X := (13247024218307/50000000000000 : ℝ)) (Y := (9188244104993/12500000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (457432331/500000000 : ℝ)) (n' := (82614527/100000000 : ℝ)) (Ab := (775582693/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (914864703/1000000000 : ℝ) ^ p + (992084383/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (914864703/1000000000 : ℝ)) (y := (992084383/1000000000 : ℝ)) (X := (15391704491989/100000000000000 : ℝ)) (Y := (21152077543589/25000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992084383/1000000000 : ℝ) ^ p + (914864703/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992084383/1000000000 : ℝ)) (y := (914864703/1000000000 : ℝ)) (X := (21152077543589/25000000000000 : ℝ)) (Y := (15391704491989/100000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (953474543/500000000 : ℝ)) (τ := (914864703/1000000000 : ℝ)) (σ := (992084383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (258527579/275381773 : ℝ) ^ p + (271380761/275381773 : ℝ) ^ p := by
    exact cert_lt (x := (258527579/275381773 : ℝ)) (y := (271380761/275381773 : ℝ)) (X := (5298809399799/20000000000000 : ℝ)) (Y := (73505954191761/100000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (914864703/1000000000 : ℝ)) (n' := (826145319/1000000000 : ℝ)) (Ab := (775582737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (14294761/15625000 : ℝ) ^ p + (992084383/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14294761/15625000 : ℝ)) (y := (992084383/1000000000 : ℝ)) (X := (15391704845819/100000000000000 : ℝ)) (Y := (21152077543589/25000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992084383/1000000000 : ℝ) ^ p + (14294761/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (992084383/1000000000 : ℝ)) (y := (14294761/15625000 : ℝ)) (X := (21152077543589/25000000000000 : ℝ)) (Y := (15391704845819/100000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1906949087/1000000000 : ℝ)) (τ := (14294761/15625000 : ℝ)) (σ := (992084383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (55398767/59010380 : ℝ) ^ p + (203535571/206536330 : ℝ) ^ p := by
    exact cert_lt (x := (55398767/59010380 : ℝ)) (y := (203535571/206536330 : ℝ)) (X := (5298809408593/20000000000000 : ℝ)) (Y := (73505954219349/100000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (14294761/15625000 : ℝ)) (n' := (20653633/25000000 : ℝ)) (Ab := (387791369/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1906949087/1000000000 : ℝ)) (τ := (14294761/15625000 : ℝ)) (σ := (992084383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (14294761/15625000 : ℝ)) (n' := (20653633/25000000 : ℝ)) (Ab := (387791369/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1906949087/1000000000 : ℝ)) (τ := (14294761/15625000 : ℝ)) (σ := (992084383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (14294761/15625000 : ℝ)) (n' := (20653633/25000000 : ℝ)) (Ab := (387791369/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1906949087/1000000000 : ℝ)) (τ := (14294761/15625000 : ℝ)) (σ := (992084383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (14294761/15625000 : ℝ)) (n' := (20653633/25000000 : ℝ)) (Ab := (387791369/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1906949087/1000000000 : ℝ)) (τ := (14294761/15625000 : ℝ)) (σ := (992084383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (273488931/301267387 : ℝ) ^ p + (299266881/301267387 : ℝ) ^ p := by
    exact cert_lt (x := (273488931/301267387 : ℝ)) (y := (299266881/301267387 : ℝ)) (X := (32686424417/250000000000 : ℝ)) (Y := (21731357619509/25000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1102317361/1192395678 : ℝ) ^ p + (196732107/198732613 : ℝ) ^ p := by
    exact cert_lt (x := (1102317361/1192395678 : ℝ)) (y := (196732107/198732613 : ℝ)) (X := (2395826127439/12500000000000 : ℝ)) (Y := (80833391377691/100000000000000 : ℝ)) 673 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992084383/1000000000 : ℝ)) (U := (596197839/500000000 : ℝ)) (Ab := (820466793/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (14294761/15625000 : ℝ)) (σ := (992084383/1000000000 : ℝ)) (Ab := (1102317361/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab000
