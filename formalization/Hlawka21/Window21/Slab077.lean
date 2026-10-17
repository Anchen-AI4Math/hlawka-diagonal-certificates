import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 77, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab077 (p : ℝ) (hpa : (749/32 : ℝ) ≤ p) (hpb : p ≤ (375/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (131271776387/6389906250000 : ℝ) (165321/15625000 : ℝ) (4000000613431/20447700000000 : ℝ) (3033/2500 : ℝ) (24271469/12500000 : ℝ) (485410213/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298337869/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5557/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4567/10000 : ℝ)
      else (7717/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (131271776387/6389906250000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (165321/15625000 : ℝ) := by norm_num
  have pc0 : 1 < (918432253/1000000000 : ℝ) ^ p + (198755297/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (918432253/1000000000 : ℝ)) (y := (198755297/200000000 : ℝ)) (X := (13611846111923/100000000000000 : ℝ)) (Y := (86388172051327/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198755297/200000000 : ℝ) ^ p + (918432253/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198755297/200000000 : ℝ)) (y := (918432253/1000000000 : ℝ)) (X := (86388172051327/100000000000000 : ℝ)) (Y := (13611846111923/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (956104369/500000000 : ℝ)) (τ := (918432253/1000000000 : ℝ)) (σ := (198755297/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (260569678/275973011 : ℝ) ^ p + (272446163/275973011 : ℝ) ^ p := by
    exact cert_lt (x := (260569678/275973011 : ℝ)) (y := (272446163/275973011 : ℝ)) (X := (1626614539429/6250000000000 : ℝ)) (Y := (73974168450473/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (918432253/1000000000 : ℝ)) (n' := (827919033/1000000000 : ℝ)) (Ab := (390854517/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (462049613/500000000 : ℝ) ^ p + (992728069/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462049613/500000000 : ℝ)) (y := (992728069/1000000000 : ℝ)) (X := (15722798174411/100000000000000 : ℝ)) (Y := (84277218342069/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992728069/1000000000 : ℝ) ^ p + (462049613/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992728069/1000000000 : ℝ)) (y := (462049613/500000000 : ℝ)) (X := (84277218342069/100000000000000 : ℝ)) (Y := (15722798174411/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (383365459/200000000 : ℝ)) (τ := (462049613/500000000 : ℝ)) (σ := (992728069/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (787813875/834632903 : ℝ) ^ p + (63388643/64202531 : ℝ) ^ p := by
    exact cert_lt (x := (787813875/834632903 : ℝ)) (y := (63388643/64202531 : ℝ)) (X := (12922540634261/50000000000000 : ℝ)) (Y := (14830984021451/20000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (462049613/500000000 : ℝ)) (n' := (834632903/1000000000 : ℝ)) (Ab := (6302511/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (184869817/200000000 : ℝ) ^ p + (992677813/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184869817/200000000 : ℝ)) (y := (992677813/1000000000 : ℝ)) (X := (988921079519/6250000000000 : ℝ)) (Y := (5261079995381/6250000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992677813/1000000000 : ℝ) ^ p + (184869817/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992677813/1000000000 : ℝ)) (y := (184869817/200000000 : ℝ)) (X := (5261079995381/6250000000000 : ℝ)) (Y := (988921079519/6250000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958513449/500000000 : ℝ)) (τ := (184869817/200000000 : ℝ)) (σ := (992677813/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (788082147/834927992 : ℝ) ^ p + (103043431/104365999 : ℝ) ^ p := by
    exact cert_lt (x := (788082147/834927992 : ℝ)) (y := (103043431/104365999 : ℝ)) (X := (25837193392507/100000000000000 : ℝ)) (Y := (37081403723571/50000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (184869817/200000000 : ℝ)) (n' := (104365999/125000000 : ℝ)) (Ab := (788082147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (184871997/200000000 : ℝ) ^ p + (248168903/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (184871997/200000000 : ℝ)) (y := (248168903/250000000 : ℝ)) (X := (3956777722553/25000000000000 : ℝ)) (Y := (84172905640873/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248168903/250000000 : ℝ) ^ p + (184871997/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248168903/250000000 : ℝ)) (y := (184871997/200000000 : ℝ)) (X := (84172905640873/100000000000000 : ℝ)) (Y := (3956777722553/25000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1917035597/1000000000 : ℝ)) (τ := (184871997/200000000 : ℝ)) (σ := (248168903/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (788093849/834940863 : ℝ) ^ p + (91595591/92771207 : ℝ) ^ p := by
    exact cert_lt (x := (788093849/834940863 : ℝ)) (y := (91595591/92771207 : ℝ)) (X := (25836850051057/100000000000000 : ℝ)) (Y := (37081575681691/50000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (184871997/200000000 : ℝ)) (n' := (834940863/1000000000 : ℝ)) (Ab := (788093849/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (924360461/1000000000 : ℝ) ^ p + (248168879/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (924360461/1000000000 : ℝ)) (y := (248168879/250000000 : ℝ)) (X := (7913650955637/50000000000000 : ℝ)) (Y := (10521589356831/12500000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248168879/250000000 : ℝ) ^ p + (924360461/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248168879/250000000 : ℝ)) (y := (924360461/1000000000 : ℝ)) (X := (10521589356831/12500000000000 : ℝ)) (Y := (7913650955637/50000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1917035977/1000000000 : ℝ)) (τ := (924360461/1000000000 : ℝ)) (σ := (248168879/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (157618872/166988285 : ℝ) ^ p + (824360881/834941425 : ℝ) ^ p := by
    exact cert_lt (x := (157618872/166988285 : ℝ)) (y := (824360881/834941425 : ℝ)) (X := (25836835092971/100000000000000 : ℝ)) (Y := (4635197898747/6250000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (924360461/1000000000 : ℝ)) (n' := (33397657/40000000 : ℝ)) (Ab := (19702359/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924360481/1000000000 : ℝ) ^ p + (124084439/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (924360481/1000000000 : ℝ)) (y := (124084439/125000000 : ℝ)) (X := (15827309937417/100000000000000 : ℝ)) (Y := (84172706905231/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124084439/125000000 : ℝ) ^ p + (924360481/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124084439/125000000 : ℝ)) (y := (924360481/1000000000 : ℝ)) (X := (84172706905231/100000000000000 : ℝ)) (Y := (15827309937417/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917035993/1000000000 : ℝ)) (τ := (924360481/1000000000 : ℝ)) (σ := (124084439/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (788094381/834941449 : ℝ) ^ p + (824360905/834941449 : ℝ) ^ p := by
    exact cert_lt (x := (788094381/834941449 : ℝ)) (y := (824360905/834941449 : ℝ)) (X := (1291841691127/5000000000000 : ℝ)) (Y := (18540791755307/25000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924360481/1000000000 : ℝ)) (n' := (834941449/1000000000 : ℝ)) (Ab := (788094381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (462180241/500000000 : ℝ) ^ p + (124084439/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (462180241/500000000 : ℝ)) (y := (124084439/125000000 : ℝ)) (X := (633092413549/4000000000000 : ℝ)) (Y := (84172706905231/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124084439/125000000 : ℝ) ^ p + (462180241/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124084439/125000000 : ℝ)) (y := (462180241/500000000 : ℝ)) (X := (84172706905231/100000000000000 : ℝ)) (Y := (633092413549/4000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (958517997/500000000 : ℝ)) (τ := (462180241/500000000 : ℝ)) (σ := (124084439/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (394047191/417470725 : ℝ) ^ p + (412180453/417470725 : ℝ) ^ p := by
    exact cert_lt (x := (394047191/417470725 : ℝ)) (y := (412180453/417470725 : ℝ)) (X := (6459208466413/25000000000000 : ℝ)) (Y := (18540791761987/25000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (462180241/500000000 : ℝ)) (n' := (16698829/20000000 : ℝ)) (Ab := (394047191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (958517997/500000000 : ℝ)) (τ := (462180241/500000000 : ℝ)) (σ := (124084439/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (462180241/500000000 : ℝ)) (n' := (16698829/20000000 : ℝ)) (Ab := (394047191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (958517997/500000000 : ℝ)) (τ := (462180241/500000000 : ℝ)) (σ := (124084439/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (462180241/500000000 : ℝ)) (n' := (16698829/20000000 : ℝ)) (Ab := (394047191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (958517997/500000000 : ℝ)) (τ := (462180241/500000000 : ℝ)) (σ := (124084439/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (462180241/500000000 : ℝ)) (n' := (16698829/20000000 : ℝ)) (Ab := (394047191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (958517997/500000000 : ℝ)) (τ := (462180241/500000000 : ℝ)) (σ := (124084439/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (413817829/451662131 : ℝ) ^ p + (449016995/451662131 : ℝ) ^ p := by
    exact cert_lt (x := (413817829/451662131 : ℝ)) (y := (449016995/451662131 : ℝ)) (X := (514434351243/4000000000000 : ℝ)) (Y := (87139141530919/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (555657305/596675738 : ℝ) ^ p + (295692733/298337869 : ℝ) ^ p := by
    exact cert_lt (x := (555657305/596675738 : ℝ)) (y := (295692733/298337869 : ℝ)) (X := (1883850641181/10000000000000 : ℝ)) (Y := (81161494043657/100000000000000 : ℝ)) 375 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124084439/125000000 : ℝ)) (U := (298337869/250000000 : ℝ)) (Ab := (413817829/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (462180241/500000000 : ℝ)) (σ := (124084439/125000000 : ℝ)) (Ab := (111131461/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab077
