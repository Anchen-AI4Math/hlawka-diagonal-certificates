import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 18, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab018 (p : ℝ) (hpa : (345/16 : ℝ) ≤ p) (hpb : p ≤ (691/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (106143982309/4709250000000 : ℝ) (1454737/125000000 : ℝ) (400000056511/1883700000000 : ℝ) (3033/2500 : ℝ) (242102571/125000000 : ℝ) (60522827/62500000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192612743/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5523/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4447/10000 : ℝ)
      else (7599/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5917/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (106143982309/4709250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1454737/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (14235481/15625000 : ℝ) ^ p + (49668409/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (14235481/15625000 : ℝ)) (y := (49668409/50000000 : ℝ)) (X := (3345943476813/25000000000000 : ℝ)) (Y := (43308121225991/50000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (49668409/50000000 : ℝ) ^ p + (14235481/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (49668409/50000000 : ℝ)) (y := (14235481/15625000 : ℝ)) (X := (43308121225991/50000000000000 : ℝ)) (Y := (3345943476813/25000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (476109741/250000000 : ℝ)) (τ := (14235481/15625000 : ℝ)) (σ := (49668409/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (128674382/136829083 : ℝ) ^ p + (404668301/410487249 : ℝ) ^ p := by
    exact cert_lt (x := (128674382/136829083 : ℝ)) (y := (404668301/410487249 : ℝ)) (X := (26530300088949/100000000000000 : ℝ)) (Y := (73469701304477/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (14235481/15625000 : ℝ)) (n' := (410487249/500000000 : ℝ)) (Ab := (193011573/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (114623223/125000000 : ℝ) ^ p + (992290153/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114623223/125000000 : ℝ)) (y := (992290153/1000000000 : ℝ)) (X := (1923877735593/12500000000000 : ℝ)) (Y := (42304497057803/50000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992290153/1000000000 : ℝ) ^ p + (114623223/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992290153/1000000000 : ℝ)) (y := (114623223/125000000 : ℝ)) (X := (42304497057803/50000000000000 : ℝ)) (Y := (1923877735593/12500000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1909275937/1000000000 : ℝ)) (τ := (114623223/125000000 : ℝ)) (σ := (992290153/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (778440433/828057262 : ℝ) ^ p + (408209683/414028631 : ℝ) ^ p := by
    exact cert_lt (x := (778440433/828057262 : ℝ)) (y := (408209683/414028631 : ℝ)) (X := (26334922770787/100000000000000 : ℝ)) (Y := (7366507862383/10000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (114623223/125000000 : ℝ)) (n' := (414028631/500000000 : ℝ)) (Ab := (778440433/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (18345569/20000000 : ℝ) ^ p + (496116159/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (18345569/20000000 : ℝ)) (y := (496116159/500000000 : ℝ)) (X := (7748722145147/50000000000000 : ℝ)) (Y := (84502570982657/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496116159/500000000 : ℝ) ^ p + (18345569/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (496116159/500000000 : ℝ)) (y := (18345569/20000000 : ℝ)) (X := (84502570982657/100000000000000 : ℝ)) (Y := (7748722145147/50000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (119344423/62500000 : ℝ)) (τ := (18345569/20000000 : ℝ)) (σ := (496116159/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (389377847/414203274 : ℝ) ^ p + (204192163/207101637 : ℝ) ^ p := by
    exact cert_lt (x := (389377847/414203274 : ℝ)) (y := (204192163/207101637 : ℝ)) (X := (3290670194943/12500000000000 : ℝ)) (Y := (73674639890543/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (18345569/20000000 : ℝ)) (n' := (207101637/250000000 : ℝ)) (Ab := (389377847/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (28665399/31250000 : ℝ) ^ p + (992229477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28665399/31250000 : ℝ)) (y := (992229477/1000000000 : ℝ)) (X := (15502668722817/100000000000000 : ℝ)) (Y := (42248673251437/50000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992229477/1000000000 : ℝ) ^ p + (28665399/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (992229477/1000000000 : ℝ)) (y := (28665399/31250000 : ℝ)) (X := (42248673251437/50000000000000 : ℝ)) (Y := (15502668722817/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (381904449/200000000 : ℝ)) (τ := (28665399/31250000 : ℝ)) (σ := (992229477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (778771115/828423634 : ℝ) ^ p + (408392869/414211817 : ℝ) ^ p := by
    exact cert_lt (x := (778771115/828423634 : ℝ)) (y := (408392869/414211817 : ℝ)) (X := (1645305856701/6250000000000 : ℝ)) (Y := (36837553710947/50000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (28665399/31250000 : ℝ)) (n' := (414211817/500000000 : ℝ)) (Ab := (155754223/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (229323367/250000000 : ℝ) ^ p + (496114669/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (229323367/250000000 : ℝ)) (y := (496114669/500000000 : ℝ)) (X := (484466380807/3125000000000 : ℝ)) (Y := (21124272723903/25000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496114669/500000000 : ℝ) ^ p + (229323367/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496114669/500000000 : ℝ)) (y := (229323367/250000000 : ℝ)) (X := (21124272723903/25000000000000 : ℝ)) (Y := (484466380807/3125000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (954761403/500000000 : ℝ)) (τ := (229323367/250000000 : ℝ)) (σ := (496114669/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (778771869/828424469 : ℝ) ^ p + (816786573/828424469 : ℝ) ^ p := by
    exact cert_lt (x := (778771869/828424469 : ℝ)) (y := (816786573/828424469 : ℝ)) (X := (26324871113303/100000000000000 : ℝ)) (Y := (2947005210797/4000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (229323367/250000000 : ℝ)) (n' := (828424469/1000000000 : ℝ)) (Ab := (778771869/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (917293503/1000000000 : ℝ) ^ p + (992229331/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917293503/1000000000 : ℝ)) (y := (992229331/1000000000 : ℝ)) (X := (15502936959079/100000000000000 : ℝ)) (Y := (84497078023323/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992229331/1000000000 : ℝ) ^ p + (917293503/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992229331/1000000000 : ℝ)) (y := (917293503/1000000000 : ℝ)) (X := (84497078023323/100000000000000 : ℝ)) (Y := (15502936959079/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (954761417/500000000 : ℝ)) (τ := (917293503/1000000000 : ℝ)) (σ := (992229331/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (778771907/828424511 : ℝ) ^ p + (816786615/828424511 : ℝ) ^ p := by
    exact cert_lt (x := (778771907/828424511 : ℝ)) (y := (816786615/828424511 : ℝ)) (X := (26324870031043/100000000000000 : ℝ)) (Y := (73675131419167/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (917293503/1000000000 : ℝ)) (n' := (828424511/1000000000 : ℝ)) (Ab := (778771907/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (14332711/15625000 : ℝ) ^ p + (992229331/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14332711/15625000 : ℝ)) (y := (992229331/1000000000 : ℝ)) (X := (1550293732403/10000000000000 : ℝ)) (Y := (84497078023323/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992229331/1000000000 : ℝ) ^ p + (14332711/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (992229331/1000000000 : ℝ)) (y := (14332711/15625000 : ℝ)) (X := (84497078023323/100000000000000 : ℝ)) (Y := (1550293732403/10000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (381904567/200000000 : ℝ)) (τ := (14332711/15625000 : ℝ)) (σ := (992229331/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (778771907/828424512 : ℝ) ^ p + (102098327/103553064 : ℝ) ^ p := by
    exact cert_lt (x := (778771907/828424512 : ℝ)) (y := (102098327/103553064 : ℝ)) (X := (26324869344857/100000000000000 : ℝ)) (Y := (7367513144653/10000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (14332711/15625000 : ℝ)) (n' := (12944133/15625000 : ℝ)) (Ab := (778771907/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (381904567/200000000 : ℝ)) (τ := (14332711/15625000 : ℝ)) (σ := (992229331/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (14332711/15625000 : ℝ)) (n' := (12944133/15625000 : ℝ)) (Ab := (778771907/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (381904567/200000000 : ℝ)) (τ := (14332711/15625000 : ℝ)) (σ := (992229331/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (14332711/15625000 : ℝ)) (n' := (12944133/15625000 : ℝ)) (Ab := (778771907/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (381904567/200000000 : ℝ)) (τ := (14332711/15625000 : ℝ)) (σ := (992229331/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (14332711/15625000 : ℝ)) (n' := (12944133/15625000 : ℝ)) (Ab := (778771907/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (381904567/200000000 : ℝ)) (τ := (14332711/15625000 : ℝ)) (σ := (992229331/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1644558385/1807387257 : ℝ) ^ p + (1795749361/1807387257 : ℝ) ^ p := by
    exact cert_lt (x := (1644558385/1807387257 : ℝ)) (y := (1795749361/1807387257 : ℝ)) (X := (13020114372689/100000000000000 : ℝ)) (Y := (86979885949293/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1104554212/1192612743 : ℝ) ^ p + (1180974847/1192612743 : ℝ) ^ p := by
    exact cert_lt (x := (1104554212/1192612743 : ℝ)) (y := (1180974847/1192612743 : ℝ)) (X := (19083593650841/100000000000000 : ℝ)) (Y := (80916407008671/100000000000000 : ℝ)) 691 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992229331/1000000000 : ℝ)) (U := (1192612743/1000000000 : ℝ)) (Ab := (328911677/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (14332711/15625000 : ℝ)) (σ := (992229331/1000000000 : ℝ)) (Ab := (276138553/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab018
