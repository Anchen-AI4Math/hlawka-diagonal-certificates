import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 62, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab062 (p : ℝ) (hpa : (239/8 : ℝ) ≤ p) (hpb : p ≤ (479/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (715295959703/52938500000000 : ℝ) (1382899/200000000 : ℝ) (1600000317631/10587700000000 : ℝ) (591/500 : ℝ) (244278209/125000000 : ℝ) (977065507/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (28943821/25000000 : ℝ)) ∧
    (∀ j i, if j = i then -(109/100 : ℝ) ≤ X j i ∧ X j i ≤ -(5599/10000 : ℝ)
      else (516/625 : ℝ) ≤ X j i ∧ X j i ≤ (5749/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (715295959703/52938500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1382899/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (235565649/250000000 : ℝ) ^ p + (198770529/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (235565649/250000000 : ℝ)) (y := (198770529/200000000 : ℝ)) (X := (16856709597841/100000000000000 : ℝ)) (Y := (16628662043699/20000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198770529/200000000 : ℝ) ^ p + (235565649/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198770529/200000000 : ℝ)) (y := (235565649/250000000 : ℝ)) (X := (16628662043699/20000000000000 : ℝ)) (Y := (16856709597841/100000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1936115241/1000000000 : ℝ)) (τ := (235565649/250000000 : ℝ)) (σ := (198770529/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (825582997/869401597 : ℝ) ^ p + (862487102/869401597 : ℝ) ^ p := by
    exact cert_lt (x := (825582997/869401597 : ℝ)) (y := (862487102/869401597 : ℝ)) (X := (10631215643269/50000000000000 : ℝ)) (Y := (19684392425747/25000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (235565649/250000000 : ℝ)) (n' := (869401597/1000000000 : ℝ)) (Ab := (825582997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (94546377/100000000 : ℝ) ^ p + (248281429/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (94546377/100000000 : ℝ)) (y := (248281429/250000000 : ℝ)) (X := (1166135332247/6250000000000 : ℝ)) (Y := (4067092687009/5000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248281429/250000000 : ℝ) ^ p + (94546377/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248281429/250000000 : ℝ)) (y := (94546377/100000000 : ℝ)) (X := (4067092687009/5000000000000 : ℝ)) (Y := (1166135332247/6250000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (969294743/500000000 : ℝ)) (τ := (94546377/100000000 : ℝ)) (σ := (248281429/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (414474571/436527558 : ℝ) ^ p + (866140621/873055116 : ℝ) ^ p := by
    exact cert_lt (x := (414474571/436527558 : ℝ)) (y := (866140621/873055116 : ℝ)) (X := (10591655788183/50000000000000 : ℝ)) (Y := (39408344819601/50000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (94546377/100000000 : ℝ)) (n' := (218263779/250000000 : ℝ)) (Ab := (414474571/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (189109899/200000000 : ℝ) ^ p + (248276257/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (189109899/200000000 : ℝ)) (y := (248276257/250000000 : ℝ)) (X := (18708878037589/100000000000000 : ℝ)) (Y := (16258228295581/20000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248276257/250000000 : ℝ) ^ p + (189109899/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248276257/250000000 : ℝ)) (y := (189109899/200000000 : ℝ)) (X := (16258228295581/20000000000000 : ℝ)) (Y := (18708878037589/100000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1938654523/1000000000 : ℝ)) (τ := (189109899/200000000 : ℝ)) (σ := (248276257/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (75367193/79377526 : ℝ) ^ p + (866238291/873152786 : ℝ) ^ p := by
    exact cert_lt (x := (75367193/79377526 : ℝ)) (y := (866238291/873152786 : ℝ)) (X := (84724817583/400000000000 : ℝ)) (Y := (39409398362781/50000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (189109899/200000000 : ℝ)) (n' := (436576393/500000000 : ℝ)) (Ab := (829039123/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (472775889/500000000 : ℝ) ^ p + (248276119/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (472775889/500000000 : ℝ)) (y := (248276119/250000000 : ℝ)) (X := (9355115210899/50000000000000 : ℝ)) (Y := (81289788785171/100000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248276119/250000000 : ℝ) ^ p + (472775889/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248276119/250000000 : ℝ)) (y := (472775889/500000000 : ℝ)) (X := (81289788785171/100000000000000 : ℝ)) (Y := (9355115210899/50000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (969328127/500000000 : ℝ)) (τ := (472775889/500000000 : ℝ)) (σ := (248276119/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (829041519/873155387 : ℝ) ^ p + (866240892/873155387 : ℝ) ^ p := by
    exact cert_lt (x := (829041519/873155387 : ℝ)) (y := (866240892/873155387 : ℝ)) (X := (21181148107549/100000000000000 : ℝ)) (Y := (15763770566521/20000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (472775889/500000000 : ℝ)) (n' := (873155387/1000000000 : ℝ)) (Ab := (829041519/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (5909699/6250000 : ℝ) ^ p + (993104461/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (5909699/6250000 : ℝ)) (y := (993104461/1000000000 : ℝ)) (X := (18710267150151/100000000000000 : ℝ)) (Y := (127015237543/156250000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993104461/1000000000 : ℝ) ^ p + (5909699/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (993104461/1000000000 : ℝ)) (y := (5909699/6250000 : ℝ)) (X := (127015237543/156250000000 : ℝ)) (Y := (18710267150151/100000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1938656301/1000000000 : ℝ)) (τ := (5909699/6250000 : ℝ)) (σ := (993104461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (829041585/873155458 : ℝ) ^ p + (123748709/124736494 : ℝ) ^ p := by
    exact cert_lt (x := (829041585/873155458 : ℝ)) (y := (123748709/124736494 : ℝ)) (X := (5295286756713/25000000000000 : ℝ)) (Y := (39409427182083/50000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (5909699/6250000 : ℝ)) (n' := (436577729/500000000 : ℝ)) (Ab := (165808317/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (945551841/1000000000 : ℝ) ^ p + (993104461/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (945551841/1000000000 : ℝ)) (y := (993104461/1000000000 : ℝ)) (X := (1169391733909/6250000000000 : ℝ)) (Y := (127015237543/156250000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993104461/1000000000 : ℝ) ^ p + (945551841/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993104461/1000000000 : ℝ)) (y := (945551841/1000000000 : ℝ)) (X := (127015237543/156250000000 : ℝ)) (Y := (1169391733909/6250000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (969328151/500000000 : ℝ)) (τ := (945551841/1000000000 : ℝ)) (σ := (993104461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (829041586/873155459 : ℝ) ^ p + (866240964/873155459 : ℝ) ^ p := by
    exact cert_lt (x := (829041586/873155459 : ℝ)) (y := (866240964/873155459 : ℝ)) (X := (4236229413099/20000000000000 : ℝ)) (Y := (78818854385737/100000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (945551841/1000000000 : ℝ)) (n' := (873155459/1000000000 : ℝ)) (Ab := (414520793/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (969328151/500000000 : ℝ)) (τ := (945551841/1000000000 : ℝ)) (σ := (993104461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (945551841/1000000000 : ℝ)) (n' := (873155459/1000000000 : ℝ)) (Ab := (414520793/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (969328151/500000000 : ℝ)) (τ := (945551841/1000000000 : ℝ)) (σ := (993104461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (945551841/1000000000 : ℝ)) (n' := (873155459/1000000000 : ℝ)) (Ab := (414520793/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (969328151/500000000 : ℝ)) (τ := (945551841/1000000000 : ℝ)) (σ := (993104461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (945551841/1000000000 : ℝ)) (n' := (873155459/1000000000 : ℝ)) (Ab := (414520793/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (969328151/500000000 : ℝ)) (τ := (945551841/1000000000 : ℝ)) (σ := (993104461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (945551841/1000000000 : ℝ)) (n' := (873155459/1000000000 : ℝ)) (Ab := (414520793/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (969328151/500000000 : ℝ)) (τ := (945551841/1000000000 : ℝ)) (σ := (993104461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (854721207/921123580 : ℝ) ^ p + (21592149/21673496 : ℝ) ^ p := by
    exact cert_lt (x := (854721207/921123580 : ℝ)) (y := (21592149/21673496 : ℝ)) (X := (2661755963201/25000000000000 : ℝ)) (Y := (22338244109879/25000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (108994503/115775284 : ℝ) ^ p + (230167669/231550568 : ℝ) ^ p := by
    exact cert_lt (x := (108994503/115775284 : ℝ)) (y := (230167669/231550568 : ℝ)) (X := (3283450030089/20000000000000 : ℝ)) (Y := (16716550137419/20000000000000 : ℝ)) 479 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993104461/1000000000 : ℝ)) (U := (28943821/25000000 : ℝ)) (Ab := (854721207/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (945551841/1000000000 : ℝ)) (σ := (993104461/1000000000 : ℝ)) (Ab := (108994503/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab062
