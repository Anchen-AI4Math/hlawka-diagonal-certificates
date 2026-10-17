import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 157, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab157 (p : ℝ) (hpa : (829/32 : ℝ) ≤ p) (hpb : p ≤ (415/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2074874106143/113158500000000 : ℝ) (941661/100000000 : ℝ) (4000000678951/22631700000000 : ℝ) (3033/2500 : ℝ) (973630173/500000000 : ℝ) (973598787/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149295659/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11193/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(47/100 : ℝ)
      else (981/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11863/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2074874106143/113158500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (941661/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (926668703/1000000000 : ℝ) ^ p + (994259531/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926668703/1000000000 : ℝ)) (y := (994259531/1000000000 : ℝ)) (X := (866930177261/6250000000000 : ℝ)) (Y := (4306456878869/5000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994259531/1000000000 : ℝ) ^ p + (926668703/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994259531/1000000000 : ℝ)) (y := (926668703/1000000000 : ℝ)) (X := (4306456878869/5000000000000 : ℝ)) (Y := (866930177261/6250000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (960464117/500000000 : ℝ)) (τ := (926668703/1000000000 : ℝ)) (σ := (994259531/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (792581163/835492511 : ℝ) ^ p + (118010843/119356073 : ℝ) ^ p := by
    exact cert_lt (x := (792581163/835492511 : ℝ)) (y := (118010843/119356073 : ℝ)) (X := (12735968895883/50000000000000 : ℝ)) (Y := (186320158929/250000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (926668703/1000000000 : ℝ)) (n' := (835492511/1000000000 : ℝ)) (Ab := (792581163/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931993287/1000000000 : ℝ) ^ p + (993257951/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931993287/1000000000 : ℝ)) (y := (993257951/1000000000 : ℝ)) (X := (4023315581237/25000000000000 : ℝ)) (Y := (83906755568351/100000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993257951/1000000000 : ℝ) ^ p + (931993287/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993257951/1000000000 : ℝ)) (y := (931993287/1000000000 : ℝ)) (X := (83906755568351/100000000000000 : ℝ)) (Y := (4023315581237/25000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (962625619/500000000 : ℝ)) (τ := (931993287/1000000000 : ℝ)) (σ := (993257951/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (199574143/210431533 : ℝ) ^ p + (416154761/420863066 : ℝ) ^ p := by
    exact cert_lt (x := (199574143/210431533 : ℝ)) (y := (416154761/420863066 : ℝ)) (X := (12654288073881/50000000000000 : ℝ)) (Y := (233410702953/312500000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931993287/1000000000 : ℝ)) (n' := (210431533/250000000 : ℝ)) (Ab := (199574143/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (466098873/500000000 : ℝ) ^ p + (496608011/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (466098873/500000000 : ℝ)) (y := (496608011/500000000 : ℝ)) (X := (3237017174359/20000000000000 : ℝ)) (Y := (83814933108599/100000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496608011/500000000 : ℝ) ^ p + (466098873/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496608011/500000000 : ℝ)) (y := (466098873/500000000 : ℝ)) (X := (83814933108599/100000000000000 : ℝ)) (Y := (3237017174359/20000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (240676721/125000000 : ℝ)) (τ := (466098873/500000000 : ℝ)) (σ := (496608011/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (798515366/841964799 : ℝ) ^ p + (277516063/280654933 : ℝ) ^ p := by
    exact cert_lt (x := (798515366/841964799 : ℝ)) (y := (277516063/280654933 : ℝ)) (X := (25302363041999/100000000000000 : ℝ)) (Y := (37348819137233/50000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (466098873/500000000 : ℝ)) (n' := (841964799/1000000000 : ℝ)) (Ab := (399257683/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (932205521/1000000000 : ℝ) ^ p + (496607211/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (932205521/1000000000 : ℝ)) (y := (496607211/500000000 : ℝ)) (X := (8094293792753/50000000000000 : ℝ)) (Y := (83811431101199/100000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496607211/500000000 : ℝ) ^ p + (932205521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496607211/500000000 : ℝ)) (y := (932205521/1000000000 : ℝ)) (X := (83811431101199/100000000000000 : ℝ)) (Y := (8094293792753/50000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1925419943/1000000000 : ℝ)) (τ := (932205521/1000000000 : ℝ)) (σ := (496607211/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (798523685/841973874 : ℝ) ^ p + (19822792/20046997 : ℝ) ^ p := by
    exact cert_lt (x := (798523685/841973874 : ℝ)) (y := (19822792/20046997 : ℝ)) (X := (12651063301653/50000000000000 : ℝ)) (Y := (74697874468469/100000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (932205521/1000000000 : ℝ)) (n' := (420986937/500000000 : ℝ)) (Ab := (159704737/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (116525727/125000000 : ℝ) ^ p + (993214361/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116525727/125000000 : ℝ)) (y := (993214361/1000000000 : ℝ)) (X := (16188720462297/100000000000000 : ℝ)) (Y := (83811297589951/100000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993214361/1000000000 : ℝ) ^ p + (116525727/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993214361/1000000000 : ℝ)) (y := (116525727/125000000 : ℝ)) (X := (83811297589951/100000000000000 : ℝ)) (Y := (16188720462297/100000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1925420177/1000000000 : ℝ)) (τ := (116525727/125000000 : ℝ)) (σ := (993214361/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (798524001/841974218 : ℝ) ^ p + (416278804/420987109 : ℝ) ^ p := by
    exact cert_lt (x := (798524001/841974218 : ℝ)) (y := (416278804/420987109 : ℝ)) (X := (25302118181041/100000000000000 : ℝ)) (Y := (1167154428463/1562500000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (116525727/125000000 : ℝ)) (n' := (420987109/500000000 : ℝ)) (Ab := (798524001/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (932205827/1000000000 : ℝ) ^ p + (993214359/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (932205827/1000000000 : ℝ)) (y := (993214359/1000000000 : ℝ)) (X := (3237745083409/20000000000000 : ℝ)) (Y := (83811293212537/100000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993214359/1000000000 : ℝ) ^ p + (932205827/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993214359/1000000000 : ℝ)) (y := (932205827/1000000000 : ℝ)) (X := (83811293212537/100000000000000 : ℝ)) (Y := (3237745083409/20000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962710093/500000000 : ℝ)) (τ := (932205827/1000000000 : ℝ)) (σ := (993214359/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (798524012/841974231 : ℝ) ^ p + (39645601/40094011 : ℝ) ^ p := by
    exact cert_lt (x := (798524012/841974231 : ℝ)) (y := (39645601/40094011 : ℝ)) (X := (12651058544341/50000000000000 : ℝ)) (Y := (37348941879989/50000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (932205827/1000000000 : ℝ)) (n' := (841974231/1000000000 : ℝ)) (Ab := (199631003/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962710093/500000000 : ℝ)) (τ := (932205827/1000000000 : ℝ)) (σ := (993214359/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (932205827/1000000000 : ℝ)) (n' := (841974231/1000000000 : ℝ)) (Ab := (199631003/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962710093/500000000 : ℝ)) (τ := (932205827/1000000000 : ℝ)) (σ := (993214359/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (932205827/1000000000 : ℝ)) (n' := (841974231/1000000000 : ℝ)) (Ab := (199631003/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962710093/500000000 : ℝ)) (τ := (932205827/1000000000 : ℝ)) (σ := (993214359/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (932205827/1000000000 : ℝ)) (n' := (841974231/1000000000 : ℝ)) (Ab := (199631003/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962710093/500000000 : ℝ)) (τ := (932205827/1000000000 : ℝ)) (σ := (993214359/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (932205827/1000000000 : ℝ)) (n' := (841974231/1000000000 : ℝ)) (Ab := (199631003/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962710093/500000000 : ℝ)) (τ := (932205827/1000000000 : ℝ)) (σ := (993214359/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (208432244/225704341 : ℝ) ^ p + (898109059/902817364 : ℝ) ^ p := by
    exact cert_lt (x := (208432244/225704341 : ℝ)) (y := (898109059/902817364 : ℝ)) (X := (12682671255943/100000000000000 : ℝ)) (Y := (3492693164733/4000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1119278065/1194365272 : ℝ) ^ p + (592474331/597182636 : ℝ) ^ p := by
    exact cert_lt (x := (1119278065/1194365272 : ℝ)) (y := (592474331/597182636 : ℝ)) (X := (1856025400461/10000000000000 : ℝ)) (Y := (40719873370933/50000000000000 : ℝ)) 415 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993214359/1000000000 : ℝ)) (U := (149295659/125000000 : ℝ)) (Ab := (52108061/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (932205827/1000000000 : ℝ)) (σ := (993214359/1000000000 : ℝ)) (Ab := (223855613/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab157
