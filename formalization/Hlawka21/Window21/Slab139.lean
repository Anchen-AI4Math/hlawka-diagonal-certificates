import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 139, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab139 (p : ℝ) (hpa : (811/32 : ℝ) ≤ p) (hpb : p ≤ (203/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1040085609391/55350750000000 : ℝ) (2413979/250000000 : ℝ) (4000000664209/22140300000000 : ℝ) (3033/2500 : ℝ) (973053567/500000000 : ℝ) (121627599/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298534717/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1397/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(4673/10000 : ℝ)
      else (7821/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1040085609391/55350750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2413979/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (462481727/500000000 : ℝ) ^ p + (497078597/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (462481727/500000000 : ℝ)) (y := (497078597/500000000 : ℝ)) (X := (3454228541017/25000000000000 : ℝ)) (Y := (86183104799783/100000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497078597/500000000 : ℝ) ^ p + (462481727/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (497078597/500000000 : ℝ)) (y := (462481727/500000000 : ℝ)) (X := (86183104799783/100000000000000 : ℝ)) (Y := (3454228541017/25000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (239890081/125000000 : ℝ)) (τ := (462481727/500000000 : ℝ)) (σ := (497078597/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (790324637/833941641 : ℝ) ^ p + (824285725/833941641 : ℝ) ^ p := by
    exact cert_lt (x := (790324637/833941641 : ℝ)) (y := (824285725/833941641 : ℝ)) (X := (12792862082359/50000000000000 : ℝ)) (Y := (74414277048483/100000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462481727/500000000 : ℝ)) (n' := (833941641/1000000000 : ℝ)) (Ab := (790324637/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (930364311/1000000000 : ℝ) ^ p + (198628949/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (930364311/1000000000 : ℝ)) (y := (198628949/200000000 : ℝ)) (X := (16016622911803/100000000000000 : ℝ)) (Y := (83983395640489/100000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198628949/200000000 : ℝ) ^ p + (930364311/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198628949/200000000 : ℝ)) (y := (930364311/1000000000 : ℝ)) (X := (83983395640489/100000000000000 : ℝ)) (Y := (16016622911803/100000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (30054829/15625000 : ℝ)) (τ := (930364311/1000000000 : ℝ)) (σ := (198628949/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (796126095/840280141 : ℝ) ^ p + (830624225/840280141 : ℝ) ^ p := by
    exact cert_lt (x := (796126095/840280141 : ℝ)) (y := (830624225/840280141 : ℝ)) (X := (25418689113753/100000000000000 : ℝ)) (Y := (18645328080601/25000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (930364311/1000000000 : ℝ)) (n' := (840280141/1000000000 : ℝ)) (Ab := (159225219/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (116322239/125000000 : ℝ) ^ p + (496550557/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (116322239/125000000 : ℝ)) (y := (496550557/500000000 : ℝ)) (X := (4027548566701/25000000000000 : ℝ)) (Y := (41944911424571/50000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496550557/500000000 : ℝ) ^ p + (116322239/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496550557/500000000 : ℝ)) (y := (116322239/125000000 : ℝ)) (X := (41944911424571/50000000000000 : ℝ)) (Y := (4027548566701/25000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (961839513/500000000 : ℝ)) (τ := (116322239/125000000 : ℝ)) (σ := (496550557/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (132725804/140088347 : ℝ) ^ p + (415437083/420265041 : ℝ) ^ p := by
    exact cert_lt (x := (132725804/140088347 : ℝ)) (y := (415437083/420265041 : ℝ)) (X := (794129593021/3125000000000 : ℝ)) (Y := (18646963644459/25000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (116322239/125000000 : ℝ)) (n' := (420265041/500000000 : ℝ)) (Ab := (99544353/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (37223451/40000000 : ℝ) ^ p + (4965497/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (37223451/40000000 : ℝ)) (y := (4965497/5000000 : ℝ)) (X := (1007116779683/6250000000000 : ℝ)) (Y := (41943074490599/50000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (4965497/5000000 : ℝ) ^ p + (37223451/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (4965497/5000000 : ℝ)) (y := (37223451/40000000 : ℝ)) (X := (41943074490599/50000000000000 : ℝ)) (Y := (1007116779683/6250000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (76947427/40000000 : ℝ)) (τ := (37223451/40000000 : ℝ)) (σ := (4965497/5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (796363778/840539867 : ℝ) ^ p + (830883951/840539867 : ℝ) ^ p := by
    exact cert_lt (x := (796363778/840539867 : ℝ)) (y := (830883951/840539867 : ℝ)) (X := (6352972627611/25000000000000 : ℝ)) (Y := (37294055317113/50000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (37223451/40000000 : ℝ)) (n' := (840539867/1000000000 : ℝ)) (Ab := (398181889/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (930586603/1000000000 : ℝ) ^ p + (993099333/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (930586603/1000000000 : ℝ)) (y := (993099333/1000000000 : ℝ)) (X := (16114012595153/100000000000000 : ℝ)) (Y := (83886005373397/100000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993099333/1000000000 : ℝ) ^ p + (930586603/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993099333/1000000000 : ℝ)) (y := (930586603/1000000000 : ℝ)) (X := (83886005373397/100000000000000 : ℝ)) (Y := (16114012595153/100000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (120230371/62500000 : ℝ)) (τ := (930586603/1000000000 : ℝ)) (σ := (993099333/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (72396739/76412750 : ℝ) ^ p + (415442167/420270125 : ℝ) ^ p := by
    exact cert_lt (x := (72396739/76412750 : ℝ)) (y := (415442167/420270125 : ℝ)) (X := (5082376179709/20000000000000 : ℝ)) (Y := (18647030164141/25000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (930586603/1000000000 : ℝ)) (n' := (3362161/4000000 : ℝ)) (Ab := (796364129/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (116323327/125000000 : ℝ) ^ p + (99309933/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (116323327/125000000 : ℝ)) (y := (99309933/100000000 : ℝ)) (X := (16114018307261/100000000000000 : ℝ)) (Y := (41942999471601/50000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99309933/100000000 : ℝ) ^ p + (116323327/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (99309933/100000000 : ℝ)) (y := (116323327/125000000 : ℝ)) (X := (41942999471601/50000000000000 : ℝ)) (Y := (16114018307261/100000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (961842973/500000000 : ℝ)) (τ := (116323327/125000000 : ℝ)) (σ := (99309933/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (796364142/840540265 : ℝ) ^ p + (830884349/840540265 : ℝ) ^ p := by
    exact cert_lt (x := (796364142/840540265 : ℝ)) (y := (830884349/840540265 : ℝ)) (X := (12705939958729/50000000000000 : ℝ)) (Y := (18647030262271/25000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (116323327/125000000 : ℝ)) (n' := (168108053/200000000 : ℝ)) (Ab := (398182071/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (961842973/500000000 : ℝ)) (τ := (116323327/125000000 : ℝ)) (σ := (99309933/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (116323327/125000000 : ℝ)) (n' := (168108053/200000000 : ℝ)) (Ab := (398182071/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (961842973/500000000 : ℝ)) (τ := (116323327/125000000 : ℝ)) (σ := (99309933/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (116323327/125000000 : ℝ)) (n' := (168108053/200000000 : ℝ)) (Ab := (398182071/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (961842973/500000000 : ℝ)) (τ := (116323327/125000000 : ℝ)) (σ := (99309933/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (116323327/125000000 : ℝ)) (n' := (168108053/200000000 : ℝ)) (Ab := (398182071/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (961842973/500000000 : ℝ)) (τ := (116323327/125000000 : ℝ)) (σ := (99309933/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (116323327/125000000 : ℝ)) (n' := (168108053/200000000 : ℝ)) (Ab := (398182071/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (961842973/500000000 : ℝ)) (τ := (116323327/125000000 : ℝ)) (σ := (99309933/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1664917101/1805861132 : ℝ) ^ p + (449051304/451465283 : ℝ) ^ p := by
    exact cert_lt (x := (1664917101/1805861132 : ℝ)) (y := (449051304/451465283 : ℝ)) (X := (2543912568789/20000000000000 : ℝ)) (Y := (8728043744773/10000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1117593623/1194138868 : ℝ) ^ p + (296120738/298534717 : ℝ) ^ p := by
    exact cert_lt (x := (1117593623/1194138868 : ℝ)) (y := (296120738/298534717 : ℝ)) (X := (18618209827149/100000000000000 : ℝ)) (Y := (40690895390269/50000000000000 : ℝ)) 203 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99309933/100000000 : ℝ)) (U := (298534717/250000000 : ℝ)) (Ab := (1664917101/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (116323327/125000000 : ℝ)) (σ := (99309933/100000000 : ℝ)) (Ab := (1117593623/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab139
