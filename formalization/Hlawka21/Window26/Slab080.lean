import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 80, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab080 (p : ℝ) (hpa : (31 : ℝ) ≤ p) (hpb : p ≤ (497/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (44515020929/3433250000000 : ℝ) (1657379/250000000 : ℝ) (200000041199/1373300000000 : ℝ) (591/500 : ℝ) (244483133/125000000 : ℝ) (122236067/125000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158385283/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(683/625 : ℝ) ≤ X j i ∧ X j i ≤ -(5631/10000 : ℝ)
      else (8289/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11507/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (44515020929/3433250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1657379/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (236111853/250000000 : ℝ) ^ p + (994041853/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236111853/250000000 : ℝ)) (y := (994041853/1000000000 : ℝ)) (X := (847090522657/5000000000000 : ℝ)) (Y := (83058210482303/100000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994041853/1000000000 : ℝ) ^ p + (236111853/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (994041853/1000000000 : ℝ)) (y := (236111853/250000000 : ℝ)) (X := (83058210482303/100000000000000 : ℝ)) (Y := (847090522657/5000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (387697853/200000000 : ℝ)) (τ := (236111853/250000000 : ℝ)) (σ := (994041853/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (828603409/871132294 : ℝ) ^ p + (432251389/435566147 : ℝ) ^ p := by
    exact cert_lt (x := (828603409/871132294 : ℝ)) (y := (432251389/435566147 : ℝ)) (X := (21124287479459/100000000000000 : ℝ)) (Y := (3155028535289/4000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (236111853/250000000 : ℝ)) (n' := (435566147/500000000 : ℝ)) (Ab := (828603409/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (189512341/200000000 : ℝ) ^ p + (3880201/3906250 : ℝ) ^ p := by
    exact cert_lt (x := (189512341/200000000 : ℝ)) (y := (3880201/3906250 : ℝ)) (X := (2345743405313/12500000000000 : ℝ)) (Y := (40617036828149/50000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (3880201/3906250 : ℝ) ^ p + (189512341/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (3880201/3906250 : ℝ)) (y := (189512341/200000000 : ℝ)) (X := (40617036828149/50000000000000 : ℝ)) (Y := (2345743405313/12500000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1940893161/1000000000 : ℝ)) (τ := (189512341/200000000 : ℝ)) (σ := (3880201/3906250 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (138646071/145779161 : ℝ) ^ p + (434022725/437337483 : ℝ) ^ p := by
    exact cert_lt (x := (138646071/145779161 : ℝ)) (y := (434022725/437337483 : ℝ)) (X := (2631019129187/12500000000000 : ℝ)) (Y := (78951847997311/100000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (189512341/200000000 : ℝ)) (n' := (437337483/500000000 : ℝ)) (Ab := (415938213/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (947641293/1000000000 : ℝ) ^ p + (124164019/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (947641293/1000000000 : ℝ)) (y := (124164019/125000000 : ℝ)) (X := (9407484867531/50000000000000 : ℝ)) (Y := (2029626263537/2500000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124164019/125000000 : ℝ) ^ p + (947641293/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124164019/125000000 : ℝ)) (y := (947641293/1000000000 : ℝ)) (X := (2029626263537/2500000000000 : ℝ)) (Y := (9407484867531/50000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (388190689/200000000 : ℝ)) (τ := (947641293/1000000000 : ℝ)) (σ := (124164019/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (11092799/11663538 : ℝ) ^ p + (434067917/437382675 : ℝ) ^ p := by
    exact cert_lt (x := (11092799/11663538 : ℝ)) (y := (434067917/437382675 : ℝ)) (X := (21046217980353/100000000000000 : ℝ)) (Y := (39476891637301/50000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (947641293/1000000000 : ℝ)) (n' := (17495307/20000000 : ℝ)) (Ab := (33278397/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (947643317/1000000000 : ℝ) ^ p + (49665583/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (947643317/1000000000 : ℝ)) (y := (49665583/50000000 : ℝ)) (X := (1176013627449/6250000000000 : ℝ)) (Y := (81183801466261/100000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49665583/50000000 : ℝ) ^ p + (947643317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49665583/50000000 : ℝ)) (y := (947643317/1000000000 : ℝ)) (X := (81183801466261/100000000000000 : ℝ)) (Y := (1176013627449/6250000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1940954977/1000000000 : ℝ)) (τ := (947643317/1000000000 : ℝ)) (σ := (49665583/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (831962049/874767649 : ℝ) ^ p + (868138133/874767649 : ℝ) ^ p := by
    exact cert_lt (x := (831962049/874767649 : ℝ)) (y := (868138133/874767649 : ℝ)) (X := (21046168867201/100000000000000 : ℝ)) (Y := (3947691624777/5000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (947643317/1000000000 : ℝ)) (n' := (874767649/1000000000 : ℝ)) (Ab := (831962049/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (118455421/125000000 : ℝ) ^ p + (31040989/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (118455421/125000000 : ℝ)) (y := (31040989/31250000 : ℝ)) (X := (18816249494523/100000000000000 : ℝ)) (Y := (20295942750311/25000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (31040989/31250000 : ℝ) ^ p + (118455421/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (31040989/31250000 : ℝ)) (y := (118455421/125000000 : ℝ)) (X := (20295942750311/25000000000000 : ℝ)) (Y := (18816249494523/100000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (242619377/125000000 : ℝ)) (τ := (118455421/125000000 : ℝ)) (σ := (31040989/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (831962101/874767706 : ℝ) ^ p + (434069095/437383853 : ℝ) ^ p := by
    exact cert_lt (x := (831962101/874767706 : ℝ)) (y := (434069095/437383853 : ℝ)) (X := (4209233425999/20000000000000 : ℝ)) (Y := (78953833715891/100000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (118455421/125000000 : ℝ)) (n' := (437383853/500000000 : ℝ)) (Ab := (831962101/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (947643369/1000000000 : ℝ) ^ p + (31040989/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (947643369/1000000000 : ℝ)) (y := (31040989/31250000 : ℝ)) (X := (3763250022259/20000000000000 : ℝ)) (Y := (20295942750311/25000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (31040989/31250000 : ℝ) ^ p + (947643369/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31040989/31250000 : ℝ)) (y := (947643369/1000000000 : ℝ)) (X := (20295942750311/25000000000000 : ℝ)) (Y := (3763250022259/20000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1940955017/1000000000 : ℝ)) (τ := (947643369/1000000000 : ℝ)) (σ := (31040989/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (277320701/291589236 : ℝ) ^ p + (217034548/218691927 : ℝ) ^ p := by
    exact cert_lt (x := (277320701/291589236 : ℝ)) (y := (217034548/218691927 : ℝ)) (X := (10523083603449/50000000000000 : ℝ)) (Y := (7895383375871/10000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (947643369/1000000000 : ℝ)) (n' := (218691927/250000000 : ℝ)) (Ab := (831962103/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1940955017/1000000000 : ℝ)) (τ := (947643369/1000000000 : ℝ)) (σ := (31040989/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (947643369/1000000000 : ℝ)) (n' := (218691927/250000000 : ℝ)) (Ab := (831962103/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1940955017/1000000000 : ℝ)) (τ := (947643369/1000000000 : ℝ)) (σ := (31040989/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (947643369/1000000000 : ℝ)) (n' := (218691927/250000000 : ℝ)) (Ab := (831962103/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1940955017/1000000000 : ℝ)) (τ := (947643369/1000000000 : ℝ)) (σ := (31040989/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (947643369/1000000000 : ℝ)) (n' := (218691927/250000000 : ℝ)) (Ab := (831962103/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1940955017/1000000000 : ℝ)) (τ := (947643369/1000000000 : ℝ)) (σ := (31040989/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (947643369/1000000000 : ℝ)) (n' := (218691927/250000000 : ℝ)) (Ab := (831962103/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1940955017/1000000000 : ℝ)) (τ := (947643369/1000000000 : ℝ)) (σ := (31040989/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1713235323/1841614717 : ℝ) ^ p + (1834985201/1841614717 : ℝ) ^ p := by
    exact cert_lt (x := (1713235323/1841614717 : ℝ)) (y := (1834985201/1841614717 : ℝ)) (X := (5298759154239/50000000000000 : ℝ)) (Y := (8940248192987/10000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1092738187/1158385283 : ℝ) ^ p + (1151755767/1158385283 : ℝ) ^ p := by
    exact cert_lt (x := (1092738187/1158385283 : ℝ)) (y := (1151755767/1158385283 : ℝ)) (X := (1632947422113/10000000000000 : ℝ)) (Y := (20917631588501/25000000000000 : ℝ)) 497 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (31040989/31250000 : ℝ)) (U := (1158385283/1000000000 : ℝ)) (Ab := (1713235323/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (947643369/1000000000 : ℝ)) (σ := (31040989/31250000 : ℝ)) (Ab := (1092738187/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab080
