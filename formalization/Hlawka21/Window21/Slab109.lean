import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 109, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab109 (p : ℝ) (hpa : (781/32 : ℝ) ≤ p) (hpb : p ≤ (391/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2089538081651/106606500000000 : ℝ) (10082559/1000000000 : ℝ) (4000000639639/21321300000000 : ℝ) (3033/2500 : ℝ) (486017203/250000000 : ℝ) (971999103/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298439643/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11147/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(289/625 : ℝ)
      else (7773/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11853/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2089538081651/106606500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10082559/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (921938619/1000000000 : ℝ) ^ p + (248494669/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (921938619/1000000000 : ℝ)) (y := (248494669/250000000 : ℝ)) (X := (6860808731839/50000000000000 : ℝ)) (Y := (43139200434829/50000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248494669/250000000 : ℝ) ^ p + (921938619/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248494669/250000000 : ℝ)) (y := (921938619/1000000000 : ℝ)) (X := (43139200434829/50000000000000 : ℝ)) (Y := (6860808731839/50000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (383183459/200000000 : ℝ)) (τ := (921938619/1000000000 : ℝ)) (σ := (248494669/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (157265844/166233725 : ℝ) ^ p + (821086066/831168625 : ℝ) ^ p := by
    exact cert_lt (x := (157265844/166233725 : ℝ)) (y := (821086066/831168625 : ℝ)) (X := (25788702399209/100000000000000 : ℝ)) (Y := (14842259819507/20000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (921938619/1000000000 : ℝ)) (n' := (6649349/8000000 : ℝ)) (Ab := (39316461/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (927467931/1000000000 : ℝ) ^ p + (992948447/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927467931/1000000000 : ℝ)) (y := (992948447/1000000000 : ℝ)) (X := (3176120073817/20000000000000 : ℝ)) (Y := (5257463551497/6250000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992948447/1000000000 : ℝ) ^ p + (927467931/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992948447/1000000000 : ℝ)) (y := (927467931/1000000000 : ℝ)) (X := (5257463551497/6250000000000 : ℝ)) (Y := (3176120073817/20000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (960208189/500000000 : ℝ)) (τ := (927467931/1000000000 : ℝ)) (σ := (992948447/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (132046073/139614382 : ℝ) ^ p + (275867911/279228764 : ℝ) ^ p := by
    exact cert_lt (x := (132046073/139614382 : ℝ)) (y := (275867911/279228764 : ℝ)) (X := (25615239375597/100000000000000 : ℝ)) (Y := (14876952349907/20000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (927467931/1000000000 : ℝ)) (n' := (209421573/250000000 : ℝ)) (Ab := (396138219/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (92769809/100000000 : ℝ) ^ p + (992901767/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92769809/100000000 : ℝ)) (y := (992901767/1000000000 : ℝ)) (X := (998574176609/6250000000000 : ℝ)) (Y := (84022829989471/100000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992901767/1000000000 : ℝ) ^ p + (92769809/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992901767/1000000000 : ℝ)) (y := (92769809/100000000 : ℝ)) (X := (84022829989471/100000000000000 : ℝ)) (Y := (998574176609/6250000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1920599857/1000000000 : ℝ)) (τ := (92769809/100000000 : ℝ)) (σ := (992901767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (198130799/209489191 : ℝ) ^ p + (827874205/837956764 : ℝ) ^ p := by
    exact cert_lt (x := (198130799/209489191 : ℝ)) (y := (827874205/837956764 : ℝ)) (X := (12804045328181/50000000000000 : ℝ)) (Y := (14878382033037/20000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (92769809/100000000 : ℝ)) (n' := (209489191/250000000 : ℝ)) (Ab := (198130799/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (927707573/1000000000 : ℝ) ^ p + (992899837/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927707573/1000000000 : ℝ)) (y := (992899837/1000000000 : ℝ)) (X := (7990589218329/50000000000000 : ℝ)) (Y := (1680376777311/2000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992899837/1000000000 : ℝ) ^ p + (927707573/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992899837/1000000000 : ℝ)) (y := (927707573/1000000000 : ℝ)) (X := (1680376777311/2000000000000 : ℝ)) (Y := (7990589218329/50000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (192060741/100000000 : ℝ)) (τ := (927707573/1000000000 : ℝ)) (σ := (992899837/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (792533362/837967907 : ℝ) ^ p + (827885348/837967907 : ℝ) ^ p := by
    exact cert_lt (x := (792533362/837967907 : ℝ)) (y := (827885348/837967907 : ℝ)) (X := (5121559252659/20000000000000 : ℝ)) (Y := (2324756393227/3125000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (927707573/1000000000 : ℝ)) (n' := (837967907/1000000000 : ℝ)) (Ab := (396266681/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231926991/250000000 : ℝ) ^ p + (992899757/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231926991/250000000 : ℝ)) (y := (992899757/1000000000 : ℝ)) (X := (15981343038001/100000000000000 : ℝ)) (Y := (42009336717143/50000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992899757/1000000000 : ℝ) ^ p + (231926991/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992899757/1000000000 : ℝ)) (y := (231926991/250000000 : ℝ)) (X := (42009336717143/50000000000000 : ℝ)) (Y := (15981343038001/100000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1920607721/1000000000 : ℝ)) (τ := (231926991/250000000 : ℝ)) (σ := (992899757/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (792533781/837968366 : ℝ) ^ p + (827885807/837968366 : ℝ) ^ p := by
    exact cert_lt (x := (792533781/837968366 : ℝ)) (y := (827885807/837968366 : ℝ)) (X := (12803892164957/50000000000000 : ℝ)) (Y := (18598054177681/25000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231926991/250000000 : ℝ)) (n' := (418984183/500000000 : ℝ)) (Ab := (792533781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (46385399/50000000 : ℝ) ^ p + (496449877/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (46385399/50000000 : ℝ)) (y := (496449877/500000000 : ℝ)) (X := (15981349773641/100000000000000 : ℝ)) (Y := (4200933361531/5000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496449877/500000000 : ℝ) ^ p + (46385399/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (496449877/500000000 : ℝ)) (y := (46385399/50000000 : ℝ)) (X := (4200933361531/5000000000000 : ℝ)) (Y := (15981349773641/100000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (960303867/500000000 : ℝ)) (τ := (46385399/50000000 : ℝ)) (σ := (496449877/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (264177933/279322795 : ℝ) ^ p + (275961942/279322795 : ℝ) ^ p := by
    exact cert_lt (x := (264177933/279322795 : ℝ)) (y := (275961942/279322795 : ℝ)) (X := (25607784353743/100000000000000 : ℝ)) (Y := (18598054303183/25000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (46385399/50000000 : ℝ)) (n' := (167593677/200000000 : ℝ)) (Ab := (792533799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (960303867/500000000 : ℝ)) (τ := (46385399/50000000 : ℝ)) (σ := (496449877/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (46385399/50000000 : ℝ)) (n' := (167593677/200000000 : ℝ)) (Ab := (792533799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (960303867/500000000 : ℝ)) (τ := (46385399/50000000 : ℝ)) (σ := (496449877/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (46385399/50000000 : ℝ)) (n' := (167593677/200000000 : ℝ)) (Ab := (792533799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (960303867/500000000 : ℝ)) (τ := (46385399/50000000 : ℝ)) (σ := (496449877/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (46385399/50000000 : ℝ)) (n' := (167593677/200000000 : ℝ)) (Ab := (792533799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (960303867/500000000 : ℝ)) (τ := (46385399/50000000 : ℝ)) (σ := (496449877/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (46385399/50000000 : ℝ)) (n' := (167593677/200000000 : ℝ)) (Ab := (792533799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (960303867/500000000 : ℝ)) (τ := (46385399/50000000 : ℝ)) (σ := (496449877/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (276738835/301040238 : ℝ) ^ p + (598719623/602080476 : ℝ) ^ p := by
    exact cert_lt (x := (276738835/301040238 : ℝ)) (y := (598719623/602080476 : ℝ)) (X := (2557000778481/20000000000000 : ℝ)) (Y := (87214996452133/100000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (371550649/397919524 : ℝ) ^ p + (394558671/397919524 : ℝ) ^ p := by
    exact cert_lt (x := (371550649/397919524 : ℝ)) (y := (394558671/397919524 : ℝ)) (X := (18720570703463/100000000000000 : ℝ)) (Y := (81279429797347/100000000000000 : ℝ)) 391 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496449877/500000000 : ℝ)) (U := (298439643/250000000 : ℝ)) (Ab := (166043301/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (46385399/50000000 : ℝ)) (σ := (496449877/500000000 : ℝ)) (Ab := (1114651947/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab109
