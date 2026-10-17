import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 83, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab083 (p : ℝ) (hpa : (755/32 : ℝ) ≤ p) (hpb : p ≤ (189/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (419650495177/20611500000000 : ℝ) (5241759/500000000 : ℝ) (800000123669/4122300000000 : ℝ) (3033/2500 : ℝ) (121385833/62500000 : ℝ) (971048927/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238685549/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(139/125 : ℝ) ≤ X j i ∧ X j i ≤ -(4579/10000 : ℝ)
      else (483/625 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (419650495177/20611500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5241759/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (459556703/500000000 : ℝ) ^ p + (124226921/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (459556703/500000000 : ℝ)) (y := (124226921/125000000 : ℝ)) (X := (6816556015563/50000000000000 : ℝ)) (Y := (10795863132367/12500000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124226921/125000000 : ℝ) ^ p + (459556703/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124226921/125000000 : ℝ)) (y := (459556703/500000000 : ℝ)) (X := (10795863132367/12500000000000 : ℝ)) (Y := (6816556015563/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (956464387/500000000 : ℝ)) (τ := (459556703/500000000 : ℝ)) (σ := (124226921/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (391302818/414276625 : ℝ) ^ p + (409034866/414276625 : ℝ) ^ p := by
    exact cert_lt (x := (391302818/414276625 : ℝ)) (y := (409034866/414276625 : ℝ)) (X := (25979611331253/100000000000000 : ℝ)) (Y := (74020389925271/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459556703/500000000 : ℝ)) (n' := (3314213/4000000 : ℝ)) (Ab := (195651409/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924754599/1000000000 : ℝ) ^ p + (992770281/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924754599/1000000000 : ℝ)) (y := (992770281/1000000000 : ℝ)) (X := (7876731885243/50000000000000 : ℝ)) (Y := (16849310640833/20000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992770281/1000000000 : ℝ) ^ p + (924754599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992770281/1000000000 : ℝ)) (y := (924754599/1000000000 : ℝ)) (X := (16849310640833/20000000000000 : ℝ)) (Y := (7876731885243/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (23969061/12500000 : ℝ)) (τ := (924754599/1000000000 : ℝ)) (σ := (992770281/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (26289361/27841000 : ℝ) ^ p + (137457747/139205000 : ℝ) ^ p := by
    exact cert_lt (x := (26289361/27841000 : ℝ)) (y := (137457747/139205000 : ℝ)) (X := (12900130362629/50000000000000 : ℝ)) (Y := (74199740307691/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924754599/1000000000 : ℝ)) (n' := (83523/100000 : ℝ)) (Ab := (78868083/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (57812537/62500000 : ℝ) ^ p + (496360361/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (57812537/62500000 : ℝ)) (y := (496360361/500000000 : ℝ)) (X := (7926382148883/50000000000000 : ℝ)) (Y := (42073626231489/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496360361/500000000 : ℝ) ^ p + (57812537/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (496360361/500000000 : ℝ)) (y := (57812537/62500000 : ℝ)) (X := (42073626231489/50000000000000 : ℝ)) (Y := (7926382148883/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958860657/500000000 : ℝ)) (τ := (57812537/62500000 : ℝ)) (σ := (496360361/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (394472438/417760121 : ℝ) ^ p + (412518362/417760121 : ℝ) ^ p := by
    exact cert_lt (x := (394472438/417760121 : ℝ)) (y := (412518362/417760121 : ℝ)) (X := (5158504087269/20000000000000 : ℝ)) (Y := (74207481106001/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (57812537/62500000 : ℝ)) (n' := (417760121/500000000 : ℝ)) (Ab := (197236219/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462505603/500000000 : ℝ) ^ p + (62044911/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (462505603/500000000 : ℝ)) (y := (62044911/62500000 : ℝ)) (X := (1585706233593/10000000000000 : ℝ)) (Y := (84142955082891/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (62044911/62500000 : ℝ) ^ p + (462505603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62044911/62500000 : ℝ)) (y := (462505603/500000000 : ℝ)) (X := (84142955082891/100000000000000 : ℝ)) (Y := (1585706233593/10000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (958864891/500000000 : ℝ)) (τ := (462505603/500000000 : ℝ)) (σ := (62044911/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (262985422/278510921 : ℝ) ^ p + (275016415/278510921 : ℝ) ^ p := by
    exact cert_lt (x := (262985422/278510921 : ℝ)) (y := (275016415/278510921 : ℝ)) (X := (322402324887/1250000000000 : ℝ)) (Y := (14841562987873/20000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (462505603/500000000 : ℝ)) (n' := (835532763/1000000000 : ℝ)) (Ab := (394478133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (57813229/62500000 : ℝ) ^ p + (992718483/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57813229/62500000 : ℝ)) (y := (992718483/1000000000 : ℝ)) (X := (792862391189/5000000000000 : ℝ)) (Y := (84142768854489/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992718483/1000000000 : ℝ) ^ p + (57813229/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992718483/1000000000 : ℝ)) (y := (57813229/62500000 : ℝ)) (X := (84142768854489/100000000000000 : ℝ)) (Y := (792862391189/5000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1917730147/1000000000 : ℝ)) (τ := (57813229/62500000 : ℝ)) (σ := (992718483/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (262985586/278511101 : ℝ) ^ p + (275016595/278511101 : ℝ) ^ p := by
    exact cert_lt (x := (262985586/278511101 : ℝ)) (y := (275016595/278511101 : ℝ)) (X := (25792172167773/100000000000000 : ℝ)) (Y := (37103914668293/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (57813229/62500000 : ℝ)) (n' := (835533303/1000000000 : ℝ)) (Ab := (394478379/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (231252921/250000000 : ℝ) ^ p + (992718479/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231252921/250000000 : ℝ)) (y := (992718479/1000000000 : ℝ)) (X := (15857255923733/100000000000000 : ℝ)) (Y := (42071380422337/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992718479/1000000000 : ℝ) ^ p + (231252921/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992718479/1000000000 : ℝ)) (y := (231252921/250000000 : ℝ)) (X := (42071380422337/50000000000000 : ℝ)) (Y := (15857255923733/100000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (262985593/278511109 : ℝ) ^ p + (275016603/278511109 : ℝ) ^ p := by
    exact cert_lt (x := (262985593/278511109 : ℝ)) (y := (275016603/278511109 : ℝ)) (X := (25792170884051/100000000000000 : ℝ)) (Y := (37103914988231/50000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (n' := (835533327/1000000000 : ℝ)) (Ab := (788956779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1917730163/1000000000 : ℝ)) (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1656271022/1806572255 : ℝ) ^ p + (1796088737/1806572255 : ℝ) ^ p := by
    exact cert_lt (x := (1656271022/1806572255 : ℝ)) (y := (1796088737/1806572255 : ℝ)) (X := (6423061743699/50000000000000 : ℝ)) (Y := (680889662517/781250000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (222391381/238685549 : ℝ) ^ p + (1182944227/1193427745 : ℝ) ^ p := by
    exact cert_lt (x := (222391381/238685549 : ℝ)) (y := (1182944227/1193427745 : ℝ)) (X := (9407828477887/50000000000000 : ℝ)) (Y := (20296085898099/25000000000000 : ℝ)) 189 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992718479/1000000000 : ℝ)) (U := (238685549/200000000 : ℝ)) (Ab := (828135511/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231252921/250000000 : ℝ)) (σ := (992718479/1000000000 : ℝ)) (Ab := (222391381/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab083
