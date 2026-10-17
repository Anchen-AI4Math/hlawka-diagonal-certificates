import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 36, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab036 (p : ℝ) (hpa : (113/4 : ℝ) ≤ p) (hpb : p ≤ (453/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (360067992499/25029500000000 : ℝ) (7371541/1000000000 : ℝ) (800000150177/5005900000000 : ℝ) (591/500 : ℝ) (195163047/100000000 : ℝ) (975762381/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578393987/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1357/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(5547/10000 : ℝ)
      else (4101/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2297/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (360067992499/25029500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7371541/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (93878607/100000000 : ℝ) ^ p + (993557699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (93878607/100000000 : ℝ)) (y := (993557699/1000000000 : ℝ)) (X := (8361090189341/50000000000000 : ℝ)) (Y := (41638919403009/50000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993557699/1000000000 : ℝ) ^ p + (93878607/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993557699/1000000000 : ℝ)) (y := (93878607/100000000 : ℝ)) (X := (41638919403009/50000000000000 : ℝ)) (Y := (8361090189341/50000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1932343769/1000000000 : ℝ)) (τ := (93878607/100000000 : ℝ)) (σ := (993557699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (410397369/433306007 : ℝ) ^ p + (859240473/866612014 : ℝ) ^ p := by
    exact cert_lt (x := (410397369/433306007 : ℝ)) (y := (859240473/866612014 : ℝ)) (X := (2148345410271/10000000000000 : ℝ)) (Y := (19629136802647/25000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (93878607/100000000 : ℝ)) (n' := (433306007/500000000 : ℝ)) (Ab := (410397369/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (942118373/1000000000 : ℝ) ^ p + (496403203/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (942118373/1000000000 : ℝ)) (y := (496403203/500000000 : ℝ)) (X := (18486777558011/100000000000000 : ℝ)) (Y := (3260529625781/4000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496403203/500000000 : ℝ) ^ p + (942118373/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496403203/500000000 : ℝ)) (y := (942118373/1000000000 : ℝ)) (X := (3260529625781/4000000000000 : ℝ)) (Y := (18486777558011/100000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1934924779/1000000000 : ℝ)) (τ := (942118373/1000000000 : ℝ)) (σ := (496403203/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (824301963/870435176 : ℝ) ^ p + (863063635/870435176 : ℝ) ^ p := by
    exact cert_lt (x := (824301963/870435176 : ℝ)) (y := (863063635/870435176 : ℝ)) (X := (2139964470167/10000000000000 : ℝ)) (Y := (9825044576523/12500000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (942118373/1000000000 : ℝ)) (n' := (108804397/125000000 : ℝ)) (Ab := (824301963/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (942214233/1000000000 : ℝ) ^ p + (992783457/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942214233/1000000000 : ℝ)) (y := (992783457/1000000000 : ℝ)) (X := (9270053986579/50000000000000 : ℝ)) (Y := (81459911024771/100000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992783457/1000000000 : ℝ) ^ p + (942214233/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992783457/1000000000 : ℝ)) (y := (942214233/1000000000 : ℝ)) (X := (81459911024771/100000000000000 : ℝ)) (Y := (9270053986579/50000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (193499769/100000000 : ℝ)) (τ := (942214233/1000000000 : ℝ)) (σ := (992783457/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (824402665/870544958 : ℝ) ^ p + (863173417/870544958 : ℝ) ^ p := by
    exact cert_lt (x := (824402665/870544958 : ℝ)) (y := (863173417/870544958 : ℝ)) (X := (4279449568751/20000000000000 : ℝ)) (Y := (39301376796409/50000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (942214233/1000000000 : ℝ)) (n' := (435272479/500000000 : ℝ)) (Ab := (164880533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (37688679/40000000 : ℝ) ^ p + (992782799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (37688679/40000000 : ℝ)) (y := (992782799/1000000000 : ℝ)) (X := (1854163562901/10000000000000 : ℝ)) (Y := (20364595609953/25000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992782799/1000000000 : ℝ) ^ p + (37688679/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (992782799/1000000000 : ℝ)) (y := (37688679/40000000 : ℝ)) (X := (20364595609953/25000000000000 : ℝ)) (Y := (1854163562901/10000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (967499887/500000000 : ℝ)) (τ := (37688679/40000000 : ℝ)) (σ := (992782799/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (824405545/870548098 : ℝ) ^ p + (863176557/870548098 : ℝ) ^ p := by
    exact cert_lt (x := (824405545/870548098 : ℝ)) (y := (863176557/870548098 : ℝ)) (X := (10698589543097/50000000000000 : ℝ)) (Y := (15720564428747/20000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (37688679/40000000 : ℝ)) (n' := (435274049/500000000 : ℝ)) (Ab := (164881109/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (471108527/500000000 : ℝ) ^ p + (49639139/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (471108527/500000000 : ℝ)) (y := (49639139/50000000 : ℝ)) (X := (3708335928847/20000000000000 : ℝ)) (Y := (10182292287719/12500000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (49639139/50000000 : ℝ) ^ p + (471108527/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (49639139/50000000 : ℝ)) (y := (471108527/500000000 : ℝ)) (X := (10182292287719/12500000000000 : ℝ)) (Y := (3708335928847/20000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (967499917/500000000 : ℝ)) (τ := (471108527/500000000 : ℝ)) (σ := (49639139/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (824405627/870548188 : ℝ) ^ p + (863176647/870548188 : ℝ) ^ p := by
    exact cert_lt (x := (824405627/870548188 : ℝ)) (y := (863176647/870548188 : ℝ)) (X := (10698588356461/50000000000000 : ℝ)) (Y := (19650706027141/25000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (471108527/500000000 : ℝ)) (n' := (217637047/250000000 : ℝ)) (Ab := (824405627/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (188443411/200000000 : ℝ) ^ p + (49639139/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (188443411/200000000 : ℝ)) (y := (49639139/50000000 : ℝ)) (X := (18541680201391/100000000000000 : ℝ)) (Y := (10182292287719/12500000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (49639139/50000000 : ℝ) ^ p + (188443411/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (49639139/50000000 : ℝ)) (y := (188443411/200000000 : ℝ)) (X := (10182292287719/12500000000000 : ℝ)) (Y := (18541680201391/100000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (386999967/200000000 : ℝ)) (τ := (188443411/200000000 : ℝ)) (σ := (49639139/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (824405628/870548189 : ℝ) ^ p + (863176648/870548189 : ℝ) ^ p := by
    exact cert_lt (x := (824405628/870548189 : ℝ)) (y := (863176648/870548189 : ℝ)) (X := (21397176751871/100000000000000 : ℝ)) (Y := (15720564826079/20000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (188443411/200000000 : ℝ)) (n' := (870548189/1000000000 : ℝ)) (Ab := (206101407/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (386999967/200000000 : ℝ)) (τ := (188443411/200000000 : ℝ)) (σ := (49639139/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (188443411/200000000 : ℝ)) (n' := (870548189/1000000000 : ℝ)) (Ab := (206101407/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (386999967/200000000 : ℝ)) (τ := (188443411/200000000 : ℝ)) (σ := (49639139/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (188443411/200000000 : ℝ)) (n' := (870548189/1000000000 : ℝ)) (Ab := (206101407/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (386999967/200000000 : ℝ)) (τ := (188443411/200000000 : ℝ)) (σ := (49639139/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (188443411/200000000 : ℝ)) (n' := (870548189/1000000000 : ℝ)) (Ab := (206101407/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (386999967/200000000 : ℝ)) (τ := (188443411/200000000 : ℝ)) (σ := (49639139/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (188443411/200000000 : ℝ)) (n' := (870548189/1000000000 : ℝ)) (Ab := (206101407/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (386999967/200000000 : ℝ)) (τ := (188443411/200000000 : ℝ)) (σ := (49639139/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1703451985/1843212026 : ℝ) ^ p + (1835840485/1843212026 : ℝ) ^ p := by
    exact cert_lt (x := (1703451985/1843212026 : ℝ)) (y := (1835840485/1843212026 : ℝ)) (X := (10725737189227/100000000000000 : ℝ)) (Y := (89274263035637/100000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (542796909/578393987 : ℝ) ^ p + (1149416433/1156787974 : ℝ) ^ p := by
    exact cert_lt (x := (542796909/578393987 : ℝ)) (y := (1149416433/1156787974 : ℝ)) (X := (8278086405357/50000000000000 : ℝ)) (Y := (41721913875381/50000000000000 : ℝ)) 453 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (49639139/50000000 : ℝ)) (U := (578393987/500000000 : ℝ)) (Ab := (340690397/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (188443411/200000000 : ℝ)) (σ := (49639139/50000000 : ℝ)) (Ab := (542796909/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab036
