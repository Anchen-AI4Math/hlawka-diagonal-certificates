import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 1, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab001 (p : ℝ) (hpa : (417/16 : ℝ) ≤ p) (hpb : p ≤ (209/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (727596261377/46182750000000 : ℝ) (4044837/500000000 : ℝ) (3200000554193/18473100000000 : ℝ) (591/500 : ℝ) (973816931/500000000 : ℝ) (243438743/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231077867/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10791/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(683/1250 : ℝ)
      else (4059/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2293/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (727596261377/46182750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4044837/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (933389249/1000000000 : ℝ) ^ p + (496557201/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (933389249/1000000000 : ℝ)) (y := (496557201/500000000 : ℝ)) (X := (4128863344359/25000000000000 : ℝ)) (Y := (41742282663683/50000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496557201/500000000 : ℝ) ^ p + (933389249/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496557201/500000000 : ℝ)) (y := (933389249/1000000000 : ℝ)) (X := (41742282663683/50000000000000 : ℝ)) (Y := (4128863344359/25000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1926503651/1000000000 : ℝ)) (τ := (933389249/1000000000 : ℝ)) (σ := (496557201/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (813403537/862195516 : ℝ) ^ p + (427052921/431097758 : ℝ) ^ p := by
    exact cert_lt (x := (813403537/862195516 : ℝ)) (y := (427052921/431097758 : ℝ)) (X := (4365914695199/20000000000000 : ℝ)) (Y := (9771303432429/12500000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (933389249/1000000000 : ℝ)) (n' := (215548879/250000000 : ℝ)) (Ab := (813403537/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (234226769/250000000 : ℝ) ^ p + (248082519/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (234226769/250000000 : ℝ)) (y := (248082519/250000000 : ℝ)) (X := (9110486366917/50000000000000 : ℝ)) (Y := (16355808918789/20000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248082519/250000000 : ℝ) ^ p + (234226769/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248082519/250000000 : ℝ)) (y := (234226769/250000000 : ℝ)) (X := (16355808918789/20000000000000 : ℝ)) (Y := (9110486366917/50000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60288661/31250000 : ℝ)) (τ := (234226769/250000000 : ℝ)) (σ := (248082519/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (817111714/866264489 : ℝ) ^ p + (858174815/866264489 : ℝ) ^ p := by
    exact cert_lt (x := (817111714/866264489 : ℝ)) (y := (858174815/866264489 : ℝ)) (X := (10869333582891/50000000000000 : ℝ)) (Y := (78261334004869/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (234226769/250000000 : ℝ)) (n' := (866264489/1000000000 : ℝ)) (Ab := (408555857/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (937019481/1000000000 : ℝ) ^ p + (992303501/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937019481/1000000000 : ℝ)) (y := (992303501/1000000000 : ℝ)) (X := (18278169525233/100000000000000 : ℝ)) (Y := (81721848107887/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992303501/1000000000 : ℝ) ^ p + (937019481/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992303501/1000000000 : ℝ)) (y := (937019481/1000000000 : ℝ)) (X := (81721848107887/100000000000000 : ℝ)) (Y := (18278169525233/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (964661491/500000000 : ℝ)) (τ := (937019481/1000000000 : ℝ)) (σ := (992303501/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (817229963/866394256 : ℝ) ^ p + (429152291/433197128 : ℝ) ^ p := by
    exact cert_lt (x := (817229963/866394256 : ℝ)) (y := (429152291/433197128 : ℝ)) (X := (21735779987387/100000000000000 : ℝ)) (Y := (1565284415899/2000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (937019481/1000000000 : ℝ)) (n' := (54149641/62500000 : ℝ)) (Ab := (817229963/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (937023051/1000000000 : ℝ) ^ p + (198460531/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (937023051/1000000000 : ℝ)) (y := (198460531/200000000 : ℝ)) (X := (4569997232557/25000000000000 : ℝ)) (Y := (81720027922319/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198460531/200000000 : ℝ) ^ p + (937023051/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198460531/200000000 : ℝ)) (y := (937023051/1000000000 : ℝ)) (X := (81720027922319/100000000000000 : ℝ)) (Y := (4569997232557/25000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (964662853/500000000 : ℝ)) (τ := (937023051/1000000000 : ℝ)) (σ := (198460531/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (817233719/866398377 : ℝ) ^ p + (286102901/288799459 : ℝ) ^ p := by
    exact cert_lt (x := (817233719/866398377 : ℝ)) (y := (286102901/288799459 : ℝ)) (X := (21735688859031/100000000000000 : ℝ)) (Y := (78264312458017/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (937023051/1000000000 : ℝ)) (n' := (866398377/1000000000 : ℝ)) (Ab := (817233719/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (937023163/1000000000 : ℝ) ^ p + (992302629/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937023163/1000000000 : ℝ)) (y := (992302629/1000000000 : ℝ)) (X := (9140023006209/50000000000000 : ℝ)) (Y := (20429992995857/25000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992302629/1000000000 : ℝ) ^ p + (937023163/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992302629/1000000000 : ℝ)) (y := (937023163/1000000000 : ℝ)) (X := (20429992995857/25000000000000 : ℝ)) (Y := (9140023006209/50000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (60291431/31250000 : ℝ)) (τ := (937023163/1000000000 : ℝ)) (σ := (992302629/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (408616918/433199253 : ℝ) ^ p + (143051472/144399751 : ℝ) ^ p := by
    exact cert_lt (x := (408616918/433199253 : ℝ)) (y := (143051472/144399751 : ℝ)) (X := (4347137121471/20000000000000 : ℝ)) (Y := (78264315327341/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (937023163/1000000000 : ℝ)) (n' := (433199253/500000000 : ℝ)) (Ab := (204308459/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (937023167/1000000000 : ℝ) ^ p + (248075657/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (937023167/1000000000 : ℝ)) (y := (248075657/250000000 : ℝ)) (X := (18280048051071/100000000000000 : ℝ)) (Y := (81719969831933/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248075657/250000000 : ℝ) ^ p + (937023167/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248075657/250000000 : ℝ)) (y := (937023167/1000000000 : ℝ)) (X := (81719969831933/100000000000000 : ℝ)) (Y := (18280048051071/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (385865159/200000000 : ℝ)) (τ := (937023167/1000000000 : ℝ)) (σ := (248075657/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (817233841/866398511 : ℝ) ^ p + (858308837/866398511 : ℝ) ^ p := by
    exact cert_lt (x := (817233841/866398511 : ℝ)) (y := (858308837/866398511 : ℝ)) (X := (21735685804501/100000000000000 : ℝ)) (Y := (15652863087711/20000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (937023167/1000000000 : ℝ)) (n' := (866398511/1000000000 : ℝ)) (Ab := (817233841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (385865159/200000000 : ℝ)) (τ := (937023167/1000000000 : ℝ)) (σ := (248075657/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (937023167/1000000000 : ℝ)) (n' := (866398511/1000000000 : ℝ)) (Ab := (817233841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (385865159/200000000 : ℝ)) (τ := (937023167/1000000000 : ℝ)) (σ := (248075657/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (937023167/1000000000 : ℝ)) (n' := (866398511/1000000000 : ℝ)) (Ab := (817233841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (385865159/200000000 : ℝ)) (τ := (937023167/1000000000 : ℝ)) (σ := (248075657/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (937023167/1000000000 : ℝ)) (n' := (866398511/1000000000 : ℝ)) (Ab := (817233841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (385865159/200000000 : ℝ)) (τ := (937023167/1000000000 : ℝ)) (σ := (248075657/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (937023167/1000000000 : ℝ)) (n' := (866398511/1000000000 : ℝ)) (Ab := (817233841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (385865159/200000000 : ℝ)) (τ := (937023167/1000000000 : ℝ)) (σ := (248075657/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1694259697/1844610665 : ℝ) ^ p + (1836520991/1844610665 : ℝ) ^ p := by
    exact cert_lt (x := (1694259697/1844610665 : ℝ)) (y := (1836520991/1844610665 : ℝ)) (X := (1355973816383/12500000000000 : ℝ)) (Y := (89152209709239/100000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1079059566/1155389335 : ℝ) ^ p + (7598011/7651585 : ℝ) ^ p := by
    exact cert_lt (x := (1079059566/1155389335 : ℝ)) (y := (7598011/7651585 : ℝ)) (X := (16770009825787/100000000000000 : ℝ)) (Y := (16645998143793/20000000000000 : ℝ)) 209 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248075657/250000000 : ℝ)) (U := (231077867/200000000 : ℝ)) (Ab := (1694259697/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (937023167/1000000000 : ℝ)) (σ := (248075657/250000000 : ℝ)) (Ab := (539529783/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab001
