import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 82, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab082 (p : ℝ) (hpa : (249/8 : ℝ) ≤ p) (hpb : p ≤ (499/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (355957182859/27576750000000 : ℝ) (6599277/1000000000 : ℝ) (1600000330921/11030700000000 : ℝ) (591/500 : ℝ) (48901/25000 : ℝ) (30561761/31250000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158453817/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10931/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1127/2000 : ℝ)
      else (8293/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2877/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (355957182859/27576750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6599277/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (94468003/100000000 : ℝ) ^ p + (31064443/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (94468003/100000000 : ℝ)) (y := (31064443/31250000 : ℝ)) (X := (3390179235691/20000000000000 : ℝ)) (Y := (16609825216849/20000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31064443/31250000 : ℝ) ^ p + (94468003/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (31064443/31250000 : ℝ)) (y := (94468003/100000000 : ℝ)) (X := (16609825216849/20000000000000 : ℝ)) (Y := (3390179235691/20000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (969371103/500000000 : ℝ)) (τ := (94468003/100000000 : ℝ)) (σ := (31064443/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (414462758/435657769 : ℝ) ^ p + (864716261/871315538 : ℝ) ^ p := by
    exact cert_lt (x := (414462758/435657769 : ℝ)) (y := (864716261/871315538 : ℝ)) (X := (329837720287/1562500000000 : ℝ)) (Y := (78890387401937/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (94468003/100000000 : ℝ)) (n' := (435657769/500000000 : ℝ)) (Ab := (207231379/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (236946219/250000000 : ℝ) ^ p + (993353593/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236946219/250000000 : ℝ)) (y := (993353593/1000000000 : ℝ)) (X := (9388713574441/50000000000000 : ℝ)) (Y := (81222593252847/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993353593/1000000000 : ℝ) ^ p + (236946219/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993353593/1000000000 : ℝ)) (y := (236946219/250000000 : ℝ)) (X := (81222593252847/100000000000000 : ℝ)) (Y := (9388713574441/50000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1941138469/1000000000 : ℝ)) (τ := (236946219/250000000 : ℝ)) (σ := (993353593/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (832188421/874846225 : ℝ) ^ p + (868246948/874846225 : ℝ) ^ p := by
    exact cert_lt (x := (832188421/874846225 : ℝ)) (y := (868246948/874846225 : ℝ)) (X := (4206759704391/20000000000000 : ℝ)) (Y := (1579324053807/2000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (236946219/250000000 : ℝ)) (n' := (34993849/40000000 : ℝ)) (Ab := (832188421/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (947863821/1000000000 : ℝ) ^ p + (198666887/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (947863821/1000000000 : ℝ)) (y := (198666887/200000000 : ℝ)) (X := (18826267368407/100000000000000 : ℝ)) (Y := (81173753068091/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198666887/200000000 : ℝ) ^ p + (947863821/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198666887/200000000 : ℝ)) (y := (947863821/1000000000 : ℝ)) (X := (81173753068091/100000000000000 : ℝ)) (Y := (18826267368407/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (121324891/62500000 : ℝ)) (τ := (947863821/1000000000 : ℝ)) (σ := (198666887/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (832271241/874935848 : ℝ) ^ p + (868336571/874935848 : ℝ) ^ p := by
    exact cert_lt (x := (832271241/874935848 : ℝ)) (y := (868336571/874935848 : ℝ)) (X := (5257970243297/25000000000000 : ℝ)) (Y := (39484060068479/50000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (947863821/1000000000 : ℝ)) (n' := (109366981/125000000 : ℝ)) (Ab := (832271241/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (947865817/1000000000 : ℝ) ^ p + (19866679/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (947865817/1000000000 : ℝ)) (y := (19866679/20000000 : ℝ)) (X := (1176718988049/6250000000000 : ℝ)) (Y := (81172517008991/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (19866679/20000000 : ℝ) ^ p + (947865817/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19866679/20000000 : ℝ)) (y := (947865817/1000000000 : ℝ)) (X := (81172517008991/100000000000000 : ℝ)) (Y := (1176718988049/6250000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1941199767/1000000000 : ℝ)) (τ := (947865817/1000000000 : ℝ)) (σ := (19866679/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (832273334/874938113 : ℝ) ^ p + (868338836/874938113 : ℝ) ^ p := by
    exact cert_lt (x := (832273334/874938113 : ℝ)) (y := (868338836/874938113 : ℝ)) (X := (21031832463223/100000000000000 : ℝ)) (Y := (78968168591181/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (947865817/1000000000 : ℝ)) (n' := (874938113/1000000000 : ℝ)) (Ab := (416136667/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (947865867/1000000000 : ℝ) ^ p + (496666969/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (947865867/1000000000 : ℝ)) (y := (496666969/500000000 : ℝ)) (X := (18827534782749/100000000000000 : ℝ)) (Y := (81172486426317/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496666969/500000000 : ℝ) ^ p + (947865867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496666969/500000000 : ℝ)) (y := (947865867/1000000000 : ℝ)) (X := (81172486426317/100000000000000 : ℝ)) (Y := (18827534782749/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (388239961/200000000 : ℝ)) (τ := (947865867/1000000000 : ℝ)) (σ := (496666969/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (832273387/874938170 : ℝ) ^ p + (868338893/874938170 : ℝ) ^ p := by
    exact cert_lt (x := (832273387/874938170 : ℝ)) (y := (868338893/874938170 : ℝ)) (X := (10515915750663/50000000000000 : ℝ)) (Y := (19742042452639/25000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (947865867/1000000000 : ℝ)) (n' := (87493817/100000000 : ℝ)) (Ab := (832273387/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (947865869/1000000000 : ℝ) ^ p + (993333937/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (947865869/1000000000 : ℝ)) (y := (993333937/1000000000 : ℝ)) (X := (4706884005427/25000000000000 : ℝ)) (Y := (81172483877761/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993333937/1000000000 : ℝ) ^ p + (947865869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993333937/1000000000 : ℝ)) (y := (947865869/1000000000 : ℝ)) (X := (81172483877761/100000000000000 : ℝ)) (Y := (4706884005427/25000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (970599903/500000000 : ℝ)) (τ := (947865869/1000000000 : ℝ)) (σ := (993333937/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (832273390/874938173 : ℝ) ^ p + (868338896/874938173 : ℝ) ^ p := by
    exact cert_lt (x := (832273390/874938173 : ℝ)) (y := (868338896/874938173 : ℝ)) (X := (1051591580831/5000000000000 : ℝ)) (Y := (78968169874733/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (947865869/1000000000 : ℝ)) (n' := (874938173/1000000000 : ℝ)) (Ab := (83227339/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (970599903/500000000 : ℝ)) (τ := (947865869/1000000000 : ℝ)) (σ := (993333937/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (947865869/1000000000 : ℝ)) (n' := (874938173/1000000000 : ℝ)) (Ab := (83227339/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (970599903/500000000 : ℝ)) (τ := (947865869/1000000000 : ℝ)) (σ := (993333937/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (947865869/1000000000 : ℝ)) (n' := (874938173/1000000000 : ℝ)) (Ab := (83227339/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (970599903/500000000 : ℝ)) (τ := (947865869/1000000000 : ℝ)) (σ := (993333937/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (947865869/1000000000 : ℝ)) (n' := (874938173/1000000000 : ℝ)) (Ab := (83227339/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (970599903/500000000 : ℝ)) (τ := (947865869/1000000000 : ℝ)) (σ := (993333937/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (947865869/1000000000 : ℝ)) (n' := (874938173/1000000000 : ℝ)) (Ab := (83227339/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (970599903/500000000 : ℝ)) (τ := (947865869/1000000000 : ℝ)) (σ := (993333937/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1713640456/1841546183 : ℝ) ^ p + (1834946906/1841546183 : ℝ) ^ p := by
    exact cert_lt (x := (1713640456/1841546183 : ℝ)) (y := (1834946906/1841546183 : ℝ)) (X := (2648061450821/25000000000000 : ℝ)) (Y := (22351938616089/25000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1093038287/1158453817 : ℝ) ^ p + (1151854540/1158453817 : ℝ) ^ p := by
    exact cert_lt (x := (1093038287/1158453817 : ℝ)) (y := (1151854540/1158453817 : ℝ)) (X := (16320107575847/100000000000000 : ℝ)) (Y := (83679893023763/100000000000000 : ℝ)) 499 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993333937/1000000000 : ℝ)) (U := (1158453817/1000000000 : ℝ)) (Ab := (214205057/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (947865869/1000000000 : ℝ)) (σ := (993333937/1000000000 : ℝ)) (Ab := (1093038287/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab082
