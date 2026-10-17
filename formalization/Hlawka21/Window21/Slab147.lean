import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 147, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab147 (p : ℝ) (hpa : (819/32 : ℝ) ≤ p) (hpb : p ≤ (205/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2077788602819/111793500000000 : ℝ) (4774047/500000000 : ℝ) (4000000670761/22358700000000 : ℝ) (3033/2500 : ℝ) (24332823/12500000 : ℝ) (973280773/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597119851/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(699/625 : ℝ) ≤ X j i ∧ X j i ≤ -(937/2000 : ℝ)
      else (3917/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11861/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2077788602819/111793500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4774047/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (462865501/500000000 : ℝ) ^ p + (198840621/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (462865501/500000000 : ℝ)) (y := (198840621/200000000 : ℝ)) (X := (1384118294337/10000000000000 : ℝ)) (Y := (8615883654179/10000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198840621/200000000 : ℝ) ^ p + (462865501/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198840621/200000000 : ℝ)) (y := (462865501/500000000 : ℝ)) (X := (8615883654179/10000000000000 : ℝ)) (Y := (1384118294337/10000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1919934107/1000000000 : ℝ)) (τ := (462865501/500000000 : ℝ)) (σ := (198840621/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (79133995/83464081 : ℝ) ^ p + (412546358/417320405 : ℝ) ^ p := by
    exact cert_lt (x := (79133995/83464081 : ℝ)) (y := (412546358/417320405 : ℝ)) (X := (102137811319/400000000000 : ℝ)) (Y := (9308193568389/12500000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462865501/500000000 : ℝ)) (n' := (83464081/100000000 : ℝ)) (Ab := (15826799/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931097869/1000000000 : ℝ) ^ p + (993195473/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931097869/1000000000 : ℝ)) (y := (993195473/1000000000 : ℝ)) (X := (4012780539319/25000000000000 : ℝ)) (Y := (83948896404509/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993195473/1000000000 : ℝ) ^ p + (931097869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993195473/1000000000 : ℝ)) (y := (931097869/1000000000 : ℝ)) (X := (83948896404509/100000000000000 : ℝ)) (Y := (4012780539319/25000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (962146671/500000000 : ℝ)) (τ := (931097869/1000000000 : ℝ)) (σ := (993195473/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (4920389/5190941 : ℝ) ^ p + (138564058/140155407 : ℝ) ^ p := by
    exact cert_lt (x := (4920389/5190941 : ℝ)) (y := (138564058/140155407 : ℝ)) (X := (5073813406579/20000000000000 : ℝ)) (Y := (74630934430609/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931097869/1000000000 : ℝ)) (n' := (420466221/500000000 : ℝ)) (Ab := (398551509/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (116413417/125000000 : ℝ) ^ p + (99315261/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (116413417/125000000 : ℝ)) (y := (99315261/100000000 : ℝ)) (X := (16143910406039/100000000000000 : ℝ)) (Y := (16771221504339/20000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99315261/100000000 : ℝ) ^ p + (116413417/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (99315261/100000000 : ℝ)) (y := (116413417/125000000 : ℝ)) (X := (16771221504339/20000000000000 : ℝ)) (Y := (16143910406039/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (962229973/500000000 : ℝ)) (τ := (116413417/125000000 : ℝ)) (σ := (99315261/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797327253/841177280 : ℝ) ^ p + (415814593/420588640 : ℝ) ^ p := by
    exact cert_lt (x := (797327253/841177280 : ℝ)) (y := (415814593/420588640 : ℝ)) (X := (3170334255891/12500000000000 : ℝ)) (Y := (74637327460857/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (116413417/125000000 : ℝ)) (n' := (2628679/3125000 : ℝ)) (Ab := (797327253/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (931315431/1000000000 : ℝ) ^ p + (248287737/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (931315431/1000000000 : ℝ)) (y := (248287737/250000000 : ℝ)) (X := (807375329923/5000000000000 : ℝ)) (Y := (83852511646117/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248287737/250000000 : ℝ) ^ p + (931315431/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248287737/250000000 : ℝ)) (y := (931315431/1000000000 : ℝ)) (X := (83852511646117/100000000000000 : ℝ)) (Y := (807375329923/5000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924466379/1000000000 : ℝ)) (τ := (931315431/1000000000 : ℝ)) (σ := (248287737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (797335917/841186741 : ℝ) ^ p + (831638647/841186741 : ℝ) ^ p := by
    exact cert_lt (x := (797335917/841186741 : ℝ)) (y := (831638647/841186741 : ℝ)) (X := (3170303301721/12500000000000 : ℝ)) (Y := (2332424201107/3125000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (931315431/1000000000 : ℝ)) (n' := (841186741/1000000000 : ℝ)) (Ab := (797335917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (29103617/31250000 : ℝ) ^ p + (248287721/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (29103617/31250000 : ℝ)) (y := (248287721/250000000 : ℝ)) (X := (16147645663729/100000000000000 : ℝ)) (Y := (2620386661867/3125000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248287721/250000000 : ℝ) ^ p + (29103617/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (248287721/250000000 : ℝ)) (y := (29103617/31250000 : ℝ)) (X := (2620386661867/3125000000000 : ℝ)) (Y := (16147645663729/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481116657/250000000 : ℝ)) (τ := (29103617/31250000 : ℝ)) (σ := (248287721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (398668126/420593553 : ℝ) ^ p + (138606502/140197851 : ℝ) ^ p := by
    exact cert_lt (x := (398668126/420593553 : ℝ)) (y := (138606502/140197851 : ℝ)) (X := (3170302183739/12500000000000 : ℝ)) (Y := (74637583963467/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (29103617/31250000 : ℝ)) (n' := (420593553/500000000 : ℝ)) (Ab := (199334063/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232828939/250000000 : ℝ) ^ p + (993150881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232828939/250000000 : ℝ)) (y := (993150881/1000000000 : ℝ)) (X := (126153523401/781250000000 : ℝ)) (Y := (41926183344569/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993150881/1000000000 : ℝ) ^ p + (232828939/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993150881/1000000000 : ℝ)) (y := (232828939/250000000 : ℝ)) (X := (41926183344569/50000000000000 : ℝ)) (Y := (126153523401/781250000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1924466637/1000000000 : ℝ)) (τ := (232828939/250000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (159467253/168237424 : ℝ) ^ p + (415819513/420593560 : ℝ) ^ p := by
    exact cert_lt (x := (159467253/168237424 : ℝ)) (y := (415819513/420593560 : ℝ)) (X := (6340604312421/25000000000000 : ℝ)) (Y := (37318792164463/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232828939/250000000 : ℝ)) (n' := (10514839/12500000 : ℝ)) (Ab := (159467253/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (931315757/1000000000 : ℝ) ^ p + (993150881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931315757/1000000000 : ℝ)) (y := (993150881/1000000000 : ℝ)) (X := (4036912859907/25000000000000 : ℝ)) (Y := (41926183344569/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993150881/1000000000 : ℝ) ^ p + (931315757/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993150881/1000000000 : ℝ)) (y := (931315757/1000000000 : ℝ)) (X := (41926183344569/50000000000000 : ℝ)) (Y := (4036912859907/25000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (398668133/420593561 : ℝ) ^ p + (415819514/420593561 : ℝ) ^ p := by
    exact cert_lt (x := (398668133/420593561 : ℝ)) (y := (415819514/420593561 : ℝ)) (X := (25362416519563/100000000000000 : ℝ)) (Y := (37318792190567/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (833029802/902880149 : ℝ) ^ p + (898106102/902880149 : ℝ) ^ p := by
    exact cert_lt (x := (833029802/902880149 : ℝ)) (y := (898106102/902880149 : ℝ)) (X := (2540591677127/20000000000000 : ℝ)) (Y := (87297041821053/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1118349469/1194239702 : ℝ) ^ p + (592345804/597119851 : ℝ) ^ p := by
    exact cert_lt (x := (1118349469/1194239702 : ℝ)) (y := (592345804/597119851 : ℝ)) (X := (18592146834183/100000000000000 : ℝ)) (Y := (10175981720707/12500000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993150881/1000000000 : ℝ)) (U := (597119851/500000000 : ℝ)) (Ab := (416514901/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ)) (Ab := (1118349469/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab147
