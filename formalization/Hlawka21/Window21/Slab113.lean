import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 113, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab113 (p : ℝ) (hpa : (785/32 : ℝ) ≤ p) (hpb : p ≤ (393/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (417649717489/21430500000000 : ℝ) (5011771/500000000 : ℝ) (800000128583/4286100000000 : ℝ) (3033/2500 : ℝ) (38886989/20000000 : ℝ) (972139777/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193809431/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11151/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4631/10000 : ℝ)
      else (389/500 : ℝ) ≤ X j i ∧ X j i ≤ (5927/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (417649717489/21430500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5011771/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (184471179/200000000 : ℝ) ^ p + (994003077/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184471179/200000000 : ℝ)) (y := (994003077/1000000000 : ℝ)) (X := (6867364406363/50000000000000 : ℝ)) (Y := (86265290330743/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994003077/1000000000 : ℝ) ^ p + (184471179/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (994003077/1000000000 : ℝ)) (y := (184471179/200000000 : ℝ)) (X := (86265290330743/100000000000000 : ℝ)) (Y := (6867364406363/50000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (479089743/250000000 : ℝ)) (τ := (184471179/200000000 : ℝ)) (σ := (994003077/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (393439924/415776415 : ℝ) ^ p + (410764644/415776415 : ℝ) ^ p := by
    exact cert_lt (x := (393439924/415776415 : ℝ)) (y := (410764644/415776415 : ℝ)) (X := (257606195489/1000000000000 : ℝ)) (Y := (9279922737329/12500000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184471179/200000000 : ℝ)) (n' := (83155283/100000000 : ℝ)) (Ab := (98359981/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (463934007/500000000 : ℝ) ^ p + (496487593/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (463934007/500000000 : ℝ)) (y := (496487593/500000000 : ℝ)) (X := (1987421081017/12500000000000 : ℝ)) (Y := (84100648963773/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496487593/500000000 : ℝ) ^ p + (463934007/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496487593/500000000 : ℝ)) (y := (463934007/500000000 : ℝ)) (X := (84100648963773/100000000000000 : ℝ)) (Y := (1987421081017/12500000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1200527/625000 : ℝ)) (τ := (463934007/500000000 : ℝ)) (σ := (496487593/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (792807489/838046315 : ℝ) ^ p + (828022773/838046315 : ℝ) ^ p := by
    exact cert_lt (x := (792807489/838046315 : ℝ)) (y := (828022773/838046315 : ℝ)) (X := (25588035811103/100000000000000 : ℝ)) (Y := (74411965164283/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (463934007/500000000 : ℝ)) (n' := (167609263/200000000 : ℝ)) (Ab := (792807489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (116011983/125000000 : ℝ) ^ p + (992928929/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116011983/125000000 : ℝ)) (y := (992928929/1000000000 : ℝ)) (X := (7997772932947/50000000000000 : ℝ)) (Y := (84004471648371/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992928929/1000000000 : ℝ) ^ p + (116011983/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992928929/1000000000 : ℝ)) (y := (116011983/125000000 : ℝ)) (X := (84004471648371/100000000000000 : ℝ)) (Y := (7997772932947/50000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1921024793/1000000000 : ℝ)) (τ := (116011983/125000000 : ℝ)) (σ := (992928929/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (158610346/167662783 : ℝ) ^ p + (828290373/838313915 : ℝ) ^ p := by
    exact cert_lt (x := (158610346/167662783 : ℝ)) (y := (828290373/838313915 : ℝ)) (X := (12790486325829/50000000000000 : ℝ)) (Y := (18604757058449/25000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (116011983/125000000 : ℝ)) (n' := (167662783/200000000 : ℝ)) (Ab := (79305173/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (464052593/500000000 : ℝ) ^ p + (99292703/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (464052593/500000000 : ℝ)) (y := (99292703/100000000 : ℝ)) (X := (1999936576611/12500000000000 : ℝ)) (Y := (42000262756463/50000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99292703/100000000 : ℝ) ^ p + (464052593/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99292703/100000000 : ℝ)) (y := (464052593/500000000 : ℝ)) (X := (42000262756463/50000000000000 : ℝ)) (Y := (1999936576611/12500000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (240129027/125000000 : ℝ)) (τ := (464052593/500000000 : ℝ)) (σ := (99292703/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (396530861/419162431 : ℝ) ^ p + (414150660/419162431 : ℝ) ^ p := by
    exact cert_lt (x := (396530861/419162431 : ℝ)) (y := (414150660/419162431 : ℝ)) (X := (1598792768759/6250000000000 : ℝ)) (Y := (37209658544017/50000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (464052593/500000000 : ℝ)) (n' := (419162431/500000000 : ℝ)) (Ab := (396530861/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (29003299/31250000 : ℝ) ^ p + (124115869/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (29003299/31250000 : ℝ)) (y := (124115869/125000000 : ℝ)) (X := (3199930872783/20000000000000 : ℝ)) (Y := (5250022714511/6250000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124115869/125000000 : ℝ) ^ p + (29003299/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (124115869/125000000 : ℝ)) (y := (29003299/31250000 : ℝ)) (X := (5250022714511/6250000000000 : ℝ)) (Y := (3199930872783/20000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (48025813/25000000 : ℝ)) (τ := (29003299/31250000 : ℝ)) (σ := (124115869/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (793062132/838325311 : ℝ) ^ p + (828301769/838325311 : ℝ) ^ p := by
    exact cert_lt (x := (793062132/838325311 : ℝ)) (y := (828301769/838325311 : ℝ)) (X := (25580672608163/100000000000000 : ℝ)) (Y := (18604832233871/25000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (29003299/31250000 : ℝ)) (n' := (838325311/1000000000 : ℝ)) (Ab := (198265533/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (928105583/1000000000 : ℝ) ^ p + (992926949/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (928105583/1000000000 : ℝ)) (y := (992926949/1000000000 : ℝ)) (X := (3999915178857/25000000000000 : ℝ)) (Y := (84000357198307/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992926949/1000000000 : ℝ) ^ p + (928105583/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992926949/1000000000 : ℝ)) (y := (928105583/1000000000 : ℝ)) (X := (84000357198307/100000000000000 : ℝ)) (Y := (3999915178857/25000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (480258133/250000000 : ℝ)) (τ := (928105583/1000000000 : ℝ)) (σ := (992926949/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (793062148/838325329 : ℝ) ^ p + (828301787/838325329 : ℝ) ^ p := by
    exact cert_lt (x := (793062148/838325329 : ℝ)) (y := (828301787/838325329 : ℝ)) (X := (25580671793593/100000000000000 : ℝ)) (Y := (37209664705219/50000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (928105583/1000000000 : ℝ)) (n' := (838325329/1000000000 : ℝ)) (Ab := (198265537/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (185621117/200000000 : ℝ) ^ p + (248231737/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (185621117/200000000 : ℝ)) (y := (248231737/250000000 : ℝ)) (X := (1999957695287/12500000000000 : ℝ)) (Y := (84000355120351/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248231737/250000000 : ℝ) ^ p + (185621117/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248231737/250000000 : ℝ)) (y := (185621117/200000000 : ℝ)) (X := (84000355120351/100000000000000 : ℝ)) (Y := (1999957695287/12500000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1921032533/1000000000 : ℝ)) (τ := (185621117/200000000 : ℝ)) (σ := (248231737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (264354050/279441777 : ℝ) ^ p + (828301789/838325331 : ℝ) ^ p := by
    exact cert_lt (x := (264354050/279441777 : ℝ)) (y := (828301789/838325331 : ℝ)) (X := (25580671879147/100000000000000 : ℝ)) (Y := (7441932946321/10000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (185621117/200000000 : ℝ)) (n' := (838325331/1000000000 : ℝ)) (Ab := (15861243/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1921032533/1000000000 : ℝ)) (τ := (185621117/200000000 : ℝ)) (σ := (248231737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (185621117/200000000 : ℝ)) (n' := (838325331/1000000000 : ℝ)) (Ab := (15861243/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1921032533/1000000000 : ℝ)) (τ := (185621117/200000000 : ℝ)) (σ := (248231737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (185621117/200000000 : ℝ)) (n' := (838325331/1000000000 : ℝ)) (Ab := (15861243/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1921032533/1000000000 : ℝ)) (τ := (185621117/200000000 : ℝ)) (σ := (248231737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (185621117/200000000 : ℝ)) (n' := (838325331/1000000000 : ℝ)) (Ab := (15861243/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1921032533/1000000000 : ℝ)) (τ := (185621117/200000000 : ℝ)) (σ := (248231737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1661049872/1806190569 : ℝ) ^ p + (1796167027/1806190569 : ℝ) ^ p := by
    exact cert_lt (x := (1661049872/1806190569 : ℝ)) (y := (1796167027/1806190569 : ℝ)) (X := (3193994737973/25000000000000 : ℝ)) (Y := (87224021276611/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1115054291/1193809431 : ℝ) ^ p + (1183785889/1193809431 : ℝ) ^ p := by
    exact cert_lt (x := (1115054291/1193809431 : ℝ)) (y := (1183785889/1193809431 : ℝ)) (X := (4676621952703/25000000000000 : ℝ)) (Y := (81293512877183/100000000000000 : ℝ)) 393 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248231737/250000000 : ℝ)) (U := (1193809431/1000000000 : ℝ)) (Ab := (103815617/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (185621117/200000000 : ℝ)) (σ := (248231737/250000000 : ℝ)) (Ab := (1115054291/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab113
