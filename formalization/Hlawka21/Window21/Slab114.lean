import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 114, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab114 (p : ℝ) (hpa : (393/16 : ℝ) ≤ p) (hpb : p ≤ (787/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (104396382091/5364450000000 : ℝ) (10008891/1000000000 : ℝ) (2000000321867/10728900000000 : ℝ) (3033/2500 : ℝ) (486104793/250000000 : ℝ) (243043681/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193822131/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(697/625 : ℝ) ≤ X j i ∧ X j i ≤ -(4633/10000 : ℝ)
      else (3891/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5927/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (104396382091/5364450000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10008891/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (115307441/125000000 : ℝ) ^ p + (497004573/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115307441/125000000 : ℝ)) (y := (497004573/500000000 : ℝ)) (X := (6868994685657/50000000000000 : ℝ)) (Y := (86262028829829/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497004573/500000000 : ℝ) ^ p + (115307441/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (497004573/500000000 : ℝ)) (y := (115307441/125000000 : ℝ)) (X := (86262028829829/100000000000000 : ℝ)) (Y := (6868994685657/50000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958234337/500000000 : ℝ)) (τ := (115307441/125000000 : ℝ)) (σ := (497004573/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (787016620/831648173 : ℝ) ^ p + (821639282/831648173 : ℝ) ^ p := by
    exact cert_lt (x := (787016620/831648173 : ℝ)) (y := (821639282/831648173 : ℝ)) (X := (25753642729561/100000000000000 : ℝ)) (Y := (18561589629613/25000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115307441/125000000 : ℝ)) (n' := (831648173/1000000000 : ℝ)) (Ab := (39350831/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (927967349/1000000000 : ℝ) ^ p + (496490921/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (927967349/1000000000 : ℝ)) (y := (496490921/500000000 : ℝ)) (X := (7952015852503/50000000000000 : ℝ)) (Y := (84095985996851/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496490921/500000000 : ℝ) ^ p + (927967349/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496490921/500000000 : ℝ)) (y := (927967349/1000000000 : ℝ)) (X := (84095985996851/100000000000000 : ℝ)) (Y := (7952015852503/50000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1920949191/1000000000 : ℝ)) (τ := (927967349/1000000000 : ℝ)) (σ := (496490921/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (792939371/838135623 : ℝ) ^ p + (276042244/279378541 : ℝ) ^ p := by
    exact cert_lt (x := (792939371/838135623 : ℝ)) (y := (276042244/279378541 : ℝ)) (X := (6395319650981/25000000000000 : ℝ)) (Y := (74418722910591/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (927967349/1000000000 : ℝ)) (n' := (838135623/1000000000 : ℝ)) (Ab := (792939371/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (928194627/1000000000 : ℝ) ^ p + (99293569/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (928194627/1000000000 : ℝ)) (y := (99293569/100000000 : ℝ)) (X := (3200021411929/20000000000000 : ℝ)) (Y := (671999286661/800000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99293569/100000000 : ℝ) ^ p + (928194627/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99293569/100000000 : ℝ)) (y := (928194627/1000000000 : ℝ)) (X := (671999286661/800000000000 : ℝ)) (Y := (3200021411929/20000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1921130317/1000000000 : ℝ)) (τ := (928194627/1000000000 : ℝ)) (σ := (99293569/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (793182989/838402513 : ℝ) ^ p + (828393622/838402513 : ℝ) ^ p := by
    exact cert_lt (x := (793182989/838402513 : ℝ)) (y := (828393622/838402513 : ℝ)) (X := (1022969445013/4000000000000 : ℝ)) (Y := (37212882451597/50000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (928194627/1000000000 : ℝ)) (n' := (838402513/1000000000 : ℝ)) (Ab := (793182989/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (928203911/1000000000 : ℝ) ^ p + (496466899/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (928203911/1000000000 : ℝ)) (y := (496466899/500000000 : ℝ)) (X := (4001010855273/25000000000000 : ℝ)) (Y := (83995974481529/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496466899/500000000 : ℝ) ^ p + (928203911/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496466899/500000000 : ℝ)) (y := (928203911/1000000000 : ℝ)) (X := (83995974481529/100000000000000 : ℝ)) (Y := (4001010855273/25000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1921137709/1000000000 : ℝ)) (τ := (928203911/1000000000 : ℝ)) (σ := (496466899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (396596470/419206707 : ℝ) ^ p + (92044947/93157046 : ℝ) ^ p := by
    exact cert_lt (x := (396596470/419206707 : ℝ)) (y := (92044947/93157046 : ℝ)) (X := (25573949036929/100000000000000 : ℝ)) (Y := (37213026224223/50000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (928203911/1000000000 : ℝ)) (n' := (419206707/500000000 : ℝ)) (Ab := (39659647/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (928204289/1000000000 : ℝ) ^ p + (992933721/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (928204289/1000000000 : ℝ)) (y := (992933721/1000000000 : ℝ)) (X := (16004203710553/100000000000000 : ℝ)) (Y := (83995814284941/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992933721/1000000000 : ℝ) ^ p + (928204289/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992933721/1000000000 : ℝ)) (y := (928204289/1000000000 : ℝ)) (X := (83995814284941/100000000000000 : ℝ)) (Y := (16004203710553/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (192113801/100000000 : ℝ)) (τ := (928204289/1000000000 : ℝ)) (σ := (992933721/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (793193345/838413858 : ℝ) ^ p + (276134989/279471286 : ℝ) ^ p := by
    exact cert_lt (x := (793193345/838413858 : ℝ)) (y := (276134989/279471286 : ℝ)) (X := (12786968550551/50000000000000 : ℝ)) (Y := (9303258020011/12500000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (928204289/1000000000 : ℝ)) (n' := (419206929/500000000 : ℝ)) (Ab := (158638669/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (464102153/500000000 : ℝ) ^ p + (992933717/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464102153/500000000 : ℝ)) (y := (992933717/1000000000 : ℝ)) (X := (8002105459687/50000000000000 : ℝ)) (Y := (10499475745381/12500000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992933717/1000000000 : ℝ) ^ p + (464102153/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992933717/1000000000 : ℝ)) (y := (464102153/500000000 : ℝ)) (X := (10499475745381/12500000000000 : ℝ)) (Y := (8002105459687/50000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921138023/1000000000 : ℝ)) (τ := (464102153/500000000 : ℝ)) (σ := (992933717/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (793193363/838413878 : ℝ) ^ p + (828404987/838413878 : ℝ) ^ p := by
    exact cert_lt (x := (793193363/838413878 : ℝ)) (y := (828404987/838413878 : ℝ)) (X := (12786968185287/50000000000000 : ℝ)) (Y := (74426064687639/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (464102153/500000000 : ℝ)) (n' := (419206939/500000000 : ℝ)) (Ab := (793193363/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1921138023/1000000000 : ℝ)) (τ := (464102153/500000000 : ℝ)) (σ := (992933717/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (464102153/500000000 : ℝ)) (n' := (419206939/500000000 : ℝ)) (Ab := (793193363/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1921138023/1000000000 : ℝ)) (τ := (464102153/500000000 : ℝ)) (σ := (992933717/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (464102153/500000000 : ℝ)) (n' := (419206939/500000000 : ℝ)) (Ab := (793193363/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1921138023/1000000000 : ℝ)) (τ := (464102153/500000000 : ℝ)) (σ := (992933717/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (464102153/500000000 : ℝ)) (n' := (419206939/500000000 : ℝ)) (Ab := (793193363/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1921138023/1000000000 : ℝ)) (τ := (464102153/500000000 : ℝ)) (σ := (992933717/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (464102153/500000000 : ℝ)) (n' := (419206939/500000000 : ℝ)) (Ab := (793193363/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1921138023/1000000000 : ℝ)) (τ := (464102153/500000000 : ℝ)) (σ := (992933717/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1661203138/1806177869 : ℝ) ^ p + (1796168978/1806177869 : ℝ) ^ p := by
    exact cert_lt (x := (1661203138/1806177869 : ℝ)) (y := (1796168978/1806177869 : ℝ)) (X := (6386867120187/50000000000000 : ℝ)) (Y := (87226266087187/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1115154358/1193822131 : ℝ) ^ p + (1183813240/1193822131 : ℝ) ^ p := by
    exact cert_lt (x := (1115154358/1193822131 : ℝ)) (y := (1183813240/1193822131 : ℝ)) (X := (18702983660457/100000000000000 : ℝ)) (Y := (81297016788579/100000000000000 : ℝ)) 787 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992933717/1000000000 : ℝ)) (U := (1193822131/1000000000 : ℝ)) (Ab := (830601569/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (464102153/500000000 : ℝ)) (σ := (992933717/1000000000 : ℝ)) (Ab := (557577179/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab114
