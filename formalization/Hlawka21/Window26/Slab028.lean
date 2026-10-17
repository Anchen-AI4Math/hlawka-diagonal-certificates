import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 28, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab028 (p : ℝ) (hpa : (111/4 : ℝ) ≤ p) (hpb : p ≤ (445/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (72173855699/4917300000000 : ℝ) (1881097/250000000 : ℝ) (800000147519/4917300000000 : ℝ) (591/500 : ℝ) (975385847/500000000 : ℝ) (975331099/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578239259/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5421/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5529/10000 : ℝ)
      else (1023/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11481/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (72173855699/4917300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1881097/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (187526163/200000000 : ℝ) ^ p + (248365333/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (187526163/200000000 : ℝ)) (y := (248365333/250000000 : ℝ)) (X := (416942768253/2500000000000 : ℝ)) (Y := (41661154458449/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248365333/250000000 : ℝ) ^ p + (187526163/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248365333/250000000 : ℝ)) (y := (187526163/200000000 : ℝ)) (X := (41661154458449/50000000000000 : ℝ)) (Y := (416942768253/2500000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1931092147/1000000000 : ℝ)) (τ := (187526163/200000000 : ℝ)) (σ := (248365333/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819208350/865675379 : ℝ) ^ p + (858150991/865675379 : ℝ) ^ p := by
    exact cert_lt (x := (819208350/865675379 : ℝ)) (y := (858150991/865675379 : ℝ)) (X := (21557240058491/100000000000000 : ℝ)) (Y := (78442761107661/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187526163/200000000 : ℝ)) (n' := (865675379/1000000000 : ℝ)) (Ab := (16384167/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (941004709/1000000000 : ℝ) ^ p + (39708099/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (941004709/1000000000 : ℝ)) (y := (39708099/40000000 : ℝ)) (X := (18429851965509/100000000000000 : ℝ)) (Y := (40785083213243/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (39708099/40000000 : ℝ) ^ p + (941004709/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39708099/40000000 : ℝ)) (y := (941004709/1000000000 : ℝ)) (X := (40785083213243/50000000000000 : ℝ)) (Y := (18429851965509/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (120856699/62500000 : ℝ)) (τ := (941004709/1000000000 : ℝ)) (σ := (39708099/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822760471/869553003 : ℝ) ^ p + (862028615/869553003 : ℝ) ^ p := by
    exact cert_lt (x := (822760471/869553003 : ℝ)) (y := (862028615/869553003 : ℝ)) (X := (21471890971911/100000000000000 : ℝ)) (Y := (7852810995831/10000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (941004709/1000000000 : ℝ)) (n' := (869553003/1000000000 : ℝ)) (Ab := (822760471/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (29409501/31250000 : ℝ) ^ p + (24816969/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (29409501/31250000 : ℝ)) (y := (24816969/25000000 : ℝ)) (X := (4621007853183/25000000000000 : ℝ)) (Y := (5094749172577/6250000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24816969/25000000 : ℝ) ^ p + (29409501/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (24816969/25000000 : ℝ)) (y := (29409501/31250000 : ℝ)) (X := (5094749172577/6250000000000 : ℝ)) (Y := (4621007853183/25000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (241722849/125000000 : ℝ)) (τ := (29409501/31250000 : ℝ)) (σ := (24816969/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822864841/869666946 : ℝ) ^ p + (431071279/434833473 : ℝ) ^ p := by
    exact cert_lt (x := (822864841/869666946 : ℝ)) (y := (431071279/434833473 : ℝ)) (X := (858775739929/4000000000000 : ℝ)) (Y := (15706121549771/20000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (29409501/31250000 : ℝ)) (n' := (434833473/500000000 : ℝ)) (Ab := (822864841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (941106939/1000000000 : ℝ) ^ p + (198535613/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (941106939/1000000000 : ℝ)) (y := (198535613/200000000 : ℝ)) (X := (9242809727593/50000000000000 : ℝ)) (Y := (81514399476579/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198535613/200000000 : ℝ) ^ p + (941106939/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198535613/200000000 : ℝ)) (y := (941106939/1000000000 : ℝ)) (X := (81514399476579/100000000000000 : ℝ)) (Y := (9242809727593/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (483446251/250000000 : ℝ)) (τ := (941106939/1000000000 : ℝ)) (σ := (198535613/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822867896/869670281 : ℝ) ^ p + (862145893/869670281 : ℝ) ^ p := by
    exact cert_lt (x := (822867896/869670281 : ℝ)) (y := (862145893/869670281 : ℝ)) (X := (21469320553259/100000000000000 : ℝ)) (Y := (2454083776501/3125000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (941106939/1000000000 : ℝ)) (n' := (869670281/1000000000 : ℝ)) (Ab := (102858487/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (58819189/62500000 : ℝ) ^ p + (248169511/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (58819189/62500000 : ℝ)) (y := (248169511/250000000 : ℝ)) (X := (3697133178231/20000000000000 : ℝ)) (Y := (20378587878981/25000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248169511/250000000 : ℝ) ^ p + (58819189/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248169511/250000000 : ℝ)) (y := (58819189/62500000 : ℝ)) (X := (20378587878981/25000000000000 : ℝ)) (Y := (3697133178231/20000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (483446267/250000000 : ℝ)) (τ := (58819189/62500000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (822867985/869670379 : ℝ) ^ p + (862145991/869670379 : ℝ) ^ p := by
    exact cert_lt (x := (822867985/869670379 : ℝ)) (y := (862145991/869670379 : ℝ)) (X := (858772713979/4000000000000 : ℝ)) (Y := (78530682996067/100000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (58819189/62500000 : ℝ)) (n' := (869670379/1000000000 : ℝ)) (Ab := (164573597/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470553513/500000000 : ℝ) ^ p + (248169511/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (470553513/500000000 : ℝ)) (y := (248169511/250000000 : ℝ)) (X := (2310708372971/12500000000000 : ℝ)) (Y := (20378587878981/25000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248169511/250000000 : ℝ) ^ p + (470553513/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248169511/250000000 : ℝ)) (y := (470553513/500000000 : ℝ)) (X := (20378587878981/25000000000000 : ℝ)) (Y := (2310708372971/12500000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (274289329/289890127 : ℝ) ^ p + (862145993/869670381 : ℝ) ^ p := by
    exact cert_lt (x := (274289329/289890127 : ℝ)) (y := (862145993/869670381 : ℝ)) (X := (10734658963789/50000000000000 : ℝ)) (Y := (2454083844997/3125000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (n' := (869670381/1000000000 : ℝ)) (Ab := (822867987/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (193378507/100000000 : ℝ)) (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (154679403/167592862 : ℝ) ^ p + (917998547/921760741 : ℝ) ^ p := by
    exact cert_lt (x := (154679403/167592862 : ℝ)) (y := (917998547/921760741 : ℝ)) (X := (2150376300913/20000000000000 : ℝ)) (Y := (44624059351087/50000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (542086421/578239259 : ℝ) ^ p + (574477065/578239259 : ℝ) ^ p := by
    exact cert_lt (x := (542086421/578239259 : ℝ)) (y := (574477065/578239259 : ℝ)) (X := (16602138744271/100000000000000 : ℝ)) (Y := (3335914470897/4000000000000 : ℝ)) 445 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248169511/250000000 : ℝ)) (U := (578239259/500000000 : ℝ)) (Ab := (1701473433/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470553513/500000000 : ℝ)) (σ := (248169511/250000000 : ℝ)) (Ab := (542086421/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab028
