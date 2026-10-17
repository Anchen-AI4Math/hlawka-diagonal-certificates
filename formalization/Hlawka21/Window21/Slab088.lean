import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 88, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab088 (p : ℝ) (hpa : (95/4 : ℝ) ≤ p) (hpb : p ≤ (761/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (26206630837/1296750000000 : ℝ) (1040399/100000000 : ℝ) (100000015561/518700000000 : ℝ) (3033/2500 : ℝ) (485636939/250000000 : ℝ) (242809157/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193491347/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(89/80 : ℝ) ≤ X j i ∧ X j i ≤ -(1147/2500 : ℝ)
      else (7737/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (26206630837/1296750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1040399/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (459836219/500000000 : ℝ) ^ p + (993847421/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459836219/500000000 : ℝ)) (y := (993847421/1000000000 : ℝ)) (X := (106645216873/781250000000 : ℝ)) (Y := (43174714909057/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993847421/1000000000 : ℝ) ^ p + (459836219/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993847421/1000000000 : ℝ)) (y := (459836219/500000000 : ℝ)) (X := (43174714909057/50000000000000 : ℝ)) (Y := (106645216873/781250000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913519859/1000000000 : ℝ)) (τ := (459836219/500000000 : ℝ)) (σ := (993847421/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (261113939/276357568 : ℝ) ^ p + (409334357/414536352 : ℝ) ^ p := by
    exact cert_lt (x := (261113939/276357568 : ℝ)) (y := (409334357/414536352 : ℝ)) (X := (12970865312727/50000000000000 : ℝ)) (Y := (74058270337493/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459836219/500000000 : ℝ)) (n' := (12954261/15625000 : ℝ)) (Ab := (783341817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (925292123/1000000000 : ℝ) ^ p + (992805139/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925292123/1000000000 : ℝ)) (y := (992805139/1000000000 : ℝ)) (X := (3944657199351/25000000000000 : ℝ)) (Y := (2631918363783/3125000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992805139/1000000000 : ℝ) ^ p + (925292123/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992805139/1000000000 : ℝ)) (y := (925292123/1000000000 : ℝ)) (X := (2631918363783/3125000000000 : ℝ)) (Y := (3944657199351/25000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (959048631/500000000 : ℝ)) (τ := (925292123/1000000000 : ℝ)) (σ := (992805139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (10525231/11142915 : ℝ) ^ p + (165062927/167143725 : ℝ) ^ p := by
    exact cert_lt (x := (10525231/11142915 : ℝ)) (y := (165062927/167143725 : ℝ)) (X := (1030541432027/4000000000000 : ℝ)) (Y := (37118232581541/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (925292123/1000000000 : ℝ)) (n' := (6685749/8000000 : ℝ)) (Ab := (31575693/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925534957/1000000000 : ℝ) ^ p + (124094519/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (925534957/1000000000 : ℝ)) (y := (124094519/125000000 : ℝ)) (X := (7938700343451/50000000000000 : ℝ)) (Y := (42061308277643/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124094519/125000000 : ℝ) ^ p + (925534957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124094519/125000000 : ℝ)) (y := (925534957/1000000000 : ℝ)) (X := (42061308277643/50000000000000 : ℝ)) (Y := (7938700343451/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918291109/1000000000 : ℝ)) (τ := (925534957/1000000000 : ℝ)) (σ := (124094519/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (394826459/418002456 : ℝ) ^ p + (412800461/418002456 : ℝ) ^ p := by
    exact cert_lt (x := (394826459/418002456 : ℝ)) (y := (412800461/418002456 : ℝ)) (X := (6438978586593/25000000000000 : ℝ)) (Y := (37122043384561/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925534957/1000000000 : ℝ)) (n' := (52250307/62500000 : ℝ)) (Ab := (394826459/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (925545341/1000000000 : ℝ) ^ p + (992754049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925545341/1000000000 : ℝ)) (y := (992754049/1000000000 : ℝ)) (X := (7940818760403/50000000000000 : ℝ)) (Y := (84118378821631/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992754049/1000000000 : ℝ) ^ p + (925545341/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992754049/1000000000 : ℝ)) (y := (925545341/1000000000 : ℝ)) (X := (84118378821631/100000000000000 : ℝ)) (Y := (7940818760403/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (191829939/100000000 : ℝ)) (τ := (925545341/1000000000 : ℝ)) (σ := (992754049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (263221353/278672384 : ℝ) ^ p + (412806581/418008576 : ℝ) ^ p := by
    exact cert_lt (x := (263221353/278672384 : ℝ)) (y := (412806581/418008576 : ℝ)) (X := (643889707389/2500000000000 : ℝ)) (Y := (7424441252589/10000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (925545341/1000000000 : ℝ)) (n' := (1632846/1953125 : ℝ)) (Ab := (789664059/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (185109157/200000000 : ℝ) ^ p + (992753959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185109157/200000000 : ℝ)) (y := (992753959/1000000000 : ℝ)) (X := (15881818703871/100000000000000 : ℝ)) (Y := (2102954936703/2500000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992753959/1000000000 : ℝ) ^ p + (185109157/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992753959/1000000000 : ℝ)) (y := (185109157/200000000 : ℝ)) (X := (2102954936703/2500000000000 : ℝ)) (Y := (15881818703871/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (59946867/31250000 : ℝ)) (τ := (185109157/200000000 : ℝ)) (σ := (992753959/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (197416134/209004419 : ℝ) ^ p + (412806843/418008838 : ℝ) ^ p := by
    exact cert_lt (x := (197416134/209004419 : ℝ)) (y := (412806843/418008838 : ℝ)) (X := (12877787187623/50000000000000 : ℝ)) (Y := (4640276654469/6250000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (185109157/200000000 : ℝ)) (n' := (209004419/250000000 : ℝ)) (Ab := (98708067/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925545803/1000000000 : ℝ) ^ p + (248188489/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925545803/1000000000 : ℝ)) (y := (248188489/250000000 : ℝ)) (X := (3970456512293/25000000000000 : ℝ)) (Y := (8411819142301/10000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248188489/250000000 : ℝ) ^ p + (925545803/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248188489/250000000 : ℝ)) (y := (925545803/1000000000 : ℝ)) (X := (8411819142301/10000000000000 : ℝ)) (Y := (3970456512293/25000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789664556/836017697 : ℝ) ^ p + (825613707/836017697 : ℝ) ^ p := by
    exact cert_lt (x := (789664556/836017697 : ℝ)) (y := (825613707/836017697 : ℝ)) (X := (12877787251361/50000000000000 : ℝ)) (Y := (74244427030393/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (n' := (836017697/1000000000 : ℝ)) (Ab := (197416139/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918299759/1000000000 : ℝ)) (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1657092566/1806508653 : ℝ) ^ p + (1796104663/1806508653 : ℝ) ^ p := by
    exact cert_lt (x := (1657092566/1806508653 : ℝ)) (y := (1796104663/1806508653 : ℝ)) (X := (12834028608657/100000000000000 : ℝ)) (Y := (43582985796099/50000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1112486192/1193491347 : ℝ) ^ p + (1183087357/1193491347 : ℝ) ^ p := by
    exact cert_lt (x := (1112486192/1193491347 : ℝ)) (y := (1183087357/1193491347 : ℝ)) (X := (18796880376759/100000000000000 : ℝ)) (Y := (81203120069197/100000000000000 : ℝ)) 761 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248188489/250000000 : ℝ)) (U := (1193491347/1000000000 : ℝ)) (Ab := (828546283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925545803/1000000000 : ℝ)) (σ := (248188489/250000000 : ℝ)) (Ab := (69530387/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab088
