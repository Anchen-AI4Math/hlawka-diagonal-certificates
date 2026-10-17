import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 54, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab054 (p : ℝ) (hpa : (235/8 : ℝ) ≤ p) (hpb : p ≤ (471/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (71672862569/5205250000000 : ℝ) (7049057/1000000000 : ℝ) (320000062463/2082100000000 : ℝ) (591/500 : ℝ) (976728653/500000000 : ℝ) (24416993/25000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578731267/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10887/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(349/625 : ℝ)
      else (103/125 : ℝ) ≤ X j i ∧ X j i ≤ (5747/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (71672862569/5205250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7049057/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (941235581/1000000000 : ℝ) ^ p + (993764737/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (941235581/1000000000 : ℝ)) (y := (993764737/1000000000 : ℝ)) (X := (16816854707453/100000000000000 : ℝ)) (Y := (41591583120899/50000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993764737/1000000000 : ℝ) ^ p + (941235581/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993764737/1000000000 : ℝ)) (y := (941235581/1000000000 : ℝ)) (X := (41591583120899/50000000000000 : ℝ)) (Y := (16816854707453/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (967500159/500000000 : ℝ)) (τ := (941235581/1000000000 : ℝ)) (σ := (993764737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (824166218/868582059 : ℝ) ^ p + (861533002/868582059 : ℝ) ^ p := by
    exact cert_lt (x := (824166218/868582059 : ℝ)) (y := (861533002/868582059 : ℝ)) (X := (10663785904081/50000000000000 : ℝ)) (Y := (78672429628087/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (941235581/1000000000 : ℝ)) (n' := (868582059/1000000000 : ℝ)) (Ab := (412083109/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (944476413/1000000000 : ℝ) ^ p + (993030361/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944476413/1000000000 : ℝ)) (y := (993030361/1000000000 : ℝ)) (X := (18607519875203/100000000000000 : ℝ)) (Y := (81392499280011/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993030361/1000000000 : ℝ) ^ p + (944476413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993030361/1000000000 : ℝ)) (y := (944476413/1000000000 : ℝ)) (X := (81392499280011/100000000000000 : ℝ)) (Y := (18607519875203/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (968753387/500000000 : ℝ)) (τ := (944476413/1000000000 : ℝ)) (σ := (993030361/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (206893740/218071643 : ℝ) ^ p + (865237515/872286572 : ℝ) ^ p := by
    exact cert_lt (x := (206893740/218071643 : ℝ)) (y := (865237515/872286572 : ℝ)) (X := (21247058059679/100000000000000 : ℝ)) (Y := (78752943204127/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (944476413/1000000000 : ℝ)) (n' := (218071643/250000000 : ℝ)) (Ab := (10344687/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (472282543/500000000 : ℝ) ^ p + (248252253/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (472282543/500000000 : ℝ)) (y := (248252253/250000000 : ℝ)) (X := (18659015409577/100000000000000 : ℝ)) (Y := (40670501991523/50000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248252253/250000000 : ℝ) ^ p + (472282543/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248252253/250000000 : ℝ)) (y := (472282543/500000000 : ℝ)) (X := (40670501991523/50000000000000 : ℝ)) (Y := (18659015409577/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (968787049/500000000 : ℝ)) (τ := (472282543/500000000 : ℝ)) (σ := (248252253/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (827668057/872387755 : ℝ) ^ p + (45544142/45915145 : ℝ) ^ p := by
    exact cert_lt (x := (827668057/872387755 : ℝ)) (y := (45544142/45915145 : ℝ)) (X := (10622433501353/50000000000000 : ℝ)) (Y := (9844391728127/12500000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (472282543/500000000 : ℝ)) (n' := (174477551/200000000 : ℝ)) (Ab := (827668057/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (944567499/1000000000 : ℝ) ^ p + (99300843/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (944567499/1000000000 : ℝ)) (y := (99300843/100000000 : ℝ)) (X := (2332552330753/12500000000000 : ℝ)) (Y := (40669800299349/50000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99300843/100000000 : ℝ) ^ p + (944567499/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99300843/100000000 : ℝ)) (y := (944567499/1000000000 : ℝ)) (X := (40669800299349/50000000000000 : ℝ)) (Y := (2332552330753/12500000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1937575929/1000000000 : ℝ)) (τ := (944567499/1000000000 : ℝ)) (σ := (99300843/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (413835295/436195254 : ℝ) ^ p + (865341451/872390508 : ℝ) ^ p := by
    exact cert_lt (x := (413835295/436195254 : ℝ)) (y := (865341451/872390508 : ℝ)) (X := (21244807402019/100000000000000 : ℝ)) (Y := (7875519342143/10000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (944567499/1000000000 : ℝ)) (n' := (218097627/250000000 : ℝ)) (Ab := (82767059/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (188913513/200000000 : ℝ) ^ p + (496504207/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (188913513/200000000 : ℝ)) (y := (496504207/500000000 : ℝ)) (X := (18660457028561/100000000000000 : ℝ)) (Y := (16267912403603/20000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496504207/500000000 : ℝ) ^ p + (188913513/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496504207/500000000 : ℝ)) (y := (188913513/200000000 : ℝ)) (X := (16267912403603/20000000000000 : ℝ)) (Y := (18660457028561/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1937575979/1000000000 : ℝ)) (τ := (188913513/200000000 : ℝ)) (σ := (496504207/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (206917665/218097646 : ℝ) ^ p + (865341527/872390584 : ℝ) ^ p := by
    exact cert_lt (x := (206917665/218097646 : ℝ)) (y := (865341527/872390584 : ℝ)) (X := (10622402906059/50000000000000 : ℝ)) (Y := (78755195066659/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (188913513/200000000 : ℝ)) (n' := (109048823/125000000 : ℝ)) (Ab := (41383533/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (472283783/500000000 : ℝ) ^ p + (496504207/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (472283783/500000000 : ℝ)) (y := (496504207/500000000 : ℝ)) (X := (3732091522023/20000000000000 : ℝ)) (Y := (16267912403603/20000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496504207/500000000 : ℝ) ^ p + (472283783/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496504207/500000000 : ℝ)) (y := (472283783/500000000 : ℝ)) (X := (16267912403603/20000000000000 : ℝ)) (Y := (3732091522023/20000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (96878799/50000000 : ℝ)) (τ := (472283783/500000000 : ℝ)) (σ := (496504207/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (827670661/872390585 : ℝ) ^ p + (865341528/872390585 : ℝ) ^ p := by
    exact cert_lt (x := (827670661/872390585 : ℝ)) (y := (865341528/872390585 : ℝ)) (X := (21244805850851/100000000000000 : ℝ)) (Y := (78755195088307/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (472283783/500000000 : ℝ)) (n' := (174478117/200000000 : ℝ)) (Ab := (827670661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (96878799/50000000 : ℝ)) (τ := (472283783/500000000 : ℝ)) (σ := (496504207/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (472283783/500000000 : ℝ)) (n' := (174478117/200000000 : ℝ)) (Ab := (827670661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (96878799/50000000 : ℝ)) (τ := (472283783/500000000 : ℝ)) (σ := (496504207/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (472283783/500000000 : ℝ)) (n' := (174478117/200000000 : ℝ)) (Ab := (827670661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (96878799/50000000 : ℝ)) (τ := (472283783/500000000 : ℝ)) (σ := (496504207/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (472283783/500000000 : ℝ)) (n' := (174478117/200000000 : ℝ)) (Ab := (827670661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (96878799/50000000 : ℝ)) (τ := (472283783/500000000 : ℝ)) (σ := (496504207/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (472283783/500000000 : ℝ)) (n' := (174478117/200000000 : ℝ)) (Ab := (827670661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (96878799/50000000 : ℝ)) (τ := (472283783/500000000 : ℝ)) (σ := (496504207/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (853833527/921268733 : ℝ) ^ p + (1835488409/1842537466 : ℝ) ^ p := by
    exact cert_lt (x := (853833527/921268733 : ℝ)) (y := (1835488409/1842537466 : ℝ)) (X := (5335142856741/50000000000000 : ℝ)) (Y := (89329714607389/100000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (544323903/578731267 : ℝ) ^ p + (1150413477/1157462534 : ℝ) ^ p := by
    exact cert_lt (x := (544323903/578731267 : ℝ)) (y := (1150413477/1157462534 : ℝ)) (X := (16458387193519/100000000000000 : ℝ)) (Y := (3341664546679/4000000000000 : ℝ)) 471 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496504207/500000000 : ℝ)) (U := (578731267/500000000 : ℝ)) (Ab := (853833527/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (472283783/500000000 : ℝ)) (σ := (496504207/500000000 : ℝ)) (Ab := (544323903/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab054
