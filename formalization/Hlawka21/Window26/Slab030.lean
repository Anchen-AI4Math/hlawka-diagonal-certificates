import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 30, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab030 (p : ℝ) (hpa : (223/8 : ℝ) ≤ p) (hpb : p ≤ (447/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (360666289693/24697250000000 : ℝ) (3742797/500000000 : ℝ) (1600000296367/9878900000000 : ℝ) (591/500 : ℝ) (975494617/500000000 : ℝ) (30482511/31250000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231311289/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5423/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5533/10000 : ℝ)
      else (8189/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5741/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (360666289693/24697250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3742797/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (187584737/200000000 : ℝ) ^ p + (198697137/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (187584737/200000000 : ℝ)) (y := (198697137/200000000 : ℝ)) (X := (16688973177613/100000000000000 : ℝ)) (Y := (83311045680461/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198697137/200000000 : ℝ) ^ p + (187584737/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198697137/200000000 : ℝ)) (y := (187584737/200000000 : ℝ)) (X := (83311045680461/100000000000000 : ℝ)) (Y := (16688973177613/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193140937/100000000 : ℝ)) (τ := (187584737/200000000 : ℝ)) (σ := (198697137/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (163922059/173182656 : ℝ) ^ p + (143071281/144318880 : ℝ) ^ p := by
    exact cert_lt (x := (163922059/173182656 : ℝ)) (y := (143071281/144318880 : ℝ)) (X := (6730786877/31250000000 : ℝ)) (Y := (78461482746639/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187584737/200000000 : ℝ)) (n' := (2705979/3125000 : ℝ)) (Ab := (163922059/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (94128713/100000000 : ℝ) ^ p + (992728721/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94128713/100000000 : ℝ)) (y := (992728721/1000000000 : ℝ)) (X := (18444281744971/100000000000000 : ℝ)) (Y := (81555737354331/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992728721/1000000000 : ℝ) ^ p + (94128713/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992728721/1000000000 : ℝ)) (y := (94128713/100000000 : ℝ)) (X := (81555737354331/100000000000000 : ℝ)) (Y := (18444281744971/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1934015851/1000000000 : ℝ)) (τ := (94128713/100000000 : ℝ)) (σ := (992728721/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (823151131/869777190 : ℝ) ^ p + (143715266/144962865 : ℝ) ^ p := by
    exact cert_lt (x := (823151131/869777190 : ℝ)) (y := (143715266/144962865 : ℝ)) (X := (2145355915741/10000000000000 : ℝ)) (Y := (78546442296967/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (94128713/100000000 : ℝ)) (n' := (86977719/100000000 : ℝ)) (Ab := (823151131/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (94138557/100000000 : ℝ) ^ p + (992705201/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94138557/100000000 : ℝ)) (y := (992705201/1000000000 : ℝ)) (X := (18498246551767/100000000000000 : ℝ)) (Y := (81501772599261/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992705201/1000000000 : ℝ) ^ p + (94138557/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992705201/1000000000 : ℝ)) (y := (94138557/100000000 : ℝ)) (X := (81501772599261/100000000000000 : ℝ)) (Y := (18498246551767/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1934090771/1000000000 : ℝ)) (τ := (94138557/100000000 : ℝ)) (σ := (992705201/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823254565/869890071 : ℝ) ^ p + (287468159/289963357 : ℝ) ^ p := by
    exact cert_lt (x := (823254565/869890071 : ℝ)) (y := (287468159/289963357 : ℝ)) (X := (21451087041291/100000000000000 : ℝ)) (Y := (39274457150679/50000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (94138557/100000000 : ℝ)) (n' := (869890071/1000000000 : ℝ)) (Ab := (164650913/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (188277687/200000000 : ℝ) ^ p + (198540903/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (188277687/200000000 : ℝ)) (y := (198540903/200000000 : ℝ)) (X := (1849981942237/10000000000000 : ℝ)) (Y := (815001991441/1000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198540903/200000000 : ℝ) ^ p + (188277687/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198540903/200000000 : ℝ)) (y := (188277687/200000000 : ℝ)) (X := (815001991441/1000000000000 : ℝ)) (Y := (1849981942237/10000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (38681859/20000000 : ℝ)) (τ := (188277687/200000000 : ℝ)) (σ := (198540903/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (823257575/869893356 : ℝ) ^ p + (143734627/144982226 : ℝ) ^ p := by
    exact cert_lt (x := (823257575/869893356 : ℝ)) (y := (143734627/144982226 : ℝ)) (X := (21451015055599/100000000000000 : ℝ)) (Y := (7854898623177/10000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (188277687/200000000 : ℝ)) (n' := (217473339/250000000 : ℝ)) (Ab := (32930303/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (941388519/1000000000 : ℝ) ^ p + (198540899/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (941388519/1000000000 : ℝ)) (y := (198540899/200000000 : ℝ)) (X := (18499865539893/100000000000000 : ℝ)) (Y := (81500153271211/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198540899/200000000 : ℝ) ^ p + (941388519/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198540899/200000000 : ℝ)) (y := (941388519/1000000000 : ℝ)) (X := (81500153271211/100000000000000 : ℝ)) (Y := (18499865539893/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (967046507/500000000 : ℝ)) (τ := (941388519/1000000000 : ℝ)) (σ := (198540899/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (274419221/289964484 : ℝ) ^ p + (143734643/144982242 : ℝ) ^ p := by
    exact cert_lt (x := (274419221/289964484 : ℝ)) (y := (143734643/144982242 : ℝ)) (X := (21451012978511/100000000000000 : ℝ)) (Y := (78548988333839/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (941388519/1000000000 : ℝ)) (n' := (217473363/250000000 : ℝ)) (Ab := (823257663/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (941388521/1000000000 : ℝ) ^ p + (496352247/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (941388521/1000000000 : ℝ)) (y := (496352247/500000000 : ℝ)) (X := (18499866637931/100000000000000 : ℝ)) (Y := (81500150977567/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496352247/500000000 : ℝ) ^ p + (941388521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496352247/500000000 : ℝ)) (y := (941388521/1000000000 : ℝ)) (X := (81500150977567/100000000000000 : ℝ)) (Y := (18499866637931/100000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (164651533/173978691 : ℝ) ^ p + (287469287/289964485 : ℝ) ^ p := by
    exact cert_lt (x := (164651533/173978691 : ℝ)) (y := (287469287/289964485 : ℝ)) (X := (10725506183821/50000000000000 : ℝ)) (Y := (9818623549941/12500000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (n' := (173978691/200000000 : ℝ)) (Ab := (164651533/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (386818603/200000000 : ℝ)) (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (567324818/614481185 : ℝ) ^ p + (611985987/614481185 : ℝ) ^ p := by
    exact cert_lt (x := (567324818/614481185 : ℝ)) (y := (611985987/614481185 : ℝ)) (X := (537262717981/5000000000000 : ℝ)) (Y := (5578421621007/6250000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1084531913/1156556445 : ℝ) ^ p + (383023617/385518815 : ℝ) ^ p := by
    exact cert_lt (x := (1084531913/1156556445 : ℝ)) (y := (383023617/385518815 : ℝ)) (X := (4147623904297/25000000000000 : ℝ)) (Y := (20852376291163/25000000000000 : ℝ)) 447 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496352247/500000000 : ℝ)) (U := (231311289/200000000 : ℝ)) (Ab := (850987227/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (941388521/1000000000 : ℝ)) (σ := (496352247/500000000 : ℝ)) (Ab := (1084531913/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab030
