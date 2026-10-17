import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 17, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab017 (p : ℝ) (hpa : (433/16 : ℝ) ≤ p) (hpb : p ≤ (217/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1448075293171/95909500000000 : ℝ) (7745029/1000000000 : ℝ) (3200000575457/19181900000000 : ℝ) (591/500 : ℝ) (974769923/500000000 : ℝ) (974712397/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578021569/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5411/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(344/625 : ℝ)
      else (4079/5000 : ℝ) ≤ X j i ∧ X j i ≤ (459/400 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1448075293171/95909500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7745029/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (187193899/200000000 : ℝ) ^ p + (248331041/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (187193899/200000000 : ℝ)) (y := (248331041/250000000 : ℝ)) (X := (16613971581029/100000000000000 : ℝ)) (Y := (667088376411/800000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248331041/250000000 : ℝ) ^ p + (187193899/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248331041/250000000 : ℝ)) (y := (187193899/200000000 : ℝ)) (X := (667088376411/800000000000 : ℝ)) (Y := (16613971581029/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1929293659/1000000000 : ℝ)) (τ := (187193899/200000000 : ℝ)) (σ := (248331041/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (816931089/864320062 : ℝ) ^ p + (856575033/864320062 : ℝ) ^ p := by
    exact cert_lt (x := (816931089/864320062 : ℝ)) (y := (856575033/864320062 : ℝ)) (X := (676988497289/3125000000000 : ℝ)) (Y := (78336369114873/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187193899/200000000 : ℝ)) (n' := (432160031/500000000 : ℝ)) (Ab := (816931089/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (469700711/500000000 : ℝ) ^ p + (992554899/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469700711/500000000 : ℝ)) (y := (992554899/1000000000 : ℝ)) (X := (18348018082403/100000000000000 : ℝ)) (Y := (1633039987271/2000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992554899/1000000000 : ℝ) ^ p + (469700711/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992554899/1000000000 : ℝ)) (y := (469700711/500000000 : ℝ)) (X := (1633039987271/2000000000000 : ℝ)) (Y := (18348018082403/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1931956321/1000000000 : ℝ)) (τ := (469700711/500000000 : ℝ)) (σ := (992554899/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (205136499/217068568 : ℝ) ^ p + (860529243/868274272 : ℝ) ^ p := by
    exact cert_lt (x := (205136499/217068568 : ℝ)) (y := (860529243/868274272 : ℝ)) (X := (21576087624427/100000000000000 : ℝ)) (Y := (9802989160769/12500000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (469700711/500000000 : ℝ)) (n' := (27133571/31250000 : ℝ)) (Ab := (205136499/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469752901/500000000 : ℝ) ^ p + (992530073/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469752901/500000000 : ℝ)) (y := (992530073/1000000000 : ℝ)) (X := (3680679680391/20000000000000 : ℝ)) (Y := (40798310067787/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992530073/1000000000 : ℝ) ^ p + (469752901/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992530073/1000000000 : ℝ)) (y := (469752901/500000000 : ℝ)) (X := (40798310067787/50000000000000 : ℝ)) (Y := (3680679680391/20000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (15456287/8000000 : ℝ)) (τ := (469752901/500000000 : ℝ)) (σ := (992530073/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (410327863/434197156 : ℝ) ^ p + (860649283/868394312 : ℝ) ^ p := by
    exact cert_lt (x := (410327863/434197156 : ℝ)) (y := (860649283/868394312 : ℝ)) (X := (2696680116077/12500000000000 : ℝ)) (Y := (784265599071/1000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469752901/500000000 : ℝ)) (n' := (108549289/125000000 : ℝ)) (Ab := (410327863/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939508957/1000000000 : ℝ) ^ p + (992529321/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939508957/1000000000 : ℝ)) (y := (992529321/1000000000 : ℝ)) (X := (18405074836969/100000000000000 : ℝ)) (Y := (16318988643547/20000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992529321/1000000000 : ℝ) ^ p + (939508957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992529321/1000000000 : ℝ)) (y := (939508957/1000000000 : ℝ)) (X := (16318988643547/20000000000000 : ℝ)) (Y := (18405074836969/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966019139/500000000 : ℝ)) (τ := (939508957/1000000000 : ℝ)) (σ := (992529321/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820659043/868397940 : ℝ) ^ p + (860652911/868397940 : ℝ) ^ p := by
    exact cert_lt (x := (820659043/868397940 : ℝ)) (y := (860652911/868397940 : ℝ)) (X := (1078668069111/5000000000000 : ℝ)) (Y := (39213319943279/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939508957/1000000000 : ℝ)) (n' := (43419897/50000000 : ℝ)) (Ab := (820659043/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (939509053/1000000000 : ℝ) ^ p + (496264649/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (939509053/1000000000 : ℝ)) (y := (496264649/500000000 : ℝ)) (X := (9202562924829/50000000000000 : ℝ)) (Y := (20398722982387/25000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496264649/500000000 : ℝ) ^ p + (939509053/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496264649/500000000 : ℝ)) (y := (939509053/1000000000 : ℝ)) (X := (20398722982387/25000000000000 : ℝ)) (Y := (9202562924829/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1932038351/1000000000 : ℝ)) (τ := (939509053/1000000000 : ℝ)) (σ := (496264649/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (273553048/289466017 : ℝ) ^ p + (860653022/868398051 : ℝ) ^ p := by
    exact cert_lt (x := (273553048/289466017 : ℝ)) (y := (860653022/868398051 : ℝ)) (X := (4314671720553/20000000000000 : ℝ)) (Y := (1568532846671/2000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (939509053/1000000000 : ℝ)) (n' := (868398051/1000000000 : ℝ)) (Ab := (102582393/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (14679829/15625000 : ℝ) ^ p + (992529297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14679829/15625000 : ℝ)) (y := (992529297/1000000000 : ℝ)) (X := (18405127443807/100000000000000 : ℝ)) (Y := (20398722424907/25000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992529297/1000000000 : ℝ) ^ p + (14679829/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (992529297/1000000000 : ℝ)) (y := (14679829/15625000 : ℝ)) (X := (20398722424907/25000000000000 : ℝ)) (Y := (18405127443807/100000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (273553049/289466018 : ℝ) ^ p + (860653025/868398054 : ℝ) ^ p := by
    exact cert_lt (x := (273553049/289466018 : ℝ)) (y := (860653025/868398054 : ℝ)) (X := (21573358720363/100000000000000 : ℝ)) (Y := (15685328479937/20000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (n' := (434199027/500000000 : ℝ)) (Ab := (820659147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932038353/1000000000 : ℝ)) (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (849319272/921978431 : ℝ) ^ p + (1836211833/1843956862 : ℝ) ^ p := by
    exact cert_lt (x := (849319272/921978431 : ℝ)) (y := (1836211833/1843956862 : ℝ)) (X := (10789458617667/100000000000000 : ℝ)) (Y := (44605270810571/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082150759/1156043138 : ℝ) ^ p + (1148298109/1156043138 : ℝ) ^ p := by
    exact cert_lt (x := (1082150759/1156043138 : ℝ)) (y := (1148298109/1156043138 : ℝ)) (X := (16668053187909/100000000000000 : ℝ)) (Y := (41665973743077/50000000000000 : ℝ)) 217 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992529297/1000000000 : ℝ)) (U := (578021569/500000000 : ℝ)) (Ab := (106164909/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (14679829/15625000 : ℝ)) (σ := (992529297/1000000000 : ℝ)) (Ab := (1082150759/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab017
