import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 107, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab107 (p : ℝ) (hpa : (779/32 : ℝ) ≤ p) (hpb : p ≤ (195/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1045093886119/53166750000000 : ℝ) (404493/40000000 : ℝ) (4000000638001/21266700000000 : ℝ) (3033/2500 : ℝ) (485981857/250000000 : ℝ) (121491029/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298433283/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2229/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(4621/10000 : ℝ)
      else (777/1000 : ℝ) ≤ X j i ∧ X j i ≤ (11853/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1045093886119/53166750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (404493/40000000 : ℝ) := by norm_num
  have pc0 : 1 < (9217283/10000000 : ℝ) ^ p + (198793281/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (9217283/10000000 : ℝ)) (y := (198793281/200000000 : ℝ)) (X := (13715012944131/100000000000000 : ℝ)) (Y := (43142502906927/50000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198793281/200000000 : ℝ) ^ p + (9217283/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (198793281/200000000 : ℝ)) (y := (9217283/10000000 : ℝ)) (X := (43142502906927/50000000000000 : ℝ)) (Y := (13715012944131/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (383138941/200000000 : ℝ)) (τ := (9217283/10000000 : ℝ)) (σ := (198793281/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (196512938/207743693 : ℝ) ^ p + (820862447/830974772 : ℝ) ^ p := by
    exact cert_lt (x := (196512938/207743693 : ℝ)) (y := (820862447/830974772 : ℝ)) (X := (25802866897263/100000000000000 : ℝ)) (Y := (37098566954829/50000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (9217283/10000000 : ℝ)) (n' := (207743693/250000000 : ℝ)) (Ab := (98256469/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (927266213/1000000000 : ℝ) ^ p + (992935011/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927266213/1000000000 : ℝ)) (y := (992935011/1000000000 : ℝ)) (X := (3174227962669/20000000000000 : ℝ)) (Y := (84128876816471/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992935011/1000000000 : ℝ) ^ p + (927266213/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992935011/1000000000 : ℝ)) (y := (927266213/1000000000 : ℝ)) (X := (84128876816471/100000000000000 : ℝ)) (Y := (3174227962669/20000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (240025153/125000000 : ℝ)) (τ := (927266213/1000000000 : ℝ)) (σ := (992935011/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (792008773/837504561 : ℝ) ^ p + (275797412/279168187 : ℝ) ^ p := by
    exact cert_lt (x := (792008773/837504561 : ℝ)) (y := (275797412/279168187 : ℝ)) (X := (160181016403/625000000000 : ℝ)) (Y := (18592759715989/25000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (927266213/1000000000 : ℝ)) (n' := (837504561/1000000000 : ℝ)) (Ab := (792008773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (927497539/1000000000 : ℝ) ^ p + (496444059/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (927497539/1000000000 : ℝ)) (y := (496444059/500000000 : ℝ)) (X := (7983965914431/50000000000000 : ℝ)) (Y := (16806417063611/20000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496444059/500000000 : ℝ) ^ p + (927497539/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496444059/500000000 : ℝ)) (y := (927497539/1000000000 : ℝ)) (X := (16806417063611/20000000000000 : ℝ)) (Y := (7983965914431/50000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1920385657/1000000000 : ℝ)) (τ := (927497539/1000000000 : ℝ)) (σ := (496444059/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (396128402/418888243 : ℝ) ^ p + (827664161/837776486 : ℝ) ^ p := by
    exact cert_lt (x := (396128402/418888243 : ℝ)) (y := (827664161/837776486 : ℝ)) (X := (100085041723/390625000000 : ℝ)) (Y := (18594557631027/25000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (927497539/1000000000 : ℝ)) (n' := (418888243/500000000 : ℝ)) (Ab := (198064201/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (927507103/1000000000 : ℝ) ^ p + (248221543/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (927507103/1000000000 : ℝ)) (y := (248221543/250000000 : ℝ)) (X := (15971945783281/100000000000000 : ℝ)) (Y := (42014035451191/50000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248221543/250000000 : ℝ) ^ p + (927507103/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248221543/250000000 : ℝ)) (y := (927507103/1000000000 : ℝ)) (X := (42014035451191/50000000000000 : ℝ)) (Y := (15971945783281/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (76815731/40000000 : ℝ)) (τ := (927507103/1000000000 : ℝ)) (σ := (248221543/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (792267057/837787727 : ℝ) ^ p + (827675402/837787727 : ℝ) ^ p := by
    exact cert_lt (x := (792267057/837787727 : ℝ)) (y := (827675402/837787727 : ℝ)) (X := (6405368329251/25000000000000 : ℝ)) (Y := (2324328991599/3125000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (927507103/1000000000 : ℝ)) (n' := (837787727/1000000000 : ℝ)) (Ab := (792267057/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (463753749/500000000 : ℝ) ^ p + (248221523/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (463753749/500000000 : ℝ)) (y := (248221523/250000000 : ℝ)) (X := (15972111583257/100000000000000 : ℝ)) (Y := (84027905873813/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248221523/250000000 : ℝ) ^ p + (463753749/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248221523/250000000 : ℝ)) (y := (463753749/500000000 : ℝ)) (X := (84027905873813/100000000000000 : ℝ)) (Y := (15972111583257/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (192039359/100000000 : ℝ)) (τ := (463753749/500000000 : ℝ)) (σ := (248221523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (792267481/837788192 : ℝ) ^ p + (827675867/837788192 : ℝ) ^ p := by
    exact cert_lt (x := (792267481/837788192 : ℝ)) (y := (827675867/837788192 : ℝ)) (X := (5124292182781/20000000000000 : ℝ)) (Y := (14875708005083/20000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (463753749/500000000 : ℝ)) (n' := (26180881/31250000 : ℝ)) (Ab := (792267481/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (463753757/500000000 : ℝ) ^ p + (992886089/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (463753757/500000000 : ℝ)) (y := (992886089/1000000000 : ℝ)) (X := (15972118299241/100000000000000 : ℝ)) (Y := (656467966291/781250000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992886089/1000000000 : ℝ) ^ p + (463753757/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992886089/1000000000 : ℝ)) (y := (463753757/500000000 : ℝ)) (X := (656467966291/781250000000 : ℝ)) (Y := (15972118299241/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1920393603/1000000000 : ℝ)) (τ := (463753757/500000000 : ℝ)) (σ := (992886089/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (792267499/837788211 : ℝ) ^ p + (275891962/279262737 : ℝ) ^ p := by
    exact cert_lt (x := (792267499/837788211 : ℝ)) (y := (275891962/279262737 : ℝ)) (X := (1601341308713/6250000000000 : ℝ)) (Y := (929731756597/1250000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (463753757/500000000 : ℝ)) (n' := (837788211/1000000000 : ℝ)) (Ab := (792267499/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (231876879/250000000 : ℝ) ^ p + (124110761/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (231876879/250000000 : ℝ)) (y := (124110761/125000000 : ℝ)) (X := (15972119138739/100000000000000 : ℝ)) (Y := (84027897622393/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124110761/125000000 : ℝ) ^ p + (231876879/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124110761/125000000 : ℝ)) (y := (231876879/250000000 : ℝ)) (X := (84027897622393/100000000000000 : ℝ)) (Y := (15972119138739/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (480098401/250000000 : ℝ)) (τ := (231876879/250000000 : ℝ)) (σ := (124110761/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (792267500/837788213 : ℝ) ^ p + (827675888/837788213 : ℝ) ^ p := by
    exact cert_lt (x := (792267500/837788213 : ℝ)) (y := (827675888/837788213 : ℝ)) (X := (6405365059199/25000000000000 : ℝ)) (Y := (74378540580639/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231876879/250000000 : ℝ)) (n' := (837788213/1000000000 : ℝ)) (Ab := (316907/400000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (480098401/250000000 : ℝ)) (τ := (231876879/250000000 : ℝ)) (σ := (124110761/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231876879/250000000 : ℝ)) (n' := (837788213/1000000000 : ℝ)) (Ab := (316907/400000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (480098401/250000000 : ℝ)) (τ := (231876879/250000000 : ℝ)) (σ := (124110761/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231876879/250000000 : ℝ)) (n' := (837788213/1000000000 : ℝ)) (Ab := (316907/400000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (480098401/250000000 : ℝ)) (τ := (231876879/250000000 : ℝ)) (σ := (124110761/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231876879/250000000 : ℝ)) (n' := (837788213/1000000000 : ℝ)) (Ab := (316907/400000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (480098401/250000000 : ℝ)) (τ := (231876879/250000000 : ℝ)) (σ := (124110761/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (79053443/86012708 : ℝ) ^ p + (598718181/602088956 : ℝ) ^ p := by
    exact cert_lt (x := (79053443/86012708 : ℝ)) (y := (598718181/602088956 : ℝ)) (X := (12789552626497/100000000000000 : ℝ)) (Y := (87210447674949/100000000000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (557224787/596866566 : ℝ) ^ p + (394540269/397911044 : ℝ) ^ p := by
    exact cert_lt (x := (557224787/596866566 : ℝ)) (y := (394540269/397911044 : ℝ)) (X := (4681916260283/25000000000000 : ℝ)) (Y := (1269880244149/1562500000000 : ℝ)) 195 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124110761/125000000 : ℝ)) (U := (298433283/250000000 : ℝ)) (Ab := (1660122303/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231876879/250000000 : ℝ)) (σ := (124110761/125000000 : ℝ)) (Ab := (557224787/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab107
