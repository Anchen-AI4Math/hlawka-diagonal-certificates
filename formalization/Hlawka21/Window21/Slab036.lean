import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 36, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab036 (p : ℝ) (hpa : (177/8 : ℝ) ≤ p) (hpb : p ≤ (709/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (264451500907/12080250000000 : ℝ) (5646977/500000000 : ℝ) (1000000144963/4832100000000 : ℝ) (3033/2500 : ℝ) (484599899/250000000 : ℝ) (242289243/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (2982087/2500000 : ℝ)) ∧
    (∀ j i, if j = i then -(2767/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2243/5000 : ℝ)
      else (7637/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5919/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (264451500907/12080250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5646977/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (913453197/1000000000 : ℝ) ^ p + (248374489/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (913453197/1000000000 : ℝ)) (y := (248374489/250000000 : ℝ)) (X := (6728617510131/50000000000000 : ℝ)) (Y := (86542782611657/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248374489/250000000 : ℝ) ^ p + (913453197/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248374489/250000000 : ℝ)) (y := (913453197/1000000000 : ℝ)) (X := (86542782611657/100000000000000 : ℝ)) (Y := (6728617510131/50000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1906951153/1000000000 : ℝ)) (τ := (913453197/1000000000 : ℝ)) (σ := (248374489/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (129194694/137206673 : ℝ) ^ p + (405973042/411620019 : ℝ) ^ p := by
    exact cert_lt (x := (129194694/137206673 : ℝ)) (y := (405973042/411620019 : ℝ)) (X := (5273207535921/20000000000000 : ℝ)) (Y := (14726792639071/20000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (913453197/1000000000 : ℝ)) (n' := (411620019/500000000 : ℝ)) (Ab := (193792041/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (229823541/250000000 : ℝ) ^ p + (992428231/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229823541/250000000 : ℝ)) (y := (992428231/1000000000 : ℝ)) (X := (15498470239681/100000000000000 : ℝ)) (Y := (4225077287759/5000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992428231/1000000000 : ℝ) ^ p + (229823541/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992428231/1000000000 : ℝ)) (y := (229823541/250000000 : ℝ)) (X := (4225077287759/5000000000000 : ℝ)) (Y := (15498470239681/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (382344479/200000000 : ℝ)) (τ := (229823541/250000000 : ℝ)) (σ := (992428231/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (781475039/830210069 : ℝ) ^ p + (818916115/830210069 : ℝ) ^ p := by
    exact cert_lt (x := (781475039/830210069 : ℝ)) (y := (818916115/830210069 : ℝ)) (X := (13087641356443/50000000000000 : ℝ)) (Y := (36912359232677/50000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (229823541/250000000 : ℝ)) (n' := (830210069/1000000000 : ℝ)) (Ab := (781475039/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (114946599/125000000 : ℝ) ^ p + (248093213/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (114946599/125000000 : ℝ)) (y := (248093213/250000000 : ℝ)) (X := (3900720435571/25000000000000 : ℝ)) (Y := (84397133716223/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248093213/250000000 : ℝ) ^ p + (114946599/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248093213/250000000 : ℝ)) (y := (114946599/125000000 : ℝ)) (X := (84397133716223/100000000000000 : ℝ)) (Y := (3900720435571/25000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (477986411/250000000 : ℝ)) (τ := (114946599/125000000 : ℝ)) (σ := (248093213/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (781774852/830541473 : ℝ) ^ p + (819247519/830541473 : ℝ) ^ p := by
    exact cert_lt (x := (781774852/830541473 : ℝ)) (y := (819247519/830541473 : ℝ)) (X := (5233256155441/20000000000000 : ℝ)) (Y := (14766744040623/20000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (114946599/125000000 : ℝ)) (n' := (830541473/1000000000 : ℝ)) (Ab := (195443713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (919585937/1000000000 : ℝ) ^ p + (992370229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919585937/1000000000 : ℝ)) (y := (992370229/1000000000 : ℝ)) (X := (15607824180199/100000000000000 : ℝ)) (Y := (84392191346537/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992370229/1000000000 : ℝ) ^ p + (919585937/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992370229/1000000000 : ℝ)) (y := (919585937/1000000000 : ℝ)) (X := (84392191346537/100000000000000 : ℝ)) (Y := (15607824180199/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (955978083/500000000 : ℝ)) (τ := (919585937/1000000000 : ℝ)) (σ := (992370229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (781788995/830557106 : ℝ) ^ p + (409631576/415278553 : ℝ) ^ p := by
    exact cert_lt (x := (781788995/830557106 : ℝ)) (y := (409631576/415278553 : ℝ)) (X := (26165856544981/100000000000000 : ℝ)) (Y := (36917072340911/50000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (919585937/1000000000 : ℝ)) (n' := (415278553/500000000 : ℝ)) (Ab := (156357799/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (229896639/250000000 : ℝ) ^ p + (496185053/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (229896639/250000000 : ℝ)) (y := (496185053/500000000 : ℝ)) (X := (7804028478593/50000000000000 : ℝ)) (Y := (42195979795709/50000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496185053/500000000 : ℝ) ^ p + (229896639/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496185053/500000000 : ℝ)) (y := (229896639/250000000 : ℝ)) (X := (42195979795709/50000000000000 : ℝ)) (Y := (7804028478593/50000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (955978331/500000000 : ℝ)) (τ := (229896639/250000000 : ℝ)) (σ := (496185053/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (781789661/830557842 : ℝ) ^ p + (409631944/415278921 : ℝ) ^ p := by
    exact cert_lt (x := (781789661/830557842 : ℝ)) (y := (409631944/415278921 : ℝ)) (X := (26165836683251/100000000000000 : ℝ)) (Y := (73834164665899/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (229896639/250000000 : ℝ)) (n' := (415278921/500000000 : ℝ)) (Ab := (781789661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (183917317/200000000 : ℝ) ^ p + (9923701/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (183917317/200000000 : ℝ)) (y := (9923701/10000000 : ℝ)) (X := (3902016965703/25000000000000 : ℝ)) (Y := (16878389657261/20000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (9923701/10000000 : ℝ) ^ p + (183917317/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (9923701/10000000 : ℝ)) (y := (183917317/200000000 : ℝ)) (X := (16878389657261/20000000000000 : ℝ)) (Y := (3902016965703/25000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (382391337/200000000 : ℝ)) (τ := (183917317/200000000 : ℝ)) (σ := (9923701/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (781789691/830557876 : ℝ) ^ p + (409631961/415278938 : ℝ) ^ p := by
    exact cert_lt (x := (781789691/830557876 : ℝ)) (y := (409631961/415278938 : ℝ)) (X := (26165835197473/100000000000000 : ℝ)) (Y := (18458541397269/25000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (183917317/200000000 : ℝ)) (n' := (207639469/250000000 : ℝ)) (Ab := (781789691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (459793293/500000000 : ℝ) ^ p + (9923701/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (459793293/500000000 : ℝ)) (y := (9923701/10000000 : ℝ)) (X := (15608068238869/100000000000000 : ℝ)) (Y := (16878389657261/20000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (9923701/10000000 : ℝ) ^ p + (459793293/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (9923701/10000000 : ℝ)) (y := (459793293/500000000 : ℝ)) (X := (16878389657261/20000000000000 : ℝ)) (Y := (15608068238869/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (955978343/500000000 : ℝ)) (τ := (459793293/500000000 : ℝ)) (σ := (9923701/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (781789693/830557878 : ℝ) ^ p + (409631962/415278939 : ℝ) ^ p := by
    exact cert_lt (x := (781789693/830557878 : ℝ)) (y := (409631962/415278939 : ℝ)) (X := (26165835284557/100000000000000 : ℝ)) (Y := (3691708282169/5000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (459793293/500000000 : ℝ)) (n' := (415278939/500000000 : ℝ)) (Ab := (781789693/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (955978343/500000000 : ℝ)) (τ := (459793293/500000000 : ℝ)) (σ := (9923701/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (459793293/500000000 : ℝ)) (n' := (415278939/500000000 : ℝ)) (Ab := (781789693/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (955978343/500000000 : ℝ)) (τ := (459793293/500000000 : ℝ)) (σ := (9923701/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (459793293/500000000 : ℝ)) (n' := (415278939/500000000 : ℝ)) (Ab := (781789693/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (955978343/500000000 : ℝ)) (τ := (459793293/500000000 : ℝ)) (σ := (9923701/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (459793293/500000000 : ℝ)) (n' := (415278939/500000000 : ℝ)) (Ab := (781789693/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (955978343/500000000 : ℝ)) (τ := (459793293/500000000 : ℝ)) (σ := (9923701/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (412001831/451791300 : ℝ) ^ p + (897935623/903582600 : ℝ) ^ p := by
    exact cert_lt (x := (412001831/451791300 : ℝ)) (y := (897935623/903582600 : ℝ)) (X := (12968572243993/100000000000000 : ℝ)) (Y := (87031427941783/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1106706259/1192834800 : ℝ) ^ p + (590770423/596417400 : ℝ) ^ p := by
    exact cert_lt (x := (1106706259/1192834800 : ℝ)) (y := (590770423/596417400 : ℝ)) (X := (9502323814153/50000000000000 : ℝ)) (Y := (80995352881629/100000000000000 : ℝ)) 709 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (9923701/10000000 : ℝ)) (U := (2982087/2500000 : ℝ)) (Ab := (412001831/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (459793293/500000000 : ℝ)) (σ := (9923701/10000000 : ℝ)) (Ab := (1106706259/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab036
