import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 37, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab037 (p : ℝ) (hpa : (709/32 : ℝ) ≤ p) (hpb : p ≤ (355/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2115218807813/96778500000000 : ℝ) (1127543/100000000 : ℝ) (4000000580671/19355700000000 : ℝ) (3033/2500 : ℝ) (121155313/62500000 : ℝ) (969199797/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238569449/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11069/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(561/1250 : ℝ)
      else (7639/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5919/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2115218807813/96778500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1127543/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (913581833/1000000000 : ℝ) ^ p + (496752513/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (913581833/1000000000 : ℝ)) (y := (496752513/500000000 : ℝ)) (X := (841325731143/6250000000000 : ℝ)) (Y := (43269402570763/50000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496752513/500000000 : ℝ) ^ p + (913581833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496752513/500000000 : ℝ)) (y := (913581833/1000000000 : ℝ)) (X := (43269402570763/50000000000000 : ℝ)) (Y := (841325731143/6250000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1907086859/1000000000 : ℝ)) (τ := (913581833/1000000000 : ℝ)) (σ := (496752513/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (775336867/823361875 : ℝ) ^ p + (162417289/164672375 : ℝ) ^ p := by
    exact cert_lt (x := (775336867/823361875 : ℝ)) (y := (162417289/164672375 : ℝ)) (X := (26357194592973/100000000000000 : ℝ)) (Y := (14728561368413/20000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (913581833/1000000000 : ℝ)) (n' := (1317379/1600000 : ℝ)) (Ab := (775336867/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (919418629/1000000000 : ℝ) ^ p + (198487157/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (919418629/1000000000 : ℝ)) (y := (198487157/200000000 : ℝ)) (X := (15504269998951/100000000000000 : ℝ)) (Y := (4224787306741/5000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198487157/200000000 : ℝ) ^ p + (919418629/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198487157/200000000 : ℝ)) (y := (919418629/1000000000 : ℝ)) (X := (4224787306741/5000000000000 : ℝ)) (Y := (15504269998951/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (955927207/500000000 : ℝ)) (τ := (919418629/1000000000 : ℝ)) (σ := (198487157/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (195409713/207581408 : ℝ) ^ p + (409525101/415162816 : ℝ) ^ p := by
    exact cert_lt (x := (195409713/207581408 : ℝ)) (y := (409525101/415162816 : ℝ)) (X := (3270836513599/12500000000000 : ℝ)) (Y := (73833309287513/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (919418629/1000000000 : ℝ)) (n' := (6486919/7812500 : ℝ)) (Ab := (195409713/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (114962063/125000000 : ℝ) ^ p + (992380539/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114962063/125000000 : ℝ)) (y := (992380539/1000000000 : ℝ)) (X := (624342825517/4000000000000 : ℝ)) (Y := (84391445837563/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992380539/1000000000 : ℝ) ^ p + (114962063/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992380539/1000000000 : ℝ)) (y := (114962063/125000000 : ℝ)) (X := (84391445837563/100000000000000 : ℝ)) (Y := (624342825517/4000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1912077043/1000000000 : ℝ)) (τ := (114962063/125000000 : ℝ)) (σ := (992380539/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (43440991/46147560 : ℝ) ^ p + (81938065/83065608 : ℝ) ^ p := by
    exact cert_lt (x := (43440991/46147560 : ℝ)) (y := (81938065/83065608 : ℝ)) (X := (26157720152421/100000000000000 : ℝ)) (Y := (18460570327597/25000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (114962063/125000000 : ℝ)) (n' := (10383201/12500000 : ℝ)) (Ab := (390968919/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (919709587/1000000000 : ℝ) ^ p + (992377927/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919709587/1000000000 : ℝ)) (y := (992377927/1000000000 : ℝ)) (X := (15613497833031/100000000000000 : ℝ)) (Y := (42193258811419/50000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992377927/1000000000 : ℝ) ^ p + (919709587/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992377927/1000000000 : ℝ)) (y := (919709587/1000000000 : ℝ)) (X := (42193258811419/50000000000000 : ℝ)) (Y := (15613497833031/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (956043757/500000000 : ℝ)) (τ := (919709587/1000000000 : ℝ)) (σ := (992377927/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (195487978/207667909 : ℝ) ^ p + (409698103/415335818 : ℝ) ^ p := by
    exact cert_lt (x := (195487978/207667909 : ℝ)) (y := (409698103/415335818 : ℝ)) (X := (26157297365321/100000000000000 : ℝ)) (Y := (36921351761219/50000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (919709587/1000000000 : ℝ)) (n' := (207667909/250000000 : ℝ)) (Ab := (97743989/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (919710203/1000000000 : ℝ) ^ p + (248094451/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (919710203/1000000000 : ℝ)) (y := (248094451/250000000 : ℝ)) (X := (3122745972341/20000000000000 : ℝ)) (Y := (84386285558247/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248094451/250000000 : ℝ) ^ p + (919710203/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248094451/250000000 : ℝ)) (y := (919710203/1000000000 : ℝ)) (X := (84386285558247/100000000000000 : ℝ)) (Y := (3122745972341/20000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1912088007/1000000000 : ℝ)) (τ := (919710203/1000000000 : ℝ)) (σ := (248094451/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (781952575/830672368 : ℝ) ^ p + (409698469/415336184 : ℝ) ^ p := by
    exact cert_lt (x := (781952575/830672368 : ℝ)) (y := (409698469/415336184 : ℝ)) (X := (26157278018061/100000000000000 : ℝ)) (Y := (73842723389631/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (919710203/1000000000 : ℝ)) (n' := (51917023/62500000 : ℝ)) (Ab := (31278103/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (919710231/1000000000 : ℝ) ^ p + (992377799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919710231/1000000000 : ℝ)) (y := (992377799/1000000000 : ℝ)) (X := (15613740408541/100000000000000 : ℝ)) (Y := (84386276124739/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992377799/1000000000 : ℝ) ^ p + (919710231/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992377799/1000000000 : ℝ)) (y := (919710231/1000000000 : ℝ)) (X := (84386276124739/100000000000000 : ℝ)) (Y := (15613740408541/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (191208803/100000000 : ℝ)) (τ := (919710231/1000000000 : ℝ)) (σ := (992377799/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (781952604/830672401 : ℝ) ^ p + (819396971/830672401 : ℝ) ^ p := by
    exact cert_lt (x := (781952604/830672401 : ℝ)) (y := (819396971/830672401 : ℝ)) (X := (26157276485779/100000000000000 : ℝ)) (Y := (36921362142641/50000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (919710231/1000000000 : ℝ)) (n' := (830672401/1000000000 : ℝ)) (Ab := (195488151/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (919710233/1000000000 : ℝ) ^ p + (496188899/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (919710233/1000000000 : ℝ)) (y := (496188899/500000000 : ℝ)) (X := (15613741161887/100000000000000 : ℝ)) (Y := (42193137119019/50000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496188899/500000000 : ℝ) ^ p + (919710233/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496188899/500000000 : ℝ)) (y := (919710233/1000000000 : ℝ)) (X := (42193137119019/50000000000000 : ℝ)) (Y := (15613741161887/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1912088031/1000000000 : ℝ)) (τ := (919710233/1000000000 : ℝ)) (σ := (496188899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (26963883/28643876 : ℝ) ^ p + (409698487/415336202 : ℝ) ^ p := by
    exact cert_lt (x := (26963883/28643876 : ℝ)) (y := (409698487/415336202 : ℝ)) (X := (26157276616371/100000000000000 : ℝ)) (Y := (14768544873341/20000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (919710233/1000000000 : ℝ)) (n' := (207668101/250000000 : ℝ)) (Ab := (781952607/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have pc21 : 1 < (459855117/500000000 : ℝ) ^ p + (496188899/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (459855117/500000000 : ℝ)) (y := (496188899/500000000 : ℝ)) (X := (12198235577/78125000000 : ℝ)) (Y := (42193137119019/50000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (496188899/500000000 : ℝ) ^ p + (459855117/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496188899/500000000 : ℝ)) (y := (459855117/500000000 : ℝ)) (X := (42193137119019/50000000000000 : ℝ)) (Y := (12198235577/78125000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (59752751/31250000 : ℝ)) (τ := (459855117/500000000 : ℝ)) (σ := (496188899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc21) (by norm_num; exact pc22)
  have pc23 : 1 < (781952608/830672405 : ℝ) ^ p + (163879395/166134481 : ℝ) ^ p := by
    exact cert_lt (x := (781952608/830672405 : ℝ)) (y := (163879395/166134481 : ℝ)) (X := (13078638329951/50000000000000 : ℝ)) (Y := (36921362196923/50000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (459855117/500000000 : ℝ)) (n' := (166134481/200000000 : ℝ)) (Ab := (24436019/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc23.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (59752751/31250000 : ℝ)) (τ := (459855117/500000000 : ℝ)) (σ := (496188899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc21) (by norm_num; exact pc22)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (459855117/500000000 : ℝ)) (n' := (166134481/200000000 : ℝ)) (Ab := (24436019/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc23.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (59752751/31250000 : ℝ)) (τ := (459855117/500000000 : ℝ)) (σ := (496188899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc21) (by norm_num; exact pc22)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (459855117/500000000 : ℝ)) (n' := (166134481/200000000 : ℝ)) (Ab := (24436019/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc23.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (59752751/31250000 : ℝ)) (τ := (459855117/500000000 : ℝ)) (σ := (496188899/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc21) (by norm_num; exact pc22)
  have pc24 : 1 < (1648194031/1807152755 : ℝ) ^ p + (359175465/361430551 : ℝ) ^ p := by
    exact cert_lt (x := (1648194031/1807152755 : ℝ)) (y := (359175465/361430551 : ℝ)) (X := (2593157673399/20000000000000 : ℝ)) (Y := (3481368476119/4000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc25 : 1 < (1106823411/1192847245 : ℝ) ^ p + (236314363/238569449 : ℝ) ^ p := by
    exact cert_lt (x := (1106823411/1192847245 : ℝ)) (y := (236314363/238569449 : ℝ)) (X := (19000373388827/100000000000000 : ℝ)) (Y := (80999626996257/100000000000000 : ℝ)) 355 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496188899/500000000 : ℝ)) (U := (238569449/200000000 : ℝ)) (Ab := (1648194031/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc24.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (459855117/500000000 : ℝ)) (σ := (496188899/500000000 : ℝ)) (Ab := (1106823411/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc25.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab037
