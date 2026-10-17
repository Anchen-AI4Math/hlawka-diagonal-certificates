import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 14, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab014 (p : ℝ) (hpa : (343/16 : ℝ) ≤ p) (hpb : p ≤ (687/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (212454618833/9363900000000 : ℝ) (11717141/1000000000 : ℝ) (2000000280917/9363900000000 : ℝ) (3033/2500 : ℝ) (242057327/125000000 : ℝ) (968183739/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192564019/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11041/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4437/10000 : ℝ)
      else (759/1000 : ℝ) ≤ X j i ∧ X j i ≤ (11833/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (212454618833/9363900000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11717141/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (910523507/1000000000 : ℝ) ^ p + (198667737/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (910523507/1000000000 : ℝ)) (y := (198667737/200000000 : ℝ)) (X := (13366944477941/100000000000000 : ℝ)) (Y := (86633071963253/100000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198667737/200000000 : ℝ) ^ p + (910523507/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198667737/200000000 : ℝ)) (y := (910523507/1000000000 : ℝ)) (X := (86633071963253/100000000000000 : ℝ)) (Y := (13366944477941/100000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (118991387/62500000 : ℝ)) (τ := (910523507/1000000000 : ℝ)) (σ := (198667737/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (154265969/164090326 : ℝ) ^ p + (808734489/820451630 : ℝ) ^ p := by
    exact cert_lt (x := (154265969/164090326 : ℝ)) (y := (808734489/820451630 : ℝ)) (X := (26568173866741/100000000000000 : ℝ)) (Y := (36715913573159/50000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (910523507/1000000000 : ℝ)) (n' := (82045163/100000000 : ℝ)) (Ab := (154265969/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (18329093/20000000 : ℝ) ^ p + (39690357/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (18329093/20000000 : ℝ)) (y := (39690357/40000000 : ℝ)) (X := (7683163716969/50000000000000 : ℝ)) (Y := (2644802758237/3125000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (39690357/40000000 : ℝ) ^ p + (18329093/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (39690357/40000000 : ℝ)) (y := (18329093/20000000 : ℝ)) (X := (2644802758237/3125000000000 : ℝ)) (Y := (7683163716969/50000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (76348543/40000000 : ℝ)) (τ := (18329093/20000000 : ℝ)) (σ := (39690357/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (14956599/15914603 : ℝ) ^ p + (815842215/827559356 : ℝ) ^ p := by
    exact cert_lt (x := (14956599/15914603 : ℝ)) (y := (815842215/827559356 : ℝ)) (X := (824117218427/3125000000000 : ℝ)) (Y := (1472564995243/2000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (18329093/20000000 : ℝ)) (n' := (206889839/250000000 : ℝ)) (Ab := (194435787/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (916750561/1000000000 : ℝ) ^ p + (992200527/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (916750561/1000000000 : ℝ)) (y := (992200527/1000000000 : ℝ)) (X := (15473199142629/100000000000000 : ℝ)) (Y := (5282926055203/6250000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992200527/1000000000 : ℝ) ^ p + (916750561/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992200527/1000000000 : ℝ)) (y := (916750561/1000000000 : ℝ)) (X := (5282926055203/6250000000000 : ℝ)) (Y := (15473199142629/100000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (119309443/62500000 : ℝ)) (τ := (916750561/1000000000 : ℝ)) (σ := (992200527/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (778061986/827912791 : ℝ) ^ p + (816195650/827912791 : ℝ) ^ p := by
    exact cert_lt (x := (778061986/827912791 : ℝ)) (y := (816195650/827912791 : ℝ)) (X := (26362059309789/100000000000000 : ℝ)) (Y := (73637941885479/100000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (916750561/1000000000 : ℝ)) (n' := (827912791/1000000000 : ℝ)) (Ab := (389030993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (458382579/500000000 : ℝ) ^ p + (496098817/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (458382579/500000000 : ℝ)) (y := (496098817/500000000 : ℝ)) (X := (7739244659007/50000000000000 : ℝ)) (Y := (16904305177789/20000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496098817/500000000 : ℝ) ^ p + (458382579/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496098817/500000000 : ℝ)) (y := (458382579/500000000 : ℝ)) (X := (16904305177789/20000000000000 : ℝ)) (Y := (7739244659007/50000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (238620349/125000000 : ℝ)) (τ := (458382579/500000000 : ℝ)) (σ := (496098817/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (86453079/91992247 : ℝ) ^ p + (816213082/827930223 : ℝ) ^ p := by
    exact cert_lt (x := (86453079/91992247 : ℝ)) (y := (816213082/827930223 : ℝ)) (X := (6590395288019/25000000000000 : ℝ)) (Y := (14727683946879/20000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (458382579/500000000 : ℝ)) (n' := (827930223/1000000000 : ℝ)) (Ab := (778077711/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (458382939/500000000 : ℝ) ^ p + (992197491/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458382939/500000000 : ℝ)) (y := (992197491/1000000000 : ℝ)) (X := (7739375150807/50000000000000 : ℝ)) (Y := (84521264365097/100000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992197491/1000000000 : ℝ) ^ p + (458382939/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992197491/1000000000 : ℝ)) (y := (458382939/500000000 : ℝ)) (X := (84521264365097/100000000000000 : ℝ)) (Y := (7739375150807/50000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1908963369/1000000000 : ℝ)) (τ := (458382939/500000000 : ℝ)) (σ := (992197491/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (778078487/827931083 : ℝ) ^ p + (816213942/827931083 : ℝ) ^ p := by
    exact cert_lt (x := (778078487/827931083 : ℝ)) (y := (816213942/827931083 : ℝ)) (X := (13180778859417/50000000000000 : ℝ)) (Y := (14727688661683/20000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (458382939/500000000 : ℝ)) (n' := (827931083/1000000000 : ℝ)) (Ab := (778078487/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (458382957/500000000 : ℝ) ^ p + (248049371/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (458382957/500000000 : ℝ)) (y := (248049371/250000000 : ℝ)) (X := (1934845418863/12500000000000 : ℝ)) (Y := (338085006253/400000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248049371/250000000 : ℝ) ^ p + (458382957/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248049371/250000000 : ℝ)) (y := (458382957/500000000 : ℝ)) (X := (338085006253/400000000000 : ℝ)) (Y := (1934845418863/12500000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (954481699/500000000 : ℝ)) (τ := (458382957/500000000 : ℝ)) (σ := (248049371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (389039263/413965563 : ℝ) ^ p + (816213985/827931126 : ℝ) ^ p := by
    exact cert_lt (x := (389039263/413965563 : ℝ)) (y := (816213985/827931126 : ℝ)) (X := (26361556692647/100000000000000 : ℝ)) (Y := (14727688897423/20000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (458382957/500000000 : ℝ)) (n' := (413965563/500000000 : ℝ)) (Ab := (389039263/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (183353183/200000000 : ℝ) ^ p + (248049371/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (183353183/200000000 : ℝ)) (y := (248049371/250000000 : ℝ)) (X := (3095752742677/20000000000000 : ℝ)) (Y := (338085006253/400000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248049371/250000000 : ℝ) ^ p + (183353183/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248049371/250000000 : ℝ)) (y := (183353183/200000000 : ℝ)) (X := (338085006253/400000000000 : ℝ)) (Y := (3095752742677/20000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1908963399/1000000000 : ℝ)) (τ := (183353183/200000000 : ℝ)) (σ := (248049371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (778078527/827931127 : ℝ) ^ p + (816213986/827931127 : ℝ) ^ p := by
    exact cert_lt (x := (778078527/827931127 : ℝ)) (y := (816213986/827931127 : ℝ)) (X := (5272311347289/20000000000000 : ℝ)) (Y := (73638444514527/100000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (183353183/200000000 : ℝ)) (n' := (827931127/1000000000 : ℝ)) (Ab := (778078527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1908963399/1000000000 : ℝ)) (τ := (183353183/200000000 : ℝ)) (σ := (248049371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (183353183/200000000 : ℝ)) (n' := (827931127/1000000000 : ℝ)) (Ab := (778078527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1908963399/1000000000 : ℝ)) (τ := (183353183/200000000 : ℝ)) (σ := (248049371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (183353183/200000000 : ℝ)) (n' := (827931127/1000000000 : ℝ)) (Ab := (778078527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1908963399/1000000000 : ℝ)) (τ := (183353183/200000000 : ℝ)) (σ := (248049371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (183353183/200000000 : ℝ)) (n' := (827931127/1000000000 : ℝ)) (Ab := (778078527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1908963399/1000000000 : ℝ)) (τ := (183353183/200000000 : ℝ)) (σ := (248049371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1643768540/1807435981 : ℝ) ^ p + (1795718840/1807435981 : ℝ) ^ p := by
    exact cert_lt (x := (1643768540/1807435981 : ℝ)) (y := (1795718840/1807435981 : ℝ)) (X := (1628994553229/12500000000000 : ℝ)) (Y := (43484021919463/50000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1104064632/1192564019 : ℝ) ^ p + (1180846878/1192564019 : ℝ) ^ p := by
    exact cert_lt (x := (1104064632/1192564019 : ℝ)) (y := (1180846878/1192564019 : ℝ)) (X := (3820336153929/20000000000000 : ℝ)) (Y := (80898319921909/100000000000000 : ℝ)) 687 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248049371/250000000 : ℝ)) (U := (1192564019/1000000000 : ℝ)) (Ab := (82188427/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (183353183/200000000 : ℝ)) (σ := (248049371/250000000 : ℝ)) (Ab := (138008079/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab014
