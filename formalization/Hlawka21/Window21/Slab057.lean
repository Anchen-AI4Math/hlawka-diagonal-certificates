import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 57, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab057 (p : ℝ) (hpa : (729/32 : ℝ) ≤ p) (hpb : p ≤ (365/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (210758160251/9950850000000 : ℝ) (5458561/500000000 : ℝ) (4000000597051/19901700000000 : ℝ) (3033/2500 : ℝ) (970072437/500000000 : ℝ) (242508001/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193098127/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2773/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(4529/10000 : ℝ)
      else (96/125 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (210758160251/9950850000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5458561/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (229019203/250000000 : ℝ) ^ p + (993643477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229019203/250000000 : ℝ)) (y := (993643477/1000000000 : ℝ)) (X := (2707704351987/20000000000000 : ℝ)) (Y := (86461494862819/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993643477/1000000000 : ℝ) ^ p + (229019203/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993643477/1000000000 : ℝ)) (y := (229019203/250000000 : ℝ)) (X := (86461494862819/100000000000000 : ℝ)) (Y := (2707704351987/20000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1909720289/1000000000 : ℝ)) (τ := (229019203/250000000 : ℝ)) (σ := (993643477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778611917/825714970 : ℝ) ^ p + (407398924/412857485 : ℝ) ^ p := by
    exact cert_lt (x := (778611917/825714970 : ℝ)) (y := (407398924/412857485 : ℝ)) (X := (13093127321829/50000000000000 : ℝ)) (Y := (738137463281/1000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (229019203/250000000 : ℝ)) (n' := (82571497/100000000 : ℝ)) (Ab := (778611917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (184365859/200000000 : ℝ) ^ p + (992584317/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184365859/200000000 : ℝ)) (y := (992584317/1000000000 : ℝ)) (X := (15616714029061/100000000000000 : ℝ)) (Y := (84383302355121/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992584317/1000000000 : ℝ) ^ p + (184365859/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992584317/1000000000 : ℝ)) (y := (184365859/200000000 : ℝ)) (X := (84383302355121/100000000000000 : ℝ)) (Y := (15616714029061/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (478603403/250000000 : ℝ)) (τ := (184365859/200000000 : ℝ)) (σ := (992584317/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (392407794/416276701 : ℝ) ^ p + (410818140/416276701 : ℝ) ^ p := by
    exact cert_lt (x := (392407794/416276701 : ℝ)) (y := (410818140/416276701 : ℝ)) (X := (26000716411071/100000000000000 : ℝ)) (Y := (73999284899331/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (184365859/200000000 : ℝ)) (n' := (416276701/500000000 : ℝ)) (Ab := (196203897/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (922092659/1000000000 : ℝ) ^ p + (992531641/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922092659/1000000000 : ℝ)) (y := (992531641/1000000000 : ℝ)) (X := (3143762640619/20000000000000 : ℝ)) (Y := (4214060144887/5000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992531641/1000000000 : ℝ) ^ p + (922092659/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992531641/1000000000 : ℝ)) (y := (922092659/1000000000 : ℝ)) (X := (4214060144887/5000000000000 : ℝ)) (Y := (3143762640619/20000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (19146243/10000000 : ℝ)) (τ := (922092659/1000000000 : ℝ)) (σ := (992531641/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785098647/832865483 : ℝ) ^ p + (821948361/832865483 : ℝ) ^ p := by
    exact cert_lt (x := (785098647/832865483 : ℝ)) (y := (821948361/832865483 : ℝ)) (X := (203064929349/781250000000 : ℝ)) (Y := (74007690040423/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (922092659/1000000000 : ℝ)) (n' := (832865483/1000000000 : ℝ)) (Ab := (785098647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (461052293/500000000 : ℝ) ^ p + (496264623/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461052293/500000000 : ℝ)) (y := (496264623/500000000 : ℝ)) (X := (3930863013879/25000000000000 : ℝ)) (Y := (2106914089709/2500000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496264623/500000000 : ℝ) ^ p + (461052293/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496264623/500000000 : ℝ)) (y := (461052293/500000000 : ℝ)) (X := (2106914089709/2500000000000 : ℝ)) (Y := (3930863013879/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239329229/125000000 : ℝ)) (τ := (461052293/500000000 : ℝ)) (σ := (496264623/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (392555732/416439807 : ℝ) ^ p + (410981246/416439807 : ℝ) ^ p := by
    exact cert_lt (x := (392555732/416439807 : ℝ)) (y := (410981246/416439807 : ℝ)) (X := (25991930654761/100000000000000 : ℝ)) (Y := (18502017624249/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (461052293/500000000 : ℝ)) (n' := (416439807/500000000 : ℝ)) (Ab := (98138933/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (461052563/500000000 : ℝ) ^ p + (496264569/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (461052563/500000000 : ℝ)) (y := (496264569/500000000 : ℝ)) (X := (1965457764063/12500000000000 : ℝ)) (Y := (84276354389349/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496264569/500000000 : ℝ) ^ p + (461052563/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496264569/500000000 : ℝ)) (y := (461052563/500000000 : ℝ)) (X := (84276354389349/100000000000000 : ℝ)) (Y := (1965457764063/12500000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239329283/125000000 : ℝ)) (τ := (461052563/500000000 : ℝ)) (σ := (496264569/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (392556022/416440127 : ℝ) ^ p + (410981566/416440127 : ℝ) ^ p := by
    exact cert_lt (x := (392556022/416440127 : ℝ)) (y := (410981566/416440127 : ℝ)) (X := (25991913062361/100000000000000 : ℝ)) (Y := (37004043863901/50000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (461052563/500000000 : ℝ)) (n' := (416440127/500000000 : ℝ)) (Ab := (196278011/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (18442103/20000000 : ℝ) ^ p + (992529133/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18442103/20000000 : ℝ)) (y := (992529133/1000000000 : ℝ)) (X := (15723671448433/100000000000000 : ℝ)) (Y := (84276344704221/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992529133/1000000000 : ℝ) ^ p + (18442103/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (992529133/1000000000 : ℝ)) (y := (18442103/20000000 : ℝ)) (X := (84276344704221/100000000000000 : ℝ)) (Y := (15723671448433/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1914634283/1000000000 : ℝ)) (τ := (18442103/20000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392556035/416440141 : ℝ) ^ p + (410981580/416440141 : ℝ) ^ p := by
    exact cert_lt (x := (392556035/416440141 : ℝ)) (y := (410981580/416440141 : ℝ)) (X := (25991912764713/100000000000000 : ℝ)) (Y := (74008088481649/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (18442103/20000000 : ℝ)) (n' := (416440141/500000000 : ℝ)) (Ab := (78511207/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (922105151/1000000000 : ℝ) ^ p + (992529133/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922105151/1000000000 : ℝ)) (y := (992529133/1000000000 : ℝ)) (X := (1572367183743/10000000000000 : ℝ)) (Y := (84276344704221/100000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992529133/1000000000 : ℝ) ^ p + (922105151/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992529133/1000000000 : ℝ)) (y := (922105151/1000000000 : ℝ)) (X := (84276344704221/100000000000000 : ℝ)) (Y := (1572367183743/10000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785112071/832880283 : ℝ) ^ p + (821963161/832880283 : ℝ) ^ p := by
    exact cert_lt (x := (785112071/832880283 : ℝ)) (y := (821963161/832880283 : ℝ)) (X := (6497978202007/25000000000000 : ℝ)) (Y := (18502022127143/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (n' := (832880283/1000000000 : ℝ)) (Ab := (785112071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478658571/250000000 : ℝ)) (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1651825417/1806901873 : ℝ) ^ p + (1795984751/1806901873 : ℝ) ^ p := by
    exact cert_lt (x := (1651825417/1806901873 : ℝ)) (y := (1795984751/1806901873 : ℝ)) (X := (1291181248513/10000000000000 : ℝ)) (Y := (8708818773441/10000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109115651/1193098127 : ℝ) ^ p + (1182181005/1193098127 : ℝ) ^ p := by
    exact cert_lt (x := (1109115651/1193098127 : ℝ)) (y := (1182181005/1193098127 : ℝ)) (X := (1891729476129/10000000000000 : ℝ)) (Y := (20270676503989/25000000000000 : ℝ)) 365 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992529133/1000000000 : ℝ)) (U := (1193098127/1000000000 : ℝ)) (Ab := (1651825417/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (922105151/1000000000 : ℝ)) (σ := (992529133/1000000000 : ℝ)) (Ab := (1109115651/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab057
