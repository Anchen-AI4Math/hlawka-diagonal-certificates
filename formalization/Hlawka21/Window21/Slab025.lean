import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 25, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab025 (p : ℝ) (hpa : (697/32 : ℝ) ≤ p) (hpb : p ≤ (349/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2120009315717/95140500000000 : ℝ) (460069/40000000 : ℝ) (4000000570843/19028100000000 : ℝ) (3033/2500 : ℝ) (968722079/500000000 : ℝ) (968677913/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (5963493/5000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2211/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2231/5000 : ℝ)
      else (3807/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2367/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2120009315717/95140500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (460069/40000000 : ℝ) := by norm_num
  have pc0 : 1 < (912012637/1000000000 : ℝ) ^ p + (993419217/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (912012637/1000000000 : ℝ)) (y := (993419217/1000000000 : ℝ)) (X := (13412776011711/100000000000000 : ℝ)) (Y := (17317448000661/20000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993419217/1000000000 : ℝ) ^ p + (912012637/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993419217/1000000000 : ℝ)) (y := (912012637/1000000000 : ℝ)) (X := (17317448000661/20000000000000 : ℝ)) (Y := (13412776011711/100000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (952715927/500000000 : ℝ)) (τ := (912012637/1000000000 : ℝ)) (σ := (993419217/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (773279891/821872208 : ℝ) ^ p + (810370483/821872208 : ℝ) ^ p := by
    exact cert_lt (x := (773279891/821872208 : ℝ)) (y := (810370483/821872208 : ℝ)) (X := (26465246874937/100000000000000 : ℝ)) (Y := (14706950891853/20000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (912012637/1000000000 : ℝ)) (n' := (51367013/62500000 : ℝ)) (Ab := (773279891/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (183579819/200000000 : ℝ) ^ p + (39693773/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (183579819/200000000 : ℝ)) (y := (39693773/40000000 : ℝ)) (X := (771675424333/5000000000000 : ℝ)) (Y := (16913301325829/20000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (39693773/40000000 : ℝ) ^ p + (183579819/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (39693773/40000000 : ℝ)) (y := (183579819/200000000 : ℝ)) (X := (16913301325829/20000000000000 : ℝ)) (Y := (771675424333/5000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (95512171/50000000 : ℝ)) (τ := (183579819/200000000 : ℝ)) (σ := (39693773/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (779640275/828911188 : ℝ) ^ p + (817409463/828911188 : ℝ) ^ p := by
    exact cert_lt (x := (779640275/828911188 : ℝ)) (y := (817409463/828911188 : ℝ)) (X := (13135841512763/50000000000000 : ℝ)) (Y := (73728318188763/100000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (183579819/200000000 : ℝ)) (n' := (207227797/250000000 : ℝ)) (Ab := (31185611/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (459093097/500000000 : ℝ) ^ p + (992287461/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459093097/500000000 : ℝ)) (y := (992287461/1000000000 : ℝ)) (X := (7769573347911/50000000000000 : ℝ)) (Y := (4223043434757/5000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992287461/1000000000 : ℝ) ^ p + (459093097/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992287461/1000000000 : ℝ)) (y := (459093097/500000000 : ℝ)) (X := (4223043434757/5000000000000 : ℝ)) (Y := (7769573347911/50000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (382094731/200000000 : ℝ)) (τ := (459093097/500000000 : ℝ)) (σ := (992287461/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (51996627/55283558 : ℝ) ^ p + (163550329/165850674 : ℝ) ^ p := by
    exact cert_lt (x := (51996627/55283558 : ℝ)) (y := (163550329/165850674 : ℝ)) (X := (26262344507897/100000000000000 : ℝ)) (Y := (73737656304367/100000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (459093097/500000000 : ℝ)) (n' := (82925337/100000000 : ℝ)) (Ab := (155989881/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (918200039/1000000000 : ℝ) ^ p + (248071177/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (918200039/1000000000 : ℝ)) (y := (248071177/250000000 : ℝ)) (X := (3886064591901/25000000000000 : ℝ)) (Y := (21113939390607/25000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248071177/250000000 : ℝ) ^ p + (918200039/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248071177/250000000 : ℝ)) (y := (918200039/1000000000 : ℝ)) (X := (21113939390607/25000000000000 : ℝ)) (Y := (3886064591901/25000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1910484747/1000000000 : ℝ)) (τ := (918200039/1000000000 : ℝ)) (σ := (248071177/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (389982155/414634934 : ℝ) ^ p + (817768143/829269868 : ℝ) ^ p := by
    exact cert_lt (x := (389982155/414634934 : ℝ)) (y := (817768143/829269868 : ℝ)) (X := (26261894954969/100000000000000 : ℝ)) (Y := (73738106367051/100000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (918200039/1000000000 : ℝ)) (n' := (207317467/250000000 : ℝ)) (Ab := (77996431/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (918200707/1000000000 : ℝ) ^ p + (39691383/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (918200707/1000000000 : ℝ)) (y := (39691383/40000000 : ℝ)) (X := (1554450503849/10000000000000 : ℝ)) (Y := (21113877661577/25000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39691383/40000000 : ℝ) ^ p + (918200707/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39691383/40000000 : ℝ)) (y := (918200707/1000000000 : ℝ)) (X := (21113877661577/25000000000000 : ℝ)) (Y := (1554450503849/10000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (955242641/500000000 : ℝ)) (τ := (918200707/1000000000 : ℝ)) (σ := (39691383/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (779965029/829270664 : ℝ) ^ p + (817768939/829270664 : ℝ) ^ p := by
    exact cert_lt (x := (779965029/829270664 : ℝ)) (y := (817768939/829270664 : ℝ)) (X := (3282734145283/12500000000000 : ℝ)) (Y := (73738128081411/100000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (918200707/1000000000 : ℝ)) (n' := (103658833/125000000 : ℝ)) (Ab := (779965029/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (45910037/50000000 : ℝ) ^ p + (124035571/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (45910037/50000000 : ℝ)) (y := (124035571/125000000 : ℝ)) (X := (1943064653053/12500000000000 : ℝ)) (Y := (42227748825371/50000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124035571/125000000 : ℝ) ^ p + (45910037/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (124035571/125000000 : ℝ)) (y := (45910037/50000000 : ℝ)) (X := (42227748825371/50000000000000 : ℝ)) (Y := (1943064653053/12500000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477621327/250000000 : ℝ)) (τ := (45910037/50000000 : ℝ)) (σ := (124035571/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (259988355/276423568 : ℝ) ^ p + (35555173/36055248 : ℝ) ^ p := by
    exact cert_lt (x := (259988355/276423568 : ℝ)) (y := (35555173/36055248 : ℝ)) (X := (13130935985599/50000000000000 : ℝ)) (Y := (9217266146573/12500000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (45910037/50000000 : ℝ)) (n' := (51829419/62500000 : ℝ)) (Ab := (155993013/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (918200741/1000000000 : ℝ) ^ p + (124035571/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (918200741/1000000000 : ℝ)) (y := (124035571/125000000 : ℝ)) (X := (3108903518739/20000000000000 : ℝ)) (Y := (42227748825371/50000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124035571/125000000 : ℝ) ^ p + (918200741/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124035571/125000000 : ℝ)) (y := (918200741/1000000000 : ℝ)) (X := (42227748825371/50000000000000 : ℝ)) (Y := (3108903518739/20000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1910485309/1000000000 : ℝ)) (τ := (918200741/1000000000 : ℝ)) (σ := (124035571/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (779965066/829270705 : ℝ) ^ p + (163553796/165854141 : ℝ) ^ p := by
    exact cert_lt (x := (779965066/829270705 : ℝ)) (y := (163553796/165854141 : ℝ)) (X := (13130936007433/50000000000000 : ℝ)) (Y := (9217266149983/12500000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (918200741/1000000000 : ℝ)) (n' := (165854141/200000000 : ℝ)) (Ab := (389982533/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1910485309/1000000000 : ℝ)) (τ := (918200741/1000000000 : ℝ)) (σ := (124035571/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (918200741/1000000000 : ℝ)) (n' := (165854141/200000000 : ℝ)) (Ab := (389982533/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1910485309/1000000000 : ℝ)) (τ := (918200741/1000000000 : ℝ)) (σ := (124035571/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (918200741/1000000000 : ℝ)) (n' := (165854141/200000000 : ℝ)) (Ab := (389982533/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1910485309/1000000000 : ℝ)) (τ := (918200741/1000000000 : ℝ)) (σ := (124035571/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (918200741/1000000000 : ℝ)) (n' := (165854141/200000000 : ℝ)) (Ab := (389982533/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1910485309/1000000000 : ℝ)) (τ := (918200741/1000000000 : ℝ)) (σ := (124035571/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (205739978/225912675 : ℝ) ^ p + (71831987/72292056 : ℝ) ^ p := by
    exact cert_lt (x := (205739978/225912675 : ℝ)) (y := (71831987/72292056 : ℝ)) (X := (6499869168261/50000000000000 : ℝ)) (Y := (43500130956083/50000000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (552700477/596349300 : ℝ) ^ p + (47247875/47707944 : ℝ) ^ p := by
    exact cert_lt (x := (552700477/596349300 : ℝ)) (y := (47247875/47707944 : ℝ)) (X := (9526213400567/50000000000000 : ℝ)) (Y := (10118446698567/12500000000000 : ℝ)) 349 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124035571/125000000 : ℝ)) (U := (5963493/5000000 : ℝ)) (Ab := (102869989/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (918200741/1000000000 : ℝ)) (σ := (124035571/125000000 : ℝ)) (Ab := (552700477/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab025
