import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 115, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab115 (p : ℝ) (hpa : (787/32 : ℝ) ≤ p) (hpb : p ≤ (197/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2087608507823/107425500000000 : ℝ) (9994287/1000000000 : ℝ) (4000000644553/21485100000000 : ℝ) (3033/2500 : ℝ) (972244359/500000000 : ℝ) (194441917/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596917423/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11153/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2317/5000 : ℝ)
      else (7783/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2371/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2087608507823/107425500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9994287/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (115320359/125000000 : ℝ) ^ p + (497007603/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115320359/125000000 : ℝ)) (y := (497007603/500000000 : ℝ)) (X := (6870618461693/50000000000000 : ℝ)) (Y := (5391173816073/6250000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497007603/500000000 : ℝ) ^ p + (115320359/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (497007603/500000000 : ℝ)) (y := (115320359/125000000 : ℝ)) (X := (5391173816073/6250000000000 : ℝ)) (Y := (6870618461693/50000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958289039/500000000 : ℝ)) (τ := (115320359/125000000 : ℝ)) (σ := (497007603/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (787153032/831743207 : ℝ) ^ p + (821748920/831743207 : ℝ) ^ p := by
    exact cert_lt (x := (787153032/831743207 : ℝ)) (y := (821748920/831743207 : ℝ)) (X := (12873348873507/50000000000000 : ℝ)) (Y := (4640831466199/6250000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115320359/125000000 : ℝ)) (n' := (831743207/1000000000 : ℝ)) (Ab := (98394129/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (1160083/1250000 : ℝ) ^ p + (992988489/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (1160083/1250000 : ℝ)) (y := (992988489/1000000000 : ℝ)) (X := (15908678200207/100000000000000 : ℝ)) (Y := (84091339656449/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992988489/1000000000 : ℝ) ^ p + (1160083/1250000 : ℝ) ^ p := by
    exact cert_lt (x := (992988489/1000000000 : ℝ)) (y := (1160083/1250000 : ℝ)) (X := (84091339656449/100000000000000 : ℝ)) (Y := (15908678200207/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1921054889/1000000000 : ℝ)) (τ := (1160083/1250000 : ℝ)) (σ := (992988489/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (793070899/838224633 : ℝ) ^ p + (276076782/279408211 : ℝ) ^ p := by
    exact cert_lt (x := (793070899/838224633 : ℝ)) (y := (276076782/279408211 : ℝ)) (X := (12787275617817/50000000000000 : ℝ)) (Y := (74425449627981/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (1160083/1250000 : ℝ)) (n' := (838224633/1000000000 : ℝ)) (Ab := (793070899/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (232073277/250000000 : ℝ) ^ p + (992942441/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232073277/250000000 : ℝ)) (y := (992942441/1000000000 : ℝ)) (X := (16004651806499/100000000000000 : ℝ)) (Y := (83995365083657/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992942441/1000000000 : ℝ) ^ p + (232073277/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992942441/1000000000 : ℝ)) (y := (232073277/250000000 : ℝ)) (X := (83995365083657/100000000000000 : ℝ)) (Y := (16004651806499/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1921235549/1000000000 : ℝ)) (τ := (232073277/250000000 : ℝ)) (σ := (992942441/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (396656948/419245407 : ℝ) ^ p + (276165509/279496938 : ℝ) ^ p := by
    exact cert_lt (x := (396656948/419245407 : ℝ)) (y := (276165509/279496938 : ℝ)) (X := (25567530398873/100000000000000 : ℝ)) (Y := (18608117648129/25000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (232073277/250000000 : ℝ)) (n' := (419245407/500000000 : ℝ)) (Ab := (99164237/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (58018897/62500000 : ℝ) ^ p + (992940557/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (58018897/62500000 : ℝ)) (y := (992940557/1000000000 : ℝ)) (X := (16008576885179/100000000000000 : ℝ)) (Y := (41995720317499/50000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992940557/1000000000 : ℝ) ^ p + (58018897/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992940557/1000000000 : ℝ)) (y := (58018897/62500000 : ℝ)) (X := (41995720317499/50000000000000 : ℝ)) (Y := (16008576885179/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1921242909/1000000000 : ℝ)) (τ := (58018897/62500000 : ℝ)) (σ := (992940557/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (793323803/838501666 : ℝ) ^ p + (828507379/838501666 : ℝ) ^ p := by
    exact cert_lt (x := (793323803/838501666 : ℝ)) (y := (828507379/838501666 : ℝ)) (X := (12783622226309/50000000000000 : ℝ)) (Y := (74432756750887/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (58018897/62500000 : ℝ)) (n' := (419250833/500000000 : ℝ)) (Ab := (793323803/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (928302729/1000000000 : ℝ) ^ p + (3102939/3125000 : ℝ) ^ p := by
    exact cert_lt (x := (928302729/1000000000 : ℝ)) (y := (3102939/3125000 : ℝ)) (X := (2001092122761/12500000000000 : ℝ)) (Y := (41995640122303/50000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (3102939/3125000 : ℝ) ^ p + (928302729/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (3102939/3125000 : ℝ)) (y := (928302729/1000000000 : ℝ)) (X := (41995640122303/50000000000000 : ℝ)) (Y := (2001092122761/12500000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1921243209/1000000000 : ℝ)) (τ := (928302729/1000000000 : ℝ)) (σ := (3102939/3125000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (793324207/838502109 : ℝ) ^ p + (276169274/279500703 : ℝ) ^ p := by
    exact cert_lt (x := (793324207/838502109 : ℝ)) (y := (276169274/279500703 : ℝ)) (X := (12783616222031/50000000000000 : ℝ)) (Y := (744327684323/1000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (928302729/1000000000 : ℝ)) (n' := (838502109/1000000000 : ℝ)) (Ab := (793324207/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (116037843/125000000 : ℝ) ^ p + (992940477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116037843/125000000 : ℝ)) (y := (992940477/1000000000 : ℝ)) (X := (2001092919003/12500000000000 : ℝ)) (Y := (20997818498909/25000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992940477/1000000000 : ℝ) ^ p + (116037843/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992940477/1000000000 : ℝ)) (y := (116037843/125000000 : ℝ)) (X := (20997818498909/25000000000000 : ℝ)) (Y := (2001092919003/12500000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921243221/1000000000 : ℝ)) (τ := (116037843/125000000 : ℝ)) (σ := (992940477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (88147136/93166903 : ℝ) ^ p + (276169280/279500709 : ℝ) ^ p := by
    exact cert_lt (x := (88147136/93166903 : ℝ)) (y := (276169280/279500709 : ℝ)) (X := (25567232420117/100000000000000 : ℝ)) (Y := (74432768906939/100000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (116037843/125000000 : ℝ)) (n' := (838502127/1000000000 : ℝ)) (Ab := (12395691/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (185660549/200000000 : ℝ) ^ p + (992940477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185660549/200000000 : ℝ)) (y := (992940477/1000000000 : ℝ)) (X := (8004371888343/50000000000000 : ℝ)) (Y := (20997818498909/25000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992940477/1000000000 : ℝ) ^ p + (185660549/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992940477/1000000000 : ℝ)) (y := (185660549/200000000 : ℝ)) (X := (20997818498909/25000000000000 : ℝ)) (Y := (8004371888343/50000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (960621611/500000000 : ℝ)) (τ := (185660549/200000000 : ℝ)) (σ := (992940477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (793324225/838502128 : ℝ) ^ p + (828507841/838502128 : ℝ) ^ p := by
    exact cert_lt (x := (793324225/838502128 : ℝ)) (y := (828507841/838502128 : ℝ)) (X := (6391808115719/25000000000000 : ℝ)) (Y := (18608192233327/25000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (185660549/200000000 : ℝ)) (n' := (52406383/62500000 : ℝ)) (Ab := (31732969/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (960621611/500000000 : ℝ)) (τ := (185660549/200000000 : ℝ)) (σ := (992940477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (185660549/200000000 : ℝ)) (n' := (52406383/62500000 : ℝ)) (Ab := (31732969/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (960621611/500000000 : ℝ)) (τ := (185660549/200000000 : ℝ)) (σ := (992940477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (185660549/200000000 : ℝ)) (n' := (52406383/62500000 : ℝ)) (Ab := (31732969/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (960621611/500000000 : ℝ)) (τ := (185660549/200000000 : ℝ)) (σ := (992940477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (185660549/200000000 : ℝ)) (n' := (52406383/62500000 : ℝ)) (Ab := (31732969/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (960621611/500000000 : ℝ)) (τ := (185660549/200000000 : ℝ)) (σ := (992940477/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (830678023/903082577 : ℝ) ^ p + (1796170867/1806165154 : ℝ) ^ p := by
    exact cert_lt (x := (830678023/903082577 : ℝ)) (y := (1796170867/1806165154 : ℝ)) (X := (12771501364709/100000000000000 : ℝ)) (Y := (21807124752259/25000000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (557627132/596917423 : ℝ) ^ p + (1183840559/1193834846 : ℝ) ^ p := by
    exact cert_lt (x := (557627132/596917423 : ℝ)) (y := (1183840559/1193834846 : ℝ)) (X := (9349748347691/50000000000000 : ℝ)) (Y := (2540640752589/3125000000000 : ℝ)) 197 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992940477/1000000000 : ℝ)) (U := (596917423/500000000 : ℝ)) (Ab := (830678023/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (185660549/200000000 : ℝ)) (σ := (992940477/1000000000 : ℝ)) (Ab := (139406783/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab115
