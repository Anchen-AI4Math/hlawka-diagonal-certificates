import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 104, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab104 (p : ℝ) (hpa : (97/4 : ℝ) ≤ p) (hpb : p ≤ (777/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (261396119851/13240500000000 : ℝ) (5078651/500000000 : ℝ) (500000079443/2648100000000 : ℝ) (3033/2500 : ℝ) (971857003/500000000 : ℝ) (971821251/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193694969/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5571/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(577/1250 : ℝ)
      else (1553/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2963/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (261396119851/13240500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5078651/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (921410689/1000000000 : ℝ) ^ p + (99394791/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (921410689/1000000000 : ℝ)) (y := (99394791/100000000 : ℝ)) (X := (3426260579941/25000000000000 : ℝ)) (Y := (1348359010977/1562500000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99394791/100000000 : ℝ) ^ p + (921410689/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99394791/100000000 : ℝ)) (y := (921410689/1000000000 : ℝ)) (X := (1348359010977/1562500000000 : ℝ)) (Y := (3426260579941/25000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1915358599/1000000000 : ℝ)) (τ := (921410689/1000000000 : ℝ)) (σ := (99394791/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (392816413/415340883 : ℝ) ^ p + (410262232/415340883 : ℝ) ^ p := by
    exact cert_lt (x := (392816413/415340883 : ℝ)) (y := (410262232/415340883 : ℝ)) (X := (25824276576461/100000000000000 : ℝ)) (Y := (37087862412561/50000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (921410689/1000000000 : ℝ)) (n' := (415340883/500000000 : ℝ)) (Ab := (392816413/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (926961509/1000000000 : ℝ) ^ p + (39716591/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (926961509/1000000000 : ℝ)) (y := (39716591/40000000 : ℝ)) (X := (396421257417/2500000000000 : ℝ)) (Y := (42071583112187/50000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (39716591/40000000 : ℝ) ^ p + (926961509/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39716591/40000000 : ℝ)) (y := (926961509/1000000000 : ℝ)) (X := (42071583112187/50000000000000 : ℝ)) (Y := (396421257417/2500000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (479969071/250000000 : ℝ)) (τ := (926961509/1000000000 : ℝ)) (σ := (39716591/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (395802283/418614889 : ℝ) ^ p + (413536238/418614889 : ℝ) ^ p := by
    exact cert_lt (x := (395802283/418614889 : ℝ)) (y := (413536238/418614889 : ℝ)) (X := (2564970466181/10000000000000 : ℝ)) (Y := (18587574147341/25000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (926961509/1000000000 : ℝ)) (n' := (418614889/500000000 : ℝ)) (Ab := (395802283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (4635973/5000000 : ℝ) ^ p + (24821689/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (4635973/5000000 : ℝ)) (y := (24821689/25000000 : ℝ)) (X := (3190790250949/20000000000000 : ℝ)) (Y := (42023033301893/50000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24821689/25000000 : ℝ) ^ p + (4635973/5000000 : ℝ) ^ p := by
    exact cert_lt (x := (24821689/25000000 : ℝ)) (y := (4635973/5000000 : ℝ)) (X := (42023033301893/50000000000000 : ℝ)) (Y := (3190790250949/20000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (24000777/12500000 : ℝ)) (τ := (4635973/5000000 : ℝ)) (σ := (24821689/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (791854522/837503901 : ℝ) ^ p + (827346599/837503901 : ℝ) ^ p := by
    exact cert_lt (x := (791854522/837503901 : ℝ)) (y := (827346599/837503901 : ℝ)) (X := (1025697893033/4000000000000 : ℝ)) (Y := (9294694220349/12500000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (4635973/5000000 : ℝ)) (n' := (837503901/1000000000 : ℝ)) (Ab := (395927261/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (14487567/15625000 : ℝ) ^ p + (99286559/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (14487567/15625000 : ℝ)) (y := (99286559/100000000 : ℝ)) (X := (3989499848309/25000000000000 : ℝ)) (Y := (4202100877611/5000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99286559/100000000 : ℝ) ^ p + (14487567/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (99286559/100000000 : ℝ)) (y := (14487567/15625000 : ℝ)) (X := (4202100877611/5000000000000 : ℝ)) (Y := (3989499848309/25000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (960034939/500000000 : ℝ)) (τ := (14487567/15625000 : ℝ)) (σ := (99286559/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (791864910/837515293 : ℝ) ^ p + (827357991/837515293 : ℝ) ^ p := by
    exact cert_lt (x := (791864910/837515293 : ℝ)) (y := (827357991/837515293 : ℝ)) (X := (25642146131907/100000000000000 : ℝ)) (Y := (18589463817047/25000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (14487567/15625000 : ℝ)) (n' := (837515293/1000000000 : ℝ)) (Ab := (79186491/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (927204691/1000000000 : ℝ) ^ p + (248216377/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (927204691/1000000000 : ℝ)) (y := (248216377/250000000 : ℝ)) (X := (398954195211/2500000000000 : ℝ)) (Y := (5252615563567/6250000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248216377/250000000 : ℝ) ^ p + (927204691/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248216377/250000000 : ℝ)) (y := (927204691/1000000000 : ℝ)) (X := (5252615563567/6250000000000 : ℝ)) (Y := (398954195211/2500000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1920070199/1000000000 : ℝ)) (τ := (927204691/1000000000 : ℝ)) (σ := (248216377/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (791865342/837515767 : ℝ) ^ p + (827358465/837515767 : ℝ) ^ p := by
    exact cert_lt (x := (791865342/837515767 : ℝ)) (y := (827358465/837515767 : ℝ)) (X := (12821066711397/50000000000000 : ℝ)) (Y := (18589466953279/25000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (927204691/1000000000 : ℝ)) (n' := (837515767/1000000000 : ℝ)) (Ab := (395932671/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (927204707/1000000000 : ℝ) ^ p + (198573101/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (927204707/1000000000 : ℝ)) (y := (198573101/200000000 : ℝ)) (X := (3191634898987/20000000000000 : ℝ)) (Y := (42020921425579/50000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198573101/200000000 : ℝ) ^ p + (927204707/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198573101/200000000 : ℝ)) (y := (927204707/1000000000 : ℝ)) (X := (42020921425579/50000000000000 : ℝ)) (Y := (3191634898987/20000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (480017553/250000000 : ℝ)) (τ := (927204707/1000000000 : ℝ)) (σ := (198573101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (791865359/837515786 : ℝ) ^ p + (413679242/418757893 : ℝ) ^ p := by
    exact cert_lt (x := (791865359/837515786 : ℝ)) (y := (413679242/418757893 : ℝ)) (X := (25642132664537/100000000000000 : ℝ)) (Y := (74357868315971/100000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (927204707/1000000000 : ℝ)) (n' := (418757893/500000000 : ℝ)) (Ab := (791865359/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (231801177/250000000 : ℝ) ^ p + (198573101/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (231801177/250000000 : ℝ)) (y := (198573101/200000000 : ℝ)) (X := (15958174912841/100000000000000 : ℝ)) (Y := (42020921425579/50000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198573101/200000000 : ℝ) ^ p + (231801177/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198573101/200000000 : ℝ)) (y := (231801177/250000000 : ℝ)) (X := (42020921425579/50000000000000 : ℝ)) (Y := (15958174912841/100000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1920070213/1000000000 : ℝ)) (τ := (231801177/250000000 : ℝ)) (σ := (198573101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (263955120/279171929 : ℝ) ^ p + (827358485/837515787 : ℝ) ^ p := by
    exact cert_lt (x := (263955120/279171929 : ℝ)) (y := (827358485/837515787 : ℝ)) (X := (12821066353697/50000000000000 : ℝ)) (Y := (37178934171219/50000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231801177/250000000 : ℝ)) (n' := (837515787/1000000000 : ℝ)) (Ab := (9898317/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1920070213/1000000000 : ℝ)) (τ := (231801177/250000000 : ℝ)) (σ := (198573101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231801177/250000000 : ℝ)) (n' := (837515787/1000000000 : ℝ)) (Ab := (9898317/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1920070213/1000000000 : ℝ)) (τ := (231801177/250000000 : ℝ)) (σ := (198573101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231801177/250000000 : ℝ)) (n' := (837515787/1000000000 : ℝ)) (Ab := (9898317/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1920070213/1000000000 : ℝ)) (τ := (231801177/250000000 : ℝ)) (σ := (198573101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231801177/250000000 : ℝ)) (n' := (837515787/1000000000 : ℝ)) (Ab := (9898317/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1920070213/1000000000 : ℝ)) (τ := (231801177/250000000 : ℝ)) (σ := (198573101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1659653372/1806305031 : ℝ) ^ p + (1796147729/1806305031 : ℝ) ^ p := by
    exact cert_lt (x := (1659653372/1806305031 : ℝ)) (y := (1796147729/1806305031 : ℝ)) (X := (799776503773/6250000000000 : ℝ)) (Y := (43601788079159/50000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1114144514/1193694969 : ℝ) ^ p + (1183537667/1193694969 : ℝ) ^ p := by
    exact cert_lt (x := (1114144514/1193694969 : ℝ)) (y := (1183537667/1193694969 : ℝ)) (X := (18738376059311/100000000000000 : ℝ)) (Y := (81261624710499/100000000000000 : ℝ)) 777 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198573101/200000000 : ℝ)) (U := (1193694969/1000000000 : ℝ)) (Ab := (414913343/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231801177/250000000 : ℝ)) (σ := (198573101/200000000 : ℝ)) (Ab := (557072257/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab104
