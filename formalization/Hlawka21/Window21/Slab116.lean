import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 116, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab116 (p : ℝ) (hpa : (197/8 : ℝ) ≤ p) (hpb : p ≤ (789/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (130455605213/6722625000000 : ℝ) (4989861/500000000 : ℝ) (1000000161343/5378100000000 : ℝ) (3033/2500 : ℝ) (194455809/100000000 : ℝ) (486122179/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298461887/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5577/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1159/2500 : ℝ)
      else (1557/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2371/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (130455605213/6722625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4989861/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (230666487/250000000 : ℝ) ^ p + (497010627/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (230666487/250000000 : ℝ)) (y := (497010627/500000000 : ℝ)) (X := (2748895757839/20000000000000 : ℝ)) (Y := (10781942564933/12500000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497010627/500000000 : ℝ) ^ p + (230666487/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (497010627/500000000 : ℝ)) (y := (230666487/250000000 : ℝ)) (X := (10781942564933/12500000000000 : ℝ)) (Y := (2748895757839/20000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958343601/500000000 : ℝ)) (τ := (230666487/250000000 : ℝ)) (σ := (497010627/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (787289094/831837967 : ℝ) ^ p + (821858245/831837967 : ℝ) ^ p := by
    exact cert_lt (x := (787289094/831837967 : ℝ)) (y := (821858245/831837967 : ℝ)) (X := (1608735360071/6250000000000 : ℝ)) (Y := (290079043339/390625000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (230666487/250000000 : ℝ)) (n' := (831837967/1000000000 : ℝ)) (Ab := (393644547/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (928165183/1000000000 : ℝ) ^ p + (248248781/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (928165183/1000000000 : ℝ)) (y := (248248781/250000000 : ℝ)) (X := (15913314447869/100000000000000 : ℝ)) (Y := (84086703604749/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248248781/250000000 : ℝ) ^ p + (928165183/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248248781/250000000 : ℝ)) (y := (928165183/1000000000 : ℝ)) (X := (84086703604749/100000000000000 : ℝ)) (Y := (15913314447869/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1921160307/1000000000 : ℝ)) (τ := (928165183/1000000000 : ℝ)) (σ := (248248781/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (793202080/838313373 : ℝ) ^ p + (276111217/279437791 : ℝ) ^ p := by
    exact cert_lt (x := (793202080/838313373 : ℝ)) (y := (276111217/279437791 : ℝ)) (X := (12783919003559/50000000000000 : ℝ)) (Y := (37216081698037/50000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (928165183/1000000000 : ℝ)) (n' := (838313373/1000000000 : ℝ)) (Ab := (4957513/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (928391323/1000000000 : ℝ) ^ p + (49647459/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (928391323/1000000000 : ℝ)) (y := (49647459/50000000 : ℝ)) (X := (3201837292129/20000000000000 : ℝ)) (Y := (419954150743/500000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (49647459/50000000 : ℝ) ^ p + (928391323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49647459/50000000 : ℝ)) (y := (928391323/1000000000 : ℝ)) (X := (419954150743/500000000000 : ℝ)) (Y := (3201837292129/20000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1921340503/1000000000 : ℝ)) (τ := (928391323/1000000000 : ℝ)) (σ := (49647459/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (264481486/279526283 : ℝ) ^ p + (276199709/279526283 : ℝ) ^ p := by
    exact cert_lt (x := (264481486/279526283 : ℝ)) (y := (276199709/279526283 : ℝ)) (X := (1278041876491/5000000000000 : ℝ)) (Y := (37219581728013/50000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (928391323/1000000000 : ℝ)) (n' := (838578849/1000000000 : ℝ)) (Ab := (396722229/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (928400527/1000000000 : ℝ) ^ p + (124118413/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (928400527/1000000000 : ℝ)) (y := (124118413/125000000 : ℝ)) (X := (16013100207689/100000000000000 : ℝ)) (Y := (16797383528539/20000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124118413/125000000 : ℝ) ^ p + (928400527/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124118413/125000000 : ℝ)) (y := (928400527/1000000000 : ℝ)) (X := (16797383528539/20000000000000 : ℝ)) (Y := (16013100207689/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1921347831/1000000000 : ℝ)) (τ := (928400527/1000000000 : ℝ)) (σ := (124118413/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (793454322/838589653 : ℝ) ^ p + (828609931/838589653 : ℝ) ^ p := by
    exact cert_lt (x := (793454322/838589653 : ℝ)) (y := (828609931/838589653 : ℝ)) (X := (6390138194061/25000000000000 : ℝ)) (Y := (74439448254957/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (928400527/1000000000 : ℝ)) (n' := (838589653/1000000000 : ℝ)) (Ab := (396727161/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464200451/500000000 : ℝ) ^ p + (992947227/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464200451/500000000 : ℝ)) (y := (992947227/1000000000 : ℝ)) (X := (16013259685553/100000000000000 : ℝ)) (Y := (41993378529251/50000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992947227/1000000000 : ℝ) ^ p + (464200451/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992947227/1000000000 : ℝ)) (y := (464200451/500000000 : ℝ)) (X := (41993378529251/50000000000000 : ℝ)) (Y := (16013259685553/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1921348129/1000000000 : ℝ)) (τ := (464200451/500000000 : ℝ)) (σ := (992947227/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (88161636/93176677 : ℝ) ^ p + (92067819/93176677 : ℝ) ^ p := by
    exact cert_lt (x := (88161636/93176677 : ℝ)) (y := (92067819/93176677 : ℝ)) (X := (25560541403769/100000000000000 : ℝ)) (Y := (74439459853447/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464200451/500000000 : ℝ)) (n' := (838590093/1000000000 : ℝ)) (Ab := (198363681/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (928400917/1000000000 : ℝ) ^ p + (124118403/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (928400917/1000000000 : ℝ)) (y := (124118403/125000000 : ℝ)) (X := (16013266064699/100000000000000 : ℝ)) (Y := (83986750801981/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124118403/125000000 : ℝ) ^ p + (928400917/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124118403/125000000 : ℝ)) (y := (928400917/1000000000 : ℝ)) (X := (83986750801981/100000000000000 : ℝ)) (Y := (16013266064699/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921348141/1000000000 : ℝ)) (τ := (928400917/1000000000 : ℝ)) (σ := (124118403/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (793454739/838590110 : ℝ) ^ p + (414305194/419295055 : ℝ) ^ p := by
    exact cert_lt (x := (793454739/838590110 : ℝ)) (y := (414305194/419295055 : ℝ)) (X := (6390135135491/25000000000000 : ℝ)) (Y := (7443946030157/10000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (928400917/1000000000 : ℝ)) (n' := (83859011/100000000 : ℝ)) (Ab := (793454739/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (464200459/500000000 : ℝ) ^ p + (124118403/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (464200459/500000000 : ℝ)) (y := (124118403/125000000 : ℝ)) (X := (2001658311247/12500000000000 : ℝ)) (Y := (83986750801981/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124118403/125000000 : ℝ) ^ p + (464200459/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124118403/125000000 : ℝ)) (y := (464200459/500000000 : ℝ)) (X := (83986750801981/100000000000000 : ℝ)) (Y := (2001658311247/12500000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (960674071/500000000 : ℝ)) (τ := (464200459/500000000 : ℝ)) (σ := (124118403/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (793454741/838590112 : ℝ) ^ p + (414305195/419295056 : ℝ) ^ p := by
    exact cert_lt (x := (793454741/838590112 : ℝ)) (y := (414305195/419295056 : ℝ)) (X := (5112108125493/20000000000000 : ℝ)) (Y := (74439460354291/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (464200459/500000000 : ℝ)) (n' := (26205941/31250000 : ℝ)) (Ab := (793454741/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (960674071/500000000 : ℝ)) (τ := (464200459/500000000 : ℝ)) (σ := (124118403/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (464200459/500000000 : ℝ)) (n' := (26205941/31250000 : ℝ)) (Ab := (793454741/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (960674071/500000000 : ℝ)) (τ := (464200459/500000000 : ℝ)) (σ := (124118403/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (464200459/500000000 : ℝ)) (n' := (26205941/31250000 : ℝ)) (Ab := (793454741/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (960674071/500000000 : ℝ)) (τ := (464200459/500000000 : ℝ)) (σ := (124118403/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (464200459/500000000 : ℝ)) (n' := (26205941/31250000 : ℝ)) (Ab := (793454741/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (960674071/500000000 : ℝ)) (τ := (464200459/500000000 : ℝ)) (σ := (124118403/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (415377143/451538113 : ℝ) ^ p + (898086365/903076226 : ℝ) ^ p := by
    exact cert_lt (x := (415377143/451538113 : ℝ)) (y := (898086365/903076226 : ℝ)) (X := (6384635325641/50000000000000 : ℝ)) (Y := (87230729592539/100000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (557676975/596923774 : ℝ) ^ p + (591933913/596923774 : ℝ) ^ p := by
    exact cert_lt (x := (557676975/596923774 : ℝ)) (y := (591933913/596923774 : ℝ)) (X := (9348006531439/50000000000000 : ℝ)) (Y := (40651993803773/50000000000000 : ℝ)) 789 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124118403/125000000 : ℝ)) (U := (298461887/250000000 : ℝ)) (Ab := (415377143/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (464200459/500000000 : ℝ)) (σ := (124118403/125000000 : ℝ)) (Ab := (22307079/20000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab116
