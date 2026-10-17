import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 85, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab085 (p : ℝ) (hpa : (757/32 : ℝ) ≤ p) (hpb : p ≤ (379/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1048780303399/51665250000000 : ℝ) (5225781/500000000 : ℝ) (4000000619983/20666100000000 : ℝ) (3033/2500 : ℝ) (971161841/500000000 : ℝ) (9711243/10000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596726587/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5561/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2291/5000 : ℝ)
      else (1933/2500 : ℝ) ≤ X j i ∧ X j i ≤ (1481/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1048780303399/51665250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5225781/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (919337951/1000000000 : ℝ) ^ p + (993828227/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919337951/1000000000 : ℝ)) (y := (993828227/1000000000 : ℝ)) (X := (6820065287397/50000000000000 : ℝ)) (Y := (21589972037889/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993828227/1000000000 : ℝ) ^ p + (919337951/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993828227/1000000000 : ℝ)) (y := (919337951/1000000000 : ℝ)) (X := (21589972037889/25000000000000 : ℝ)) (Y := (6820065287397/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (956583089/500000000 : ℝ)) (τ := (919337951/1000000000 : ℝ)) (σ := (993828227/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (782901297/828762016 : ℝ) ^ p + (409155227/414381008 : ℝ) ^ p := by
    exact cert_lt (x := (782901297/828762016 : ℝ)) (y := (409155227/414381008 : ℝ)) (X := (12982193322839/50000000000000 : ℝ)) (Y := (74035614758843/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (919337951/1000000000 : ℝ)) (n' := (25898813/31250000 : ℝ)) (Ab := (782901297/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (924970543/1000000000 : ℝ) ^ p + (496392129/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924970543/1000000000 : ℝ)) (y := (496392129/500000000 : ℝ)) (X := (7881786897559/50000000000000 : ℝ)) (Y := (84236443393221/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496392129/500000000 : ℝ) ^ p + (924970543/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496392129/500000000 : ℝ)) (y := (924970543/1000000000 : ℝ)) (X := (84236443393221/100000000000000 : ℝ)) (Y := (7881786897559/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1917754801/1000000000 : ℝ)) (τ := (924970543/1000000000 : ℝ)) (σ := (496392129/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (788966614/835426423 : ℝ) ^ p + (824974861/835426423 : ℝ) ^ p := by
    exact cert_lt (x := (788966614/835426423 : ℝ)) (y := (824974861/835426423 : ℝ)) (X := (25785499388049/100000000000000 : ℝ)) (Y := (9276812697513/12500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (924970543/1000000000 : ℝ)) (n' := (835426423/1000000000 : ℝ)) (Ab := (394483307/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185043053/200000000 : ℝ) ^ p + (992734929/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185043053/200000000 : ℝ)) (y := (992734929/1000000000 : ℝ)) (X := (1239270487/7812500000 : ℝ)) (Y := (84137355199789/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992734929/1000000000 : ℝ) ^ p + (185043053/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992734929/1000000000 : ℝ)) (y := (185043053/200000000 : ℝ)) (X := (84137355199789/100000000000000 : ℝ)) (Y := (1239270487/7812500000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958975097/500000000 : ℝ)) (τ := (185043053/200000000 : ℝ)) (σ := (992734929/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (789229270/835715073 : ℝ) ^ p + (275087837/278571691 : ℝ) ^ p := by
    exact cert_lt (x := (789229270/835715073 : ℝ)) (y := (275087837/278571691 : ℝ)) (X := (6444451670863/25000000000000 : ℝ)) (Y := (37111097180587/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185043053/200000000 : ℝ)) (n' := (835715073/1000000000 : ℝ)) (Ab := (78922927/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462612893/500000000 : ℝ) ^ p + (310229/312500 : ℝ) ^ p := by
    exact cert_lt (x := (462612893/500000000 : ℝ)) (y := (310229/312500 : ℝ)) (X := (15866935555001/100000000000000 : ℝ)) (Y := (10516635143381/12500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (310229/312500 : ℝ) ^ p + (462612893/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (310229/312500 : ℝ)) (y := (462612893/500000000 : ℝ)) (X := (10516635143381/12500000000000 : ℝ)) (Y := (15866935555001/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (958979293/500000000 : ℝ)) (τ := (462612893/500000000 : ℝ)) (σ := (310229/312500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (19731014/20893187 : ℝ) ^ p + (412637959/417863740 : ℝ) ^ p := by
    exact cert_lt (x := (19731014/20893187 : ℝ)) (y := (412637959/417863740 : ℝ)) (X := (2577747642663/10000000000000 : ℝ)) (Y := (74222524916837/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (462612893/500000000 : ℝ)) (n' := (20893187/25000000 : ℝ)) (Ab := (9865507/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925226239/1000000000 : ℝ) ^ p + (248183177/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925226239/1000000000 : ℝ)) (y := (248183177/250000000 : ℝ)) (X := (7933559787531/50000000000000 : ℝ)) (Y := (21033224114513/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248183177/250000000 : ℝ) ^ p + (925226239/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248183177/250000000 : ℝ)) (y := (925226239/1000000000 : ℝ)) (X := (21033224114513/25000000000000 : ℝ)) (Y := (7933559787531/50000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1917958947/1000000000 : ℝ)) (τ := (925226239/1000000000 : ℝ)) (σ := (248183177/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (263080349/278576005 : ℝ) ^ p + (275092151/278576005 : ℝ) ^ p := by
    exact cert_lt (x := (263080349/278576005 : ℝ)) (y := (275092151/278576005 : ℝ)) (X := (2577746231439/10000000000000 : ℝ)) (Y := (74222539170479/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925226239/1000000000 : ℝ)) (n' := (167145603/200000000 : ℝ)) (Ab := (789241047/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925226257/1000000000 : ℝ) ^ p + (198546541/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (925226257/1000000000 : ℝ)) (y := (198546541/200000000 : ℝ)) (X := (396678172179/2500000000000 : ℝ)) (Y := (84132890435591/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198546541/200000000 : ℝ) ^ p + (925226257/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198546541/200000000 : ℝ)) (y := (925226257/1000000000 : ℝ)) (X := (84132890435591/100000000000000 : ℝ)) (Y := (396678172179/2500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (958979481/500000000 : ℝ)) (τ := (925226257/1000000000 : ℝ)) (σ := (198546541/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (394620533/417864018 : ℝ) ^ p + (12504189/12662546 : ℝ) ^ p := by
    exact cert_lt (x := (394620533/417864018 : ℝ)) (y := (12504189/12662546 : ℝ)) (X := (12888730835397/50000000000000 : ℝ)) (Y := (74222539729967/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925226257/1000000000 : ℝ)) (n' := (208932009/250000000 : ℝ)) (Ab := (394620533/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (925226259/1000000000 : ℝ) ^ p + (31022897/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (925226259/1000000000 : ℝ)) (y := (31022897/31250000 : ℝ)) (X := (3173425539923/20000000000000 : ℝ)) (Y := (10516611053513/12500000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (31022897/31250000 : ℝ) ^ p + (925226259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31022897/31250000 : ℝ)) (y := (925226259/1000000000 : ℝ)) (X := (10516611053513/12500000000000 : ℝ)) (Y := (3173425539923/20000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (394620534/417864019 : ℝ) ^ p + (412638238/417864019 : ℝ) ^ p := by
    exact cert_lt (x := (394620534/417864019 : ℝ)) (y := (412638238/417864019 : ℝ)) (X := (25777461756863/100000000000000 : ℝ)) (Y := (18555634945813/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (n' := (417864019/500000000 : ℝ)) (Ab := (197310267/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1917958963/1000000000 : ℝ)) (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (828300441/903273413 : ℝ) ^ p + (898047632/903273413 : ℝ) ^ p := by
    exact cert_lt (x := (828300441/903273413 : ℝ)) (y := (898047632/903273413 : ℝ)) (X := (12841263485307/100000000000000 : ℝ)) (Y := (21789684174973/25000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112169251/1193453174 : ℝ) ^ p + (591500806/596726587 : ℝ) ^ p := by
    exact cert_lt (x := (1112169251/1193453174 : ℝ)) (y := (591500806/596726587 : ℝ)) (X := (1880811522893/10000000000000 : ℝ)) (Y := (81191885510091/100000000000000 : ℝ)) 379 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (31022897/31250000 : ℝ)) (U := (596726587/500000000 : ℝ)) (Ab := (828300441/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925226259/1000000000 : ℝ)) (σ := (31022897/31250000 : ℝ)) (Ab := (1112169251/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab085
