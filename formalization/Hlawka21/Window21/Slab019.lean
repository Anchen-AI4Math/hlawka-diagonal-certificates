import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 19, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab019 (p : ℝ) (hpa : (691/32 : ℝ) ≤ p) (hpb : p ≤ (173/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2122466443481/94321500000000 : ℝ) (11618251/1000000000 : ℝ) (4000000565929/18864300000000 : ℝ) (3033/2500 : ℝ) (484227603/250000000 : ℝ) (968410283/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192624971/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11047/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4449/10000 : ℝ)
      else (7601/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5917/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2122466443481/94321500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11618251/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (911206557/1000000000 : ℝ) ^ p + (993375517/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (911206557/1000000000 : ℝ)) (y := (993375517/1000000000 : ℝ)) (X := (6693975031961/50000000000000 : ℝ)) (Y := (21653016623353/25000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993375517/1000000000 : ℝ) ^ p + (911206557/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993375517/1000000000 : ℝ)) (y := (911206557/1000000000 : ℝ)) (X := (21653016623353/25000000000000 : ℝ)) (Y := (6693975031961/50000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (952291037/500000000 : ℝ)) (τ := (911206557/1000000000 : ℝ)) (σ := (993375517/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (772224077/821104070 : ℝ) ^ p + (809485819/821104070 : ℝ) ^ p := by
    exact cert_lt (x := (772224077/821104070 : ℝ)) (y := (809485819/821104070 : ℝ)) (X := (13260457719977/50000000000000 : ℝ)) (Y := (14695817112659/20000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (911206557/1000000000 : ℝ)) (n' := (82110407/100000000 : ℝ)) (Ab := (772224077/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (458558751/500000000 : ℝ) ^ p + (99229793/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (458558751/500000000 : ℝ)) (y := (99229793/100000000 : ℝ)) (X := (3079429174849/20000000000000 : ℝ)) (Y := (84602870115009/100000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99229793/100000000 : ℝ) ^ p + (458558751/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99229793/100000000 : ℝ)) (y := (458558751/500000000 : ℝ)) (X := (84602870115009/100000000000000 : ℝ)) (Y := (3079429174849/20000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (238676929/125000000 : ℝ)) (τ := (458558751/500000000 : ℝ)) (σ := (99229793/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (778613413/828180587 : ℝ) ^ p + (816562336/828180587 : ℝ) ^ p := by
    exact cert_lt (x := (778613413/828180587 : ℝ)) (y := (816562336/828180587 : ℝ)) (X := (5265159683947/20000000000000 : ℝ)) (Y := (18418550653819/25000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (458558751/500000000 : ℝ)) (n' := (828180587/1000000000 : ℝ)) (Ab := (778613413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (229352341/250000000 : ℝ) ^ p + (198448047/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (229352341/250000000 : ℝ)) (y := (198448047/200000000 : ℝ)) (X := (7751728023453/50000000000000 : ℝ)) (Y := (84496559428189/100000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198448047/200000000 : ℝ) ^ p + (229352341/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198448047/200000000 : ℝ)) (y := (229352341/250000000 : ℝ)) (X := (84496559428189/100000000000000 : ℝ)) (Y := (7751728023453/50000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1909649599/1000000000 : ℝ)) (τ := (229352341/250000000 : ℝ)) (σ := (198448047/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (129821298/138088141 : ℝ) ^ p + (816910595/828528846 : ℝ) ^ p := by
    exact cert_lt (x := (129821298/138088141 : ℝ)) (y := (816910595/828528846 : ℝ)) (X := (13158134667773/50000000000000 : ℝ)) (Y := (36841865776311/50000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (229352341/250000000 : ℝ)) (n' := (414264423/500000000 : ℝ)) (Ab := (194731947/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (917423613/1000000000 : ℝ) ^ p + (992237407/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917423613/1000000000 : ℝ)) (y := (992237407/1000000000 : ℝ)) (X := (3877166025049/25000000000000 : ℝ)) (Y := (84491351740291/100000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992237407/1000000000 : ℝ) ^ p + (917423613/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992237407/1000000000 : ℝ)) (y := (917423613/1000000000 : ℝ)) (X := (84491351740291/100000000000000 : ℝ)) (Y := (3877166025049/25000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (95483051/50000000 : ℝ)) (τ := (917423613/1000000000 : ℝ)) (σ := (992237407/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (389471567/414272923 : ℝ) ^ p + (816927595/828545846 : ℝ) ^ p := by
    exact cert_lt (x := (389471567/414272923 : ℝ)) (y := (816927595/828545846 : ℝ)) (X := (6578951121429/25000000000000 : ℝ)) (Y := (36842098262759/50000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (917423613/1000000000 : ℝ)) (n' := (414272923/500000000 : ℝ)) (Ab := (389471567/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (229356077/250000000 : ℝ) ^ p + (992237269/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229356077/250000000 : ℝ)) (y := (992237269/1000000000 : ℝ)) (X := (7754459083753/50000000000000 : ℝ)) (Y := (84491097624741/100000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992237269/1000000000 : ℝ) ^ p + (229356077/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992237269/1000000000 : ℝ)) (y := (229356077/250000000 : ℝ)) (X := (84491097624741/100000000000000 : ℝ)) (Y := (7754459083753/50000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1909661577/1000000000 : ℝ)) (τ := (229356077/250000000 : ℝ)) (σ := (992237269/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (778943882/828546675 : ℝ) ^ p + (816928424/828546675 : ℝ) ^ p := by
    exact cert_lt (x := (778943882/828546675 : ℝ)) (y := (816928424/828546675 : ℝ)) (X := (13157890783711/50000000000000 : ℝ)) (Y := (9210527399921/12500000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (229356077/250000000 : ℝ)) (n' := (33141867/40000000 : ℝ)) (Ab := (389471941/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (458712171/500000000 : ℝ) ^ p + (496118631/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (458712171/500000000 : ℝ)) (y := (496118631/500000000 : ℝ)) (X := (9693081623/62500000000 : ℝ)) (Y := (84491084734841/100000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496118631/500000000 : ℝ) ^ p + (458712171/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496118631/500000000 : ℝ)) (y := (458712171/500000000 : ℝ)) (X := (84491084734841/100000000000000 : ℝ)) (Y := (9693081623/62500000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477415401/250000000 : ℝ)) (τ := (458712171/500000000 : ℝ)) (σ := (496118631/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (778943919/828546716 : ℝ) ^ p + (816928465/828546716 : ℝ) ^ p := by
    exact cert_lt (x := (778943919/828546716 : ℝ)) (y := (816928465/828546716 : ℝ)) (X := (6578945109589/25000000000000 : ℝ)) (Y := (4605263770047/6250000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (458712171/500000000 : ℝ)) (n' := (207136679/250000000 : ℝ)) (Ab := (778943919/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (114678043/125000000 : ℝ) ^ p + (496118631/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (114678043/125000000 : ℝ)) (y := (496118631/500000000 : ℝ)) (X := (3101786265587/20000000000000 : ℝ)) (Y := (84491084734841/100000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496118631/500000000 : ℝ) ^ p + (114678043/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496118631/500000000 : ℝ)) (y := (114678043/125000000 : ℝ)) (X := (84491084734841/100000000000000 : ℝ)) (Y := (3101786265587/20000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (954830803/500000000 : ℝ)) (τ := (114678043/125000000 : ℝ)) (σ := (496118631/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (778943921/828546718 : ℝ) ^ p + (816928467/828546718 : ℝ) ^ p := by
    exact cert_lt (x := (778943921/828546718 : ℝ)) (y := (816928467/828546718 : ℝ)) (X := (26315780525831/100000000000000 : ℝ)) (Y := (36842110187727/50000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (114678043/125000000 : ℝ)) (n' := (414273359/500000000 : ℝ)) (Ab := (778943921/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (954830803/500000000 : ℝ)) (τ := (114678043/125000000 : ℝ)) (σ := (496118631/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (114678043/125000000 : ℝ)) (n' := (414273359/500000000 : ℝ)) (Ab := (778943921/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (954830803/500000000 : ℝ)) (τ := (114678043/125000000 : ℝ)) (σ := (496118631/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (114678043/125000000 : ℝ)) (n' := (414273359/500000000 : ℝ)) (Ab := (778943921/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (954830803/500000000 : ℝ)) (τ := (114678043/125000000 : ℝ)) (σ := (496118631/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (114678043/125000000 : ℝ)) (n' := (414273359/500000000 : ℝ)) (Ab := (778943921/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (954830803/500000000 : ℝ)) (τ := (114678043/125000000 : ℝ)) (σ := (496118631/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1644754489/1807375029 : ℝ) ^ p + (1795756778/1807375029 : ℝ) ^ p := by
    exact cert_lt (x := (1644754489/1807375029 : ℝ)) (y := (1795756778/1807375029 : ℝ)) (X := (6508589217191/50000000000000 : ℝ)) (Y := (21745705436337/25000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (368225322/397541657 : ℝ) ^ p + (1181006720/1192624971 : ℝ) ^ p := by
    exact cert_lt (x := (368225322/397541657 : ℝ)) (y := (1181006720/1192624971 : ℝ)) (X := (9539553140139/50000000000000 : ℝ)) (Y := (20230223598859/25000000000000 : ℝ)) 173 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496118631/500000000 : ℝ)) (U := (1192624971/1000000000 : ℝ)) (Ab := (1644754489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (114678043/125000000 : ℝ)) (σ := (496118631/500000000 : ℝ)) (Ab := (552337983/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab019
