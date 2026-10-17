import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 13, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab013 (p : ℝ) (hpa : (685/32 : ℝ) ≤ p) (hpb : p ≤ (343/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (212496587669/9350250000000 : ℝ) (5868559/500000000 : ℝ) (800000112203/3740100000000 : ℝ) (3033/2500 : ℝ) (48409187/25000000 : ℝ) (24203451/25000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192551879/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(138/125 : ℝ) ≤ X j i ∧ X j i ≤ -(887/2000 : ℝ)
      else (7587/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11833/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (212496587669/9350250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5868559/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (910385637/1000000000 : ℝ) ^ p + (993331273/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (910385637/1000000000 : ℝ)) (y := (993331273/1000000000 : ℝ)) (X := (6681353639401/50000000000000 : ℝ)) (Y := (43318654282439/50000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993331273/1000000000 : ℝ) ^ p + (910385637/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993331273/1000000000 : ℝ)) (y := (910385637/1000000000 : ℝ)) (X := (43318654282439/50000000000000 : ℝ)) (Y := (6681353639401/50000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (190371691/100000000 : ℝ)) (τ := (910385637/1000000000 : ℝ)) (σ := (993331273/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (771149398/820319765 : ℝ) ^ p + (808582647/820319765 : ℝ) ^ p := by
    exact cert_lt (x := (771149398/820319765 : ℝ)) (y := (808582647/820319765 : ℝ)) (X := (6644430848107/25000000000000 : ℝ)) (Y := (1468445558329/2000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (910385637/1000000000 : ℝ)) (n' := (164063953/200000000 : ℝ)) (Ab := (385574699/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (229080199/250000000 : ℝ) ^ p + (992251087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229080199/250000000 : ℝ)) (y := (992251087/1000000000 : ℝ)) (X := (7680052842483/50000000000000 : ℝ)) (Y := (84639910009351/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992251087/1000000000 : ℝ) ^ p + (229080199/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992251087/1000000000 : ℝ)) (y := (229080199/250000000 : ℝ)) (X := (84639910009351/100000000000000 : ℝ)) (Y := (7680052842483/50000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1908571883/1000000000 : ℝ)) (τ := (229080199/250000000 : ℝ)) (σ := (992251087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (777567477/827433725 : ℝ) ^ p + (815696607/827433725 : ℝ) ^ p := by
    exact cert_lt (x := (777567477/827433725 : ℝ)) (y := (815696607/827433725 : ℝ)) (X := (26381038117691/100000000000000 : ℝ)) (Y := (36809481448661/50000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (229080199/250000000 : ℝ)) (n' := (33097349/40000000 : ℝ)) (Ab := (777567477/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (458308763/500000000 : ℝ) ^ p + (992192547/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458308763/500000000 : ℝ)) (y := (992192547/1000000000 : ℝ)) (X := (7733544989087/50000000000000 : ℝ)) (Y := (84532926051629/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992192547/1000000000 : ℝ) ^ p + (458308763/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992192547/1000000000 : ℝ)) (y := (458308763/500000000 : ℝ)) (X := (84532926051629/100000000000000 : ℝ)) (Y := (7733544989087/50000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1908810073/1000000000 : ℝ)) (τ := (458308763/500000000 : ℝ)) (σ := (992192547/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (777887217/827788208 : ℝ) ^ p + (408025545/413894104 : ℝ) ^ p := by
    exact cert_lt (x := (777887217/827788208 : ℝ)) (y := (408025545/413894104 : ℝ)) (X := (13185656318389/50000000000000 : ℝ)) (Y := (73628688133803/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (458308763/500000000 : ℝ)) (n' := (51736763/62500000 : ℝ)) (Ab := (777887217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (458316097/500000000 : ℝ) ^ p + (992189641/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458316097/500000000 : ℝ)) (y := (992189641/1000000000 : ℝ)) (X := (7736198412257/50000000000000 : ℝ)) (Y := (16905523718421/20000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992189641/1000000000 : ℝ) ^ p + (458316097/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992189641/1000000000 : ℝ)) (y := (458316097/500000000 : ℝ)) (X := (16905523718421/20000000000000 : ℝ)) (Y := (7736198412257/50000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (381764367/200000000 : ℝ)) (τ := (458316097/500000000 : ℝ)) (σ := (992189641/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (194475755/206951432 : ℝ) ^ p + (408034305/413902864 : ℝ) ^ p := by
    exact cert_lt (x := (194475755/206951432 : ℝ)) (y := (408034305/413902864 : ℝ)) (X := (26370832370951/100000000000000 : ℝ)) (Y := (73629168610519/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (458316097/500000000 : ℝ)) (n' := (25868929/31250000 : ℝ)) (Ab := (38895151/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (916632919/1000000000 : ℝ) ^ p + (992189497/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (916632919/1000000000 : ℝ)) (y := (992189497/1000000000 : ℝ)) (X := (15472659172747/100000000000000 : ℝ)) (Y := (21131838900421/25000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992189497/1000000000 : ℝ) ^ p + (916632919/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992189497/1000000000 : ℝ)) (y := (916632919/1000000000 : ℝ)) (X := (21131838900421/25000000000000 : ℝ)) (Y := (15472659172747/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (119301401/62500000 : ℝ)) (τ := (916632919/1000000000 : ℝ)) (σ := (992189497/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (777903801/827806594 : ℝ) ^ p + (408034738/413903297 : ℝ) ^ p := by
    exact cert_lt (x := (777903801/827806594 : ℝ)) (y := (408034738/413903297 : ℝ)) (X := (6592702134509/25000000000000 : ℝ)) (Y := (3681459617983/5000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (916632919/1000000000 : ℝ)) (n' := (413903297/500000000 : ℝ)) (Ab := (777903801/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (458316477/500000000 : ℝ) ^ p + (99218949/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (458316477/500000000 : ℝ)) (y := (99218949/100000000 : ℝ)) (X := (15472671837941/100000000000000 : ℝ)) (Y := (84527342817447/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99218949/100000000 : ℝ) ^ p + (458316477/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99218949/100000000 : ℝ)) (y := (458316477/500000000 : ℝ)) (X := (84527342817447/100000000000000 : ℝ)) (Y := (15472671837941/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477205611/250000000 : ℝ)) (τ := (458316477/500000000 : ℝ)) (σ := (99218949/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (777903839/827806636 : ℝ) ^ p + (408034759/413903318 : ℝ) ^ p := by
    exact cert_lt (x := (777903839/827806636 : ℝ)) (y := (408034759/413903318 : ℝ)) (X := (13185403735561/50000000000000 : ℝ)) (Y := (14725838702293/20000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (458316477/500000000 : ℝ)) (n' := (206951659/250000000 : ℝ)) (Ab := (777903839/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (229158239/250000000 : ℝ) ^ p + (99218949/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (229158239/250000000 : ℝ)) (y := (99218949/100000000 : ℝ)) (X := (15472672561667/100000000000000 : ℝ)) (Y := (84527342817447/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (99218949/100000000 : ℝ) ^ p + (229158239/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (99218949/100000000 : ℝ)) (y := (229158239/250000000 : ℝ)) (X := (84527342817447/100000000000000 : ℝ)) (Y := (15472672561667/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (954411223/500000000 : ℝ)) (τ := (229158239/250000000 : ℝ)) (σ := (99218949/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (777903841/827806638 : ℝ) ^ p + (408034760/413903319 : ℝ) ^ p := by
    exact cert_lt (x := (777903841/827806638 : ℝ)) (y := (408034760/413903319 : ℝ)) (X := (26370807558741/100000000000000 : ℝ)) (Y := (73629193566313/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (229158239/250000000 : ℝ)) (n' := (413903319/500000000 : ℝ)) (Ab := (777903841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (954411223/500000000 : ℝ)) (τ := (229158239/250000000 : ℝ)) (σ := (99218949/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (229158239/250000000 : ℝ)) (n' := (413903319/500000000 : ℝ)) (Ab := (777903841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (954411223/500000000 : ℝ)) (τ := (229158239/250000000 : ℝ)) (σ := (99218949/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (229158239/250000000 : ℝ)) (n' := (413903319/500000000 : ℝ)) (Ab := (777903841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (954411223/500000000 : ℝ)) (τ := (229158239/250000000 : ℝ)) (σ := (99218949/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (229158239/250000000 : ℝ)) (n' := (413903319/500000000 : ℝ)) (Ab := (777903841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (954411223/500000000 : ℝ)) (τ := (229158239/250000000 : ℝ)) (σ := (99218949/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1643569705/1807448121 : ℝ) ^ p + (1795711003/1807448121 : ℝ) ^ p := by
    exact cert_lt (x := (1643569705/1807448121 : ℝ)) (y := (1795711003/1807448121 : ℝ)) (X := (6517469841467/50000000000000 : ℝ)) (Y := (17393012129609/20000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1103941577/1192551879 : ℝ) ^ p + (1180814761/1192551879 : ℝ) ^ p := by
    exact cert_lt (x := (1103941577/1192551879 : ℝ)) (y := (1180814761/1192551879 : ℝ)) (X := (4776558545113/25000000000000 : ℝ)) (Y := (80893766544693/100000000000000 : ℝ)) 343 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99218949/100000000 : ℝ)) (U := (1192551879/1000000000 : ℝ)) (Ab := (328713941/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (229158239/250000000 : ℝ)) (σ := (99218949/100000000 : ℝ)) (Ab := (1103941577/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab013
