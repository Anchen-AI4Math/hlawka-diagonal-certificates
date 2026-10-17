import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 21, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab021 (p : ℝ) (hpa : (693/32 : ℝ) ≤ p) (hpb : p ≤ (347/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (424328467567/18918900000000 : ℝ) (231583/20000000 : ℝ) (4000000567567/18918900000000 : ℝ) (3033/2500 : ℝ) (242136167/125000000 : ℝ) (968499999/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149081181/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(221/200 : ℝ) ≤ X j i ∧ X j i ≤ -(4453/10000 : ℝ)
      else (1521/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2367/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (424328467567/18918900000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (231583/20000000 : ℝ) := by norm_num
  have pc0 : 1 < (182295377/200000000 : ℝ) ^ p + (993390143/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (182295377/200000000 : ℝ)) (y := (993390143/1000000000 : ℝ)) (X := (13396272997651/100000000000000 : ℝ)) (Y := (86603744053137/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993390143/1000000000 : ℝ) ^ p + (182295377/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993390143/1000000000 : ℝ)) (y := (182295377/200000000 : ℝ)) (X := (86603744053137/100000000000000 : ℝ)) (Y := (13396272997651/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (476216757/250000000 : ℝ)) (τ := (182295377/200000000 : ℝ)) (σ := (993390143/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (772578089/821361898 : ℝ) ^ p + (404891374/410680949 : ℝ) ^ p := by
    exact cert_lt (x := (772578089/821361898 : ℝ)) (y := (404891374/410680949 : ℝ)) (X := (5300445882979/20000000000000 : ℝ)) (Y := (73497771441081/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (182295377/200000000 : ℝ)) (n' := (410680949/500000000 : ℝ)) (Ab := (772578089/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (183475939/200000000 : ℝ) ^ p + (248078361/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (183475939/200000000 : ℝ)) (y := (248078361/250000000 : ℝ)) (X := (3081868533161/20000000000000 : ℝ)) (Y := (84590673461609/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248078361/250000000 : ℝ) ^ p + (183475939/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248078361/250000000 : ℝ)) (y := (183475939/200000000 : ℝ)) (X := (84590673461609/100000000000000 : ℝ)) (Y := (3081868533161/20000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1909693139/1000000000 : ℝ)) (τ := (183475939/200000000 : ℝ)) (σ := (248078361/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (155791559/165685182 : ℝ) ^ p + (81684676/82842591 : ℝ) ^ p := by
    exact cert_lt (x := (155791559/165685182 : ℝ)) (y := (81684676/82842591 : ℝ)) (X := (5261526440411/20000000000000 : ℝ)) (Y := (73692369006541/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (183475939/200000000 : ℝ)) (n' := (82842591/100000000 : ℝ)) (Ab := (155791559/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (917669959/1000000000 : ℝ) ^ p + (992256027/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917669959/1000000000 : ℝ)) (y := (992256027/1000000000 : ℝ)) (X := (3878857262671/25000000000000 : ℝ)) (Y := (84484586090149/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992256027/1000000000 : ℝ) ^ p + (917669959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992256027/1000000000 : ℝ)) (y := (917669959/1000000000 : ℝ)) (X := (84484586090149/100000000000000 : ℝ)) (Y := (3878857262671/25000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (954962993/500000000 : ℝ)) (τ := (917669959/1000000000 : ℝ)) (σ := (992256027/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (779270410/828772129 : ℝ) ^ p + (817192979/828772129 : ℝ) ^ p := by
    exact cert_lt (x := (779270410/828772129 : ℝ)) (y := (817192979/828772129 : ℝ)) (X := (26298167151637/100000000000000 : ℝ)) (Y := (7370183378519/10000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (917669959/1000000000 : ℝ)) (n' := (828772129/1000000000 : ℝ)) (Ab := (77927041/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (114710509/125000000 : ℝ) ^ p + (124031653/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (114710509/125000000 : ℝ)) (y := (124031653/125000000 : ℝ)) (X := (77603024117/500000000000 : ℝ)) (Y := (16895882067209/20000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124031653/125000000 : ℝ) ^ p + (114710509/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (124031653/125000000 : ℝ)) (y := (114710509/125000000 : ℝ)) (X := (16895882067209/20000000000000 : ℝ)) (Y := (77603024117/500000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (119371081/62500000 : ℝ)) (τ := (114710509/125000000 : ℝ)) (σ := (124031653/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (779285607/828788960 : ℝ) ^ p + (81720981/82878896 : ℝ) ^ p := by
    exact cert_lt (x := (779285607/828788960 : ℝ)) (y := (81720981/82878896 : ℝ)) (X := (3287213377937/12500000000000 : ℝ)) (Y := (18425573432863/25000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (114710509/125000000 : ℝ)) (n' := (5179931/6250000 : ℝ)) (Ab := (779285607/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (917684757/1000000000 : ℝ) ^ p + (31007909/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (917684757/1000000000 : ℝ)) (y := (31007909/31250000 : ℝ)) (X := (7760428040401/50000000000000 : ℝ)) (Y := (84479159219031/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (31007909/31250000 : ℝ) ^ p + (917684757/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31007909/31250000 : ℝ)) (y := (917684757/1000000000 : ℝ)) (X := (84479159219031/100000000000000 : ℝ)) (Y := (7760428040401/50000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (381987569/200000000 : ℝ)) (τ := (917684757/1000000000 : ℝ)) (σ := (31007909/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (259762115/276263259 : ℝ) ^ p + (817210627/828789777 : ℝ) ^ p := by
    exact cert_lt (x := (259762115/276263259 : ℝ)) (y := (817210627/828789777 : ℝ)) (X := (26297684920633/100000000000000 : ℝ)) (Y := (36851158028737/50000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (917684757/1000000000 : ℝ)) (n' := (828789777/1000000000 : ℝ)) (Ab := (155857269/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (917684791/1000000000 : ℝ) ^ p + (992253081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917684791/1000000000 : ℝ)) (y := (992253081/1000000000 : ℝ)) (X := (15520868552073/100000000000000 : ℝ)) (Y := (8447914629391/10000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992253081/1000000000 : ℝ) ^ p + (917684791/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992253081/1000000000 : ℝ)) (y := (917684791/1000000000 : ℝ)) (X := (8447914629391/10000000000000 : ℝ)) (Y := (15520868552073/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (119371117/62500000 : ℝ)) (τ := (917684791/1000000000 : ℝ)) (σ := (992253081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (779286381/828789817 : ℝ) ^ p + (817210667/828789817 : ℝ) ^ p := by
    exact cert_lt (x := (779286381/828789817 : ℝ)) (y := (817210667/828789817 : ℝ)) (X := (26297683741741/100000000000000 : ℝ)) (Y := (36851158575273/50000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (917684791/1000000000 : ℝ)) (n' := (828789817/1000000000 : ℝ)) (Ab := (779286381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (114710599/125000000 : ℝ) ^ p + (992253081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114710599/125000000 : ℝ)) (y := (992253081/1000000000 : ℝ)) (X := (3880217229719/25000000000000 : ℝ)) (Y := (8447914629391/10000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992253081/1000000000 : ℝ) ^ p + (114710599/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992253081/1000000000 : ℝ)) (y := (114710599/125000000 : ℝ)) (X := (8447914629391/10000000000000 : ℝ)) (Y := (3880217229719/25000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1909937873/1000000000 : ℝ)) (τ := (114710599/125000000 : ℝ)) (σ := (992253081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (389643191/414394909 : ℝ) ^ p + (408605334/414394909 : ℝ) ^ p := by
    exact cert_lt (x := (389643191/414394909 : ℝ)) (y := (408605334/414394909 : ℝ)) (X := (5259536757091/20000000000000 : ℝ)) (Y := (73702317177873/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (114710599/125000000 : ℝ)) (n' := (414394909/500000000 : ℝ)) (Ab := (389643191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1909937873/1000000000 : ℝ)) (τ := (114710599/125000000 : ℝ)) (σ := (992253081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (114710599/125000000 : ℝ)) (n' := (414394909/500000000 : ℝ)) (Ab := (389643191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1909937873/1000000000 : ℝ)) (τ := (114710599/125000000 : ℝ)) (σ := (992253081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (114710599/125000000 : ℝ)) (n' := (414394909/500000000 : ℝ)) (Ab := (389643191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1909937873/1000000000 : ℝ)) (τ := (114710599/125000000 : ℝ)) (σ := (992253081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (114710599/125000000 : ℝ)) (n' := (414394909/500000000 : ℝ)) (Ab := (389643191/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1909937873/1000000000 : ℝ)) (τ := (114710599/125000000 : ℝ)) (σ := (992253081/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (822572533/903675276 : ℝ) ^ p + (897885701/903675276 : ℝ) ^ p := by
    exact cert_lt (x := (822572533/903675276 : ℝ)) (y := (897885701/903675276 : ℝ)) (X := (6505663735039/50000000000000 : ℝ)) (Y := (86988672816021/100000000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1104918647/1192649448 : ℝ) ^ p + (590535149/596324724 : ℝ) ^ p := by
    exact cert_lt (x := (1104918647/1192649448 : ℝ)) (y := (590535149/596324724 : ℝ)) (X := (19070160383523/100000000000000 : ℝ)) (Y := (10116230001851/12500000000000 : ℝ)) 347 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992253081/1000000000 : ℝ)) (U := (149081181/125000000 : ℝ)) (Ab := (822572533/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (114710599/125000000 : ℝ)) (σ := (992253081/1000000000 : ℝ)) (Ab := (1104918647/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab021
