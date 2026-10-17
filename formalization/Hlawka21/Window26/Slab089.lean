import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 89, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab089 (p : ℝ) (hpa : (505/16 : ℝ) ≤ p) (hpb : p ≤ (253/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (35539674223/2796437500000 : ℝ) (129911/20000000 : ℝ) (640000134229/4474300000000 : ℝ) (591/500 : ℝ) (978320751/500000000 : ℝ) (97827829/100000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231738199/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10941/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5647/10000 : ℝ)
      else (1661/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11511/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (35539674223/2796437500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (129911/20000000 : ℝ) := by norm_num
  have pc0 : 1 < (472739559/500000000 : ℝ) ^ p + (994132247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (472739559/500000000 : ℝ)) (y := (994132247/1000000000 : ℝ)) (X := (679285959161/4000000000000 : ℝ)) (Y := (20754468324099/25000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994132247/1000000000 : ℝ) ^ p + (472739559/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (994132247/1000000000 : ℝ)) (y := (472739559/500000000 : ℝ)) (X := (20754468324099/25000000000000 : ℝ)) (Y := (679285959161/4000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (387922273/200000000 : ℝ)) (τ := (472739559/500000000 : ℝ)) (σ := (994132247/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (830032778/871943519 : ℝ) ^ p + (865447969/871943519 : ℝ) ^ p := by
    exact cert_lt (x := (830032778/871943519 : ℝ)) (y := (865447969/871943519 : ℝ)) (X := (21059248296869/100000000000000 : ℝ)) (Y := (39470376284883/50000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (472739559/500000000 : ℝ)) (n' := (871943519/1000000000 : ℝ)) (Ab := (415016389/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (948551217/1000000000 : ℝ) ^ p + (49671499/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (948551217/1000000000 : ℝ)) (y := (49671499/50000000 : ℝ)) (X := (4704217060081/25000000000000 : ℝ)) (Y := (40591576487651/50000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (49671499/50000000 : ℝ) ^ p + (948551217/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49671499/50000000 : ℝ)) (y := (948551217/1000000000 : ℝ)) (X := (40591576487651/50000000000000 : ℝ)) (Y := (4704217060081/25000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1941981197/1000000000 : ℝ)) (τ := (948551217/1000000000 : ℝ)) (σ := (49671499/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (416630327/437716380 : ℝ) ^ p + (86893721/87543276 : ℝ) ^ p := by
    exact cert_lt (x := (416630327/437716380 : ℝ)) (y := (86893721/87543276 : ℝ)) (X := (2098453267257/10000000000000 : ℝ)) (Y := (79015468616543/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (948551217/1000000000 : ℝ)) (n' := (21885819/25000000 : ℝ)) (Ab := (416630327/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (948627971/1000000000 : ℝ) ^ p + (993411319/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (948627971/1000000000 : ℝ)) (y := (993411319/1000000000 : ℝ)) (X := (18865080370041/100000000000000 : ℝ)) (Y := (20283734854229/25000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993411319/1000000000 : ℝ) ^ p + (948627971/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993411319/1000000000 : ℝ)) (y := (948627971/1000000000 : ℝ)) (X := (20283734854229/25000000000000 : ℝ)) (Y := (18865080370041/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (194203929/100000000 : ℝ)) (τ := (948627971/1000000000 : ℝ)) (σ := (993411319/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (833341161/875519792 : ℝ) ^ p + (434512121/437759896 : ℝ) ^ p := by
    exact cert_lt (x := (833341161/875519792 : ℝ)) (y := (434512121/437759896 : ℝ)) (X := (20982675322567/100000000000000 : ℝ)) (Y := (19754331378719/25000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (948627971/1000000000 : ℝ)) (n' := (54719987/62500000 : ℝ)) (Ab := (833341161/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (474314939/500000000 : ℝ) ^ p + (198682171/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (474314939/500000000 : ℝ)) (y := (198682171/200000000 : ℝ)) (X := (18866279751497/100000000000000 : ℝ)) (Y := (81133740955047/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198682171/200000000 : ℝ) ^ p + (474314939/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198682171/200000000 : ℝ)) (y := (474314939/500000000 : ℝ)) (X := (81133740955047/100000000000000 : ℝ)) (Y := (18866279751497/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1942040733/1000000000 : ℝ)) (τ := (474314939/500000000 : ℝ)) (σ := (198682171/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (833343162/875521955 : ℝ) ^ p + (173805281/175104391 : ℝ) ^ p := by
    exact cert_lt (x := (833343162/875521955 : ℝ)) (y := (173805281/175104391 : ℝ)) (X := (1049131465019/5000000000000 : ℝ)) (Y := (79017371660073/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (474314939/500000000 : ℝ)) (n' := (175104391/200000000 : ℝ)) (Ab := (416671581/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (474314963/500000000 : ℝ) ^ p + (993410843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (474314963/500000000 : ℝ)) (y := (993410843/1000000000 : ℝ)) (X := (1886630994139/10000000000000 : ℝ)) (Y := (81133709960571/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993410843/1000000000 : ℝ) ^ p + (474314963/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993410843/1000000000 : ℝ)) (y := (474314963/500000000 : ℝ)) (X := (81133709960571/100000000000000 : ℝ)) (Y := (1886630994139/10000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1942040769/1000000000 : ℝ)) (τ := (474314963/500000000 : ℝ)) (σ := (993410843/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (833343212/875522009 : ℝ) ^ p + (869026459/875522009 : ℝ) ^ p := by
    exact cert_lt (x := (833343212/875522009 : ℝ)) (y := (869026459/875522009 : ℝ)) (X := (10491314093383/50000000000000 : ℝ)) (Y := (790173728121/1000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (474314963/500000000 : ℝ)) (n' := (875522009/1000000000 : ℝ)) (Ab := (208335803/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (948629927/1000000000 : ℝ) ^ p + (993410843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (948629927/1000000000 : ℝ)) (y := (993410843/1000000000 : ℝ)) (X := (18866310570347/100000000000000 : ℝ)) (Y := (81133709960571/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993410843/1000000000 : ℝ) ^ p + (948629927/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993410843/1000000000 : ℝ)) (y := (948629927/1000000000 : ℝ)) (X := (81133709960571/100000000000000 : ℝ)) (Y := (18866310570347/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (194204077/100000000 : ℝ)) (τ := (948629927/1000000000 : ℝ)) (σ := (993410843/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (277781071/291840670 : ℝ) ^ p + (86902646/87552201 : ℝ) ^ p := by
    exact cert_lt (x := (277781071/291840670 : ℝ)) (y := (86902646/87552201 : ℝ)) (X := (20982628225127/100000000000000 : ℝ)) (Y := (39508686416717/50000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (948629927/1000000000 : ℝ)) (n' := (87552201/100000000 : ℝ)) (Ab := (833343213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (194204077/100000000 : ℝ)) (τ := (948629927/1000000000 : ℝ)) (σ := (993410843/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (948629927/1000000000 : ℝ)) (n' := (87552201/100000000 : ℝ)) (Ab := (833343213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (194204077/100000000 : ℝ)) (τ := (948629927/1000000000 : ℝ)) (σ := (993410843/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (948629927/1000000000 : ℝ)) (n' := (87552201/100000000 : ℝ)) (Ab := (833343213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (194204077/100000000 : ℝ)) (τ := (948629927/1000000000 : ℝ)) (σ := (993410843/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (948629927/1000000000 : ℝ)) (n' := (87552201/100000000 : ℝ)) (Ab := (833343213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (194204077/100000000 : ℝ)) (τ := (948629927/1000000000 : ℝ)) (σ := (993410843/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (948629927/1000000000 : ℝ)) (n' := (87552201/100000000 : ℝ)) (Ab := (833343213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (194204077/100000000 : ℝ)) (τ := (948629927/1000000000 : ℝ)) (σ := (993410843/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1715034061/1841309005 : ℝ) ^ p + (366962691/368261801 : ℝ) ^ p := by
    exact cert_lt (x := (1715034061/1841309005 : ℝ)) (y := (366962691/368261801 : ℝ)) (X := (5287063774417/50000000000000 : ℝ)) (Y := (89425872763433/100000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (218814633/231738199 : ℝ) ^ p + (230439089/231738199 : ℝ) ^ p := by
    exact cert_lt (x := (218814633/231738199 : ℝ)) (y := (230439089/231738199 : ℝ)) (X := (16287895288449/100000000000000 : ℝ)) (Y := (41856052731233/50000000000000 : ℝ)) 253 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993410843/1000000000 : ℝ)) (U := (231738199/200000000 : ℝ)) (Ab := (1715034061/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (948629927/1000000000 : ℝ)) (σ := (993410843/1000000000 : ℝ)) (Ab := (218814633/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab089
