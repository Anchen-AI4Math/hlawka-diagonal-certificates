import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 45, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab045 (p : ℝ) (hpa : (461/16 : ℝ) ≤ p) (hpb : p ≤ (231/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (89799940861/6381968750000 : ℝ) (1801687/250000000 : ℝ) (3200000612669/20422300000000 : ℝ) (591/500 : ℝ) (488140367/250000000 : ℝ) (488114949/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157129/1000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1359/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(1113/2000 : ℝ)
      else (8221/10000 : ℝ) ≤ X j i ∧ X j i ≤ (1149/1000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (89799940861/6381968750000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1801687/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (117504469/125000000 : ℝ) ^ p + (198732573/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (117504469/125000000 : ℝ)) (y := (198732573/200000000 : ℝ)) (X := (209630144237/1250000000000 : ℝ)) (Y := (5201850511119/6250000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198732573/200000000 : ℝ) ^ p + (117504469/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (198732573/200000000 : ℝ)) (y := (117504469/125000000 : ℝ)) (X := (5201850511119/6250000000000 : ℝ)) (Y := (209630144237/1250000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1933698617/1000000000 : ℝ)) (τ := (117504469/125000000 : ℝ)) (σ := (198732573/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (45695192/48201099 : ℝ) ^ p + (430206517/433809891 : ℝ) ^ p := by
    exact cert_lt (x := (45695192/48201099 : ℝ)) (y := (430206517/433809891 : ℝ)) (X := (21403841197117/100000000000000 : ℝ)) (Y := (15719232017199/20000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (117504469/125000000 : ℝ)) (n' := (433809891/500000000 : ℝ)) (Ab := (51407091/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (471660971/500000000 : ℝ) ^ p + (496460027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (471660971/500000000 : ℝ)) (y := (496460027/500000000 : ℝ)) (X := (927418314127/5000000000000 : ℝ)) (Y := (40725826208799/50000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496460027/500000000 : ℝ) ^ p + (471660971/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496460027/500000000 : ℝ)) (y := (471660971/500000000 : ℝ)) (X := (40725826208799/50000000000000 : ℝ)) (Y := (927418314127/5000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (484060499/250000000 : ℝ)) (τ := (471660971/500000000 : ℝ)) (σ := (496460027/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (825970990/871382943 : ℝ) ^ p + (864176195/871382943 : ℝ) ^ p := by
    exact cert_lt (x := (825970990/871382943 : ℝ)) (y := (864176195/871382943 : ℝ)) (X := (21321707542043/100000000000000 : ℝ)) (Y := (78678293218647/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (471660971/500000000 : ℝ)) (n' := (871382943/1000000000 : ℝ)) (Ab := (82597099/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (943414109/1000000000 : ℝ) ^ p + (39715917/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (943414109/1000000000 : ℝ)) (y := (39715917/40000000 : ℝ)) (X := (4650191673319/25000000000000 : ℝ)) (Y := (81399252029533/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39715917/40000000 : ℝ) ^ p + (943414109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39715917/40000000 : ℝ)) (y := (943414109/1000000000 : ℝ)) (X := (81399252029533/100000000000000 : ℝ)) (Y := (4650191673319/25000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (968156017/500000000 : ℝ)) (τ := (943414109/1000000000 : ℝ)) (σ := (39715917/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (826067783/871488300 : ℝ) ^ p + (216070388/217872075 : ℝ) ^ p := by
    exact cert_lt (x := (826067783/871488300 : ℝ)) (y := (216070388/217872075 : ℝ)) (X := (10659708561837/50000000000000 : ℝ)) (Y := (39340291837177/50000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (943414109/1000000000 : ℝ)) (n' := (8714883/10000000 : ℝ)) (Ab := (826067783/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (943416679/1000000000 : ℝ) ^ p + (992897307/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943416679/1000000000 : ℝ)) (y := (992897307/1000000000 : ℝ)) (X := (18602229881119/100000000000000 : ℝ)) (Y := (81397789103017/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992897307/1000000000 : ℝ) ^ p + (943416679/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992897307/1000000000 : ℝ)) (y := (943416679/1000000000 : ℝ)) (X := (81397789103017/100000000000000 : ℝ)) (Y := (18602229881119/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (968156993/500000000 : ℝ)) (τ := (943416679/1000000000 : ℝ)) (σ := (992897307/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (826070483/871491238 : ℝ) ^ p + (432142245/435745619 : ℝ) ^ p := by
    exact cert_lt (x := (826070483/871491238 : ℝ)) (y := (432142245/435745619 : ℝ)) (X := (426387077457/2000000000000 : ℝ)) (Y := (78680647539307/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (943416679/1000000000 : ℝ)) (n' := (435745619/500000000 : ℝ)) (Ab := (826070483/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (943416751/1000000000 : ℝ) ^ p + (99289729/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (943416751/1000000000 : ℝ)) (y := (99289729/100000000 : ℝ)) (X := (145330241209/781250000000 : ℝ)) (Y := (81397748861061/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99289729/100000000 : ℝ) ^ p + (943416751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99289729/100000000 : ℝ)) (y := (943416751/1000000000 : ℝ)) (X := (81397748861061/100000000000000 : ℝ)) (Y := (145330241209/781250000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1936314041/1000000000 : ℝ)) (τ := (943416751/1000000000 : ℝ)) (σ := (99289729/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (413035279/435745660 : ℝ) ^ p + (216071143/217872830 : ℝ) ^ p := by
    exact cert_lt (x := (413035279/435745660 : ℝ)) (y := (216071143/217872830 : ℝ)) (X := (21319351841191/100000000000000 : ℝ)) (Y := (39340324660891/50000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (943416751/1000000000 : ℝ)) (n' := (21787283/25000000 : ℝ)) (Ab := (413035279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (943416753/1000000000 : ℝ) ^ p + (992897289/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943416753/1000000000 : ℝ)) (y := (992897289/1000000000 : ℝ)) (X := (9301136006733/50000000000000 : ℝ)) (Y := (1271839788967/1562500000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992897289/1000000000 : ℝ) ^ p + (943416753/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992897289/1000000000 : ℝ)) (y := (943416753/1000000000 : ℝ)) (X := (1271839788967/1562500000000 : ℝ)) (Y := (9301136006733/50000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (968157021/500000000 : ℝ)) (τ := (943416753/1000000000 : ℝ)) (σ := (992897289/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (413035280/435745661 : ℝ) ^ p + (432142287/435745661 : ℝ) ^ p := by
    exact cert_lt (x := (413035280/435745661 : ℝ)) (y := (432142287/435745661 : ℝ)) (X := (2131935191887/10000000000000 : ℝ)) (Y := (78680649365257/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (943416753/1000000000 : ℝ)) (n' := (435745661/500000000 : ℝ)) (Ab := (5162941/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (968157021/500000000 : ℝ)) (τ := (943416753/1000000000 : ℝ)) (σ := (992897289/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (943416753/1000000000 : ℝ)) (n' := (435745661/500000000 : ℝ)) (Ab := (5162941/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (968157021/500000000 : ℝ)) (τ := (943416753/1000000000 : ℝ)) (σ := (992897289/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (943416753/1000000000 : ℝ)) (n' := (435745661/500000000 : ℝ)) (Ab := (5162941/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (968157021/500000000 : ℝ)) (τ := (943416753/1000000000 : ℝ)) (σ := (992897289/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (943416753/1000000000 : ℝ)) (n' := (435745661/500000000 : ℝ)) (Ab := (5162941/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (968157021/500000000 : ℝ)) (τ := (943416753/1000000000 : ℝ)) (σ := (992897289/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (943416753/1000000000 : ℝ)) (n' := (435745661/500000000 : ℝ)) (Ab := (5162941/6250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (968157021/500000000 : ℝ)) (τ := (943416753/1000000000 : ℝ)) (σ := (992897289/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (852799523/921435500 : ℝ) ^ p + (458916063/460717750 : ℝ) ^ p := by
    exact cert_lt (x := (852799523/921435500 : ℝ)) (y := (458916063/460717750 : ℝ)) (X := (10697455692977/100000000000000 : ℝ)) (Y := (89302544544267/100000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (543572459/578564500 : ℝ) ^ p + (287480563/289282250 : ℝ) ^ p := by
    exact cert_lt (x := (543572459/578564500 : ℝ)) (y := (287480563/289282250 : ℝ)) (X := (128955841819/781250000000 : ℝ)) (Y := (16698730605563/20000000000000 : ℝ)) 231 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992897289/1000000000 : ℝ)) (U := (1157129/1000000 : ℝ)) (Ab := (852799523/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (943416753/1000000000 : ℝ)) (σ := (992897289/1000000000 : ℝ)) (Ab := (543572459/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab045
