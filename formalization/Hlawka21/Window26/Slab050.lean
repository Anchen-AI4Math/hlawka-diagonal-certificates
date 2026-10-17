import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 50, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab050 (p : ℝ) (hpa : (233/8 : ℝ) ≤ p) (hpb : p ≤ (467/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (28698537989/2064380000000 : ℝ) (1423659/200000000 : ℝ) (1600000309657/10321900000000 : ℝ) (591/500 : ℝ) (244132921/125000000 : ℝ) (976481919/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (72332201/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(136/125 : ℝ) ≤ X j i ∧ X j i ≤ -(697/1250 : ℝ)
      else (1029/1250 : ℝ) ≤ X j i ∧ X j i ≤ (2873/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (28698537989/2064380000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1423659/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (188141657/200000000 : ℝ) ^ p + (496859929/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (188141657/200000000 : ℝ)) (y := (496859929/500000000 : ℝ)) (X := (16796426987263/100000000000000 : ℝ)) (Y := (83203593663051/100000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496859929/500000000 : ℝ) ^ p + (188141657/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496859929/500000000 : ℝ)) (y := (188141657/200000000 : ℝ)) (X := (83203593663051/100000000000000 : ℝ)) (Y := (16796426987263/100000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1934428143/1000000000 : ℝ)) (τ := (188141657/200000000 : ℝ)) (σ := (496859929/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (823439553/868159799 : ℝ) ^ p + (861041504/868159799 : ℝ) ^ p := by
    exact cert_lt (x := (823439553/868159799 : ℝ)) (y := (861041504/868159799 : ℝ)) (X := (10680535703409/50000000000000 : ℝ)) (Y := (15727785911629/20000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (188141657/200000000 : ℝ)) (n' := (868159799/1000000000 : ℝ)) (Ab := (823439553/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (47198459/50000000 : ℝ) ^ p + (49649087/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (47198459/50000000 : ℝ)) (y := (49649087/50000000 : ℝ)) (X := (18581519603701/100000000000000 : ℝ)) (Y := (20354624834553/25000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (49649087/50000000 : ℝ) ^ p + (47198459/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (49649087/50000000 : ℝ)) (y := (47198459/50000000 : ℝ)) (X := (20354624834553/25000000000000 : ℝ)) (Y := (18581519603701/100000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (48423773/25000000 : ℝ)) (τ := (47198459/50000000 : ℝ)) (σ := (49649087/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (413434934/435945105 : ℝ) ^ p + (57651461/58126014 : ℝ) ^ p := by
    exact cert_lt (x := (413434934/435945105 : ℝ)) (y := (57651461/58126014 : ℝ)) (X := (21279845061793/100000000000000 : ℝ)) (Y := (19680039016619/25000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (47198459/50000000 : ℝ)) (n' := (87189021/100000000 : ℝ)) (Ab := (206717467/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (944059383/1000000000 : ℝ) ^ p + (992960049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944059383/1000000000 : ℝ)) (y := (992960049/1000000000 : ℝ)) (X := (1863341469673/10000000000000 : ℝ)) (Y := (40683302223623/50000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992960049/1000000000 : ℝ) ^ p + (944059383/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992960049/1000000000 : ℝ)) (y := (944059383/1000000000 : ℝ)) (X := (40683302223623/50000000000000 : ℝ)) (Y := (1863341469673/10000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (242127429/125000000 : ℝ)) (τ := (944059383/1000000000 : ℝ)) (σ := (992960049/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (826964583/871993219 : ℝ) ^ p + (864874924/871993219 : ℝ) ^ p := by
    exact cert_lt (x := (826964583/871993219 : ℝ)) (y := (864874924/871993219 : ℝ)) (X := (21277610687959/100000000000000 : ℝ)) (Y := (7872239028303/10000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (944059383/1000000000 : ℝ)) (n' := (871993219/1000000000 : ℝ)) (Ab := (826964583/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (188812373/200000000 : ℝ) ^ p + (992959451/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188812373/200000000 : ℝ)) (y := (992959451/1000000000 : ℝ)) (X := (18634844604097/100000000000000 : ℝ)) (Y := (40682587103799/50000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992959451/1000000000 : ℝ) ^ p + (188812373/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992959451/1000000000 : ℝ)) (y := (188812373/200000000 : ℝ)) (X := (40682587103799/50000000000000 : ℝ)) (Y := (18634844604097/100000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (484255329/250000000 : ℝ)) (τ := (188812373/200000000 : ℝ)) (σ := (992959451/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (826967189/871996053 : ℝ) ^ p + (288292586/290665351 : ℝ) ^ p := by
    exact cert_lt (x := (826967189/871996053 : ℝ)) (y := (288292586/290665351 : ℝ)) (X := (10638774682871/50000000000000 : ℝ)) (Y := (15744490348911/20000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (188812373/200000000 : ℝ)) (n' := (871996053/1000000000 : ℝ)) (Ab := (826967189/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (236015483/250000000 : ℝ) ^ p + (198591887/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (236015483/250000000 : ℝ)) (y := (198591887/200000000 : ℝ)) (X := (18634883204999/100000000000000 : ℝ)) (Y := (1627302718813/2000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198591887/200000000 : ℝ) ^ p + (236015483/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198591887/200000000 : ℝ)) (y := (236015483/250000000 : ℝ)) (X := (1627302718813/2000000000000 : ℝ)) (Y := (18634883204999/100000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1937021367/1000000000 : ℝ)) (τ := (236015483/250000000 : ℝ)) (σ := (198591887/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (82696726/87199613 : ℝ) ^ p + (172975567/174399226 : ℝ) ^ p := by
    exact cert_lt (x := (82696726/87199613 : ℝ)) (y := (172975567/174399226 : ℝ)) (X := (2659693480737/12500000000000 : ℝ)) (Y := (15744490682893/20000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (236015483/250000000 : ℝ)) (n' := (87199613/100000000 : ℝ)) (Ab := (41348363/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (188812387/200000000 : ℝ) ^ p + (496479717/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (188812387/200000000 : ℝ)) (y := (496479717/500000000 : ℝ)) (X := (93174424667/500000000000 : ℝ)) (Y := (81365133548967/100000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496479717/500000000 : ℝ) ^ p + (188812387/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496479717/500000000 : ℝ)) (y := (188812387/200000000 : ℝ)) (X := (81365133548967/100000000000000 : ℝ)) (Y := (93174424667/500000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1937021369/1000000000 : ℝ)) (τ := (188812387/200000000 : ℝ)) (σ := (496479717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (826967263/871996133 : ℝ) ^ p + (864877838/871996133 : ℝ) ^ p := by
    exact cert_lt (x := (826967263/871996133 : ℝ)) (y := (864877838/871996133 : ℝ)) (X := (4255509592447/20000000000000 : ℝ)) (Y := (39361226739763/50000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (188812387/200000000 : ℝ)) (n' := (871996133/1000000000 : ℝ)) (Ab := (826967263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1937021369/1000000000 : ℝ)) (τ := (188812387/200000000 : ℝ)) (σ := (496479717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (188812387/200000000 : ℝ)) (n' := (871996133/1000000000 : ℝ)) (Ab := (826967263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1937021369/1000000000 : ℝ)) (τ := (188812387/200000000 : ℝ)) (σ := (496479717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (188812387/200000000 : ℝ)) (n' := (871996133/1000000000 : ℝ)) (Ab := (826967263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1937021369/1000000000 : ℝ)) (τ := (188812387/200000000 : ℝ)) (σ := (496479717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (188812387/200000000 : ℝ)) (n' := (871996133/1000000000 : ℝ)) (Ab := (826967263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1937021369/1000000000 : ℝ)) (τ := (188812387/200000000 : ℝ)) (σ := (496479717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (188812387/200000000 : ℝ)) (n' := (871996133/1000000000 : ℝ)) (Ab := (826967263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1937021369/1000000000 : ℝ)) (τ := (188812387/200000000 : ℝ)) (σ := (496479717/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (426689355/460671196 : ℝ) ^ p + (1835566489/1842684784 : ℝ) ^ p := by
    exact cert_lt (x := (426689355/460671196 : ℝ)) (y := (1835566489/1842684784 : ℝ)) (X := (5341114556171/50000000000000 : ℝ)) (Y := (4465888558459/5000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1087985671/1157315216 : ℝ) ^ p + (1150196921/1157315216 : ℝ) ^ p := by
    exact cert_lt (x := (1087985671/1157315216 : ℝ)) (y := (1150196921/1157315216 : ℝ)) (X := (8239740346233/50000000000000 : ℝ)) (Y := (83520520109817/100000000000000 : ℝ)) 467 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496479717/500000000 : ℝ)) (U := (72332201/62500000 : ℝ)) (Ab := (85337871/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (188812387/200000000 : ℝ)) (σ := (496479717/500000000 : ℝ)) (Ab := (1087985671/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab050
