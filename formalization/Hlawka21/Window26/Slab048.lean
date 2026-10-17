import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 48, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab048 (p : ℝ) (hpa : (29 : ℝ) ≤ p) (hpb : p ≤ (465/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (280404413/20073437500 : ℝ) (894177/125000000 : ℝ) (200000038541/1284700000000 : ℝ) (591/500 : ℝ) (122053993/62500000 : ℝ) (488190877/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289310249/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10877/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1393/2500 : ℝ)
      else (2057/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11491/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (280404413/20073437500 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (894177/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (94044109/100000000 : ℝ) ^ p + (49684859/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (94044109/100000000 : ℝ)) (y := (49684859/50000000 : ℝ)) (X := (8393044354303/50000000000000 : ℝ)) (Y := (83213931596011/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (49684859/50000000 : ℝ) ^ p + (94044109/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (49684859/50000000 : ℝ)) (y := (94044109/100000000 : ℝ)) (X := (83213931596011/100000000000000 : ℝ)) (Y := (8393044354303/50000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (193413827/100000000 : ℝ)) (τ := (94044109/100000000 : ℝ)) (σ := (49684859/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (411535758/433972727 : ℝ) ^ p + (430396019/433972727 : ℝ) ^ p := by
    exact cert_lt (x := (411535758/433972727 : ℝ)) (y := (430396019/433972727 : ℝ)) (X := (1336128214097/6250000000000 : ℝ)) (Y := (314487798201/400000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (94044109/100000000 : ℝ)) (n' := (433972727/500000000 : ℝ)) (Ab := (205767879/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (471856037/500000000 : ℝ) ^ p + (992957187/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471856037/500000000 : ℝ)) (y := (992957187/1000000000 : ℝ)) (X := (18568349562251/100000000000000 : ℝ)) (Y := (81431669976271/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992957187/1000000000 : ℝ) ^ p + (471856037/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992957187/1000000000 : ℝ)) (y := (471856037/500000000 : ℝ)) (X := (81431669976271/100000000000000 : ℝ)) (Y := (18568349562251/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1936669261/1000000000 : ℝ)) (τ := (471856037/500000000 : ℝ)) (σ := (992957187/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (275504228/290562971 : ℝ) ^ p + (288178499/290562971 : ℝ) ^ p := by
    exact cert_lt (x := (275504228/290562971 : ℝ)) (y := (288178499/290562971 : ℝ)) (X := (1064823240377/5000000000000 : ℝ)) (Y := (78703536569683/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (471856037/500000000 : ℝ)) (n' := (871688913/1000000000 : ℝ)) (Ab := (206628171/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (188760611/200000000 : ℝ) ^ p + (496467661/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (188760611/200000000 : ℝ)) (y := (496467661/500000000 : ℝ)) (X := (465511141099/2500000000000 : ℝ)) (Y := (81379573171003/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496467661/500000000 : ℝ) ^ p + (188760611/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496467661/500000000 : ℝ)) (y := (188760611/200000000 : ℝ)) (X := (81379573171003/100000000000000 : ℝ)) (Y := (465511141099/2500000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1936738377/1000000000 : ℝ)) (τ := (188760611/200000000 : ℝ)) (σ := (496467661/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (413304111/435896426 : ℝ) ^ p + (216159859/217948213 : ℝ) ^ p := by
    exact cert_lt (x := (413304111/435896426 : ℝ)) (y := (216159859/217948213 : ℝ)) (X := (5323551998171/25000000000000 : ℝ)) (Y := (9838224129667/12500000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (188760611/200000000 : ℝ)) (n' := (217948213/250000000 : ℝ)) (Ab := (413304111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (235951393/250000000 : ℝ) ^ p + (248233679/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (235951393/250000000 : ℝ)) (y := (248233679/250000000 : ℝ)) (X := (18621888892507/100000000000000 : ℝ)) (Y := (5086133108689/6250000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248233679/250000000 : ℝ) ^ p + (235951393/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248233679/250000000 : ℝ)) (y := (235951393/250000000 : ℝ)) (X := (5086133108689/6250000000000 : ℝ)) (Y := (18621888892507/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (30261567/15625000 : ℝ)) (τ := (235951393/250000000 : ℝ)) (σ := (248233679/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (826610865/871795727 : ℝ) ^ p + (864642311/871795727 : ℝ) ^ p := by
    exact cert_lt (x := (826610865/871795727 : ℝ)) (y := (864642311/871795727 : ℝ)) (X := (21294145860201/100000000000000 : ℝ)) (Y := (78705855445497/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (235951393/250000000 : ℝ)) (n' := (871795727/1000000000 : ℝ)) (Ab := (165322173/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (471902821/500000000 : ℝ) ^ p + (992934699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471902821/500000000 : ℝ)) (y := (992934699/1000000000 : ℝ)) (X := (18621929032071/100000000000000 : ℝ)) (Y := (10172261155883/12500000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992934699/1000000000 : ℝ) ^ p + (471902821/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992934699/1000000000 : ℝ)) (y := (471902821/500000000 : ℝ)) (X := (10172261155883/12500000000000 : ℝ)) (Y := (18621929032071/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1936740341/1000000000 : ℝ)) (τ := (471902821/500000000 : ℝ)) (σ := (992934699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (826610938/871795807 : ℝ) ^ p + (864642391/871795807 : ℝ) ^ p := by
    exact cert_lt (x := (826610938/871795807 : ℝ)) (y := (864642391/871795807 : ℝ)) (X := (21294143723767/100000000000000 : ℝ)) (Y := (78705857182067/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (471902821/500000000 : ℝ)) (n' := (871795807/1000000000 : ℝ)) (Ab := (413305469/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (943805643/1000000000 : ℝ) ^ p + (992934699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943805643/1000000000 : ℝ)) (y := (992934699/1000000000 : ℝ)) (X := (9310964802747/50000000000000 : ℝ)) (Y := (10172261155883/12500000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992934699/1000000000 : ℝ) ^ p + (943805643/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992934699/1000000000 : ℝ)) (y := (943805643/1000000000 : ℝ)) (X := (10172261155883/12500000000000 : ℝ)) (Y := (9310964802747/50000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (968370171/500000000 : ℝ)) (τ := (943805643/1000000000 : ℝ)) (σ := (992934699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (826610939/871795808 : ℝ) ^ p + (108080299/108974476 : ℝ) ^ p := by
    exact cert_lt (x := (826610939/871795808 : ℝ)) (y := (108080299/108974476 : ℝ)) (X := (21294143762571/100000000000000 : ℝ)) (Y := (39352928601887/50000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (943805643/1000000000 : ℝ)) (n' := (27243619/31250000 : ℝ)) (Ab := (826610939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (968370171/500000000 : ℝ)) (τ := (943805643/1000000000 : ℝ)) (σ := (992934699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (943805643/1000000000 : ℝ)) (n' := (27243619/31250000 : ℝ)) (Ab := (826610939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (968370171/500000000 : ℝ)) (τ := (943805643/1000000000 : ℝ)) (σ := (992934699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (943805643/1000000000 : ℝ)) (n' := (27243619/31250000 : ℝ)) (Ab := (826610939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (968370171/500000000 : ℝ)) (τ := (943805643/1000000000 : ℝ)) (σ := (992934699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (943805643/1000000000 : ℝ)) (n' := (27243619/31250000 : ℝ)) (Ab := (826610939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (968370171/500000000 : ℝ)) (τ := (943805643/1000000000 : ℝ)) (σ := (992934699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (943805643/1000000000 : ℝ)) (n' := (27243619/31250000 : ℝ)) (Ab := (826610939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (968370171/500000000 : ℝ)) (τ := (943805643/1000000000 : ℝ)) (σ := (992934699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (426574235/460689751 : ℝ) ^ p + (458901397/460689751 : ℝ) ^ p := by
    exact cert_lt (x := (426574235/460689751 : ℝ)) (y := (458901397/460689751 : ℝ)) (X := (2137655201069/20000000000000 : ℝ)) (Y := (89311724247377/100000000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1087651111/1157240996 : ℝ) ^ p + (287521895/289310249 : ℝ) ^ p := by
    exact cert_lt (x := (1087651111/1157240996 : ℝ)) (y := (287521895/289310249 : ℝ)) (X := (16490154958703/100000000000000 : ℝ)) (Y := (10438730735887/12500000000000 : ℝ)) 465 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992934699/1000000000 : ℝ)) (U := (289310249/250000000 : ℝ)) (Ab := (85314847/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (943805643/1000000000 : ℝ)) (σ := (992934699/1000000000 : ℝ)) (Ab := (1087651111/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab048
