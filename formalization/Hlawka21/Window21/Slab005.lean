import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 5, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab005 (p : ℝ) (hpa : (677/32 : ℝ) ≤ p) (hpb : p ≤ (339/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (266045840017/11551312500000 : ℝ) (2974843/250000000 : ℝ) (4000000554463/18482100000000 : ℝ) (3033/2500 : ℝ) (483907217/250000000 : ℝ) (483883833/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (74528461/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(1103/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(4417/10000 : ℝ)
      else (7569/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11831/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (266045840017/11551312500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2974843/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (909267269/1000000000 : ℝ) ^ p + (993271423/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (909267269/1000000000 : ℝ)) (y := (993271423/1000000000 : ℝ)) (X := (3332095148127/25000000000000 : ℝ)) (Y := (86671636044413/100000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993271423/1000000000 : ℝ) ^ p + (909267269/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993271423/1000000000 : ℝ)) (y := (909267269/1000000000 : ℝ)) (X := (86671636044413/100000000000000 : ℝ)) (Y := (3332095148127/25000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (475634673/250000000 : ℝ)) (τ := (909267269/1000000000 : ℝ)) (σ := (993271423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (36651726/39011809 : ℝ) ^ p + (807348617/819247989 : ℝ) ^ p := by
    exact cert_lt (x := (36651726/39011809 : ℝ)) (y := (807348617/819247989 : ℝ)) (X := (666382569627/2500000000000 : ℝ)) (Y := (573005457123/781250000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (909267269/1000000000 : ℝ)) (n' := (819247989/1000000000 : ℝ)) (Ab := (384843123/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (457617117/500000000 : ℝ) ^ p + (248046983/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (457617117/500000000 : ℝ)) (y := (248046983/250000000 : ℝ)) (X := (612385181849/4000000000000 : ℝ)) (Y := (42345192994889/50000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248046983/250000000 : ℝ) ^ p + (457617117/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248046983/250000000 : ℝ)) (y := (457617117/500000000 : ℝ)) (X := (42345192994889/50000000000000 : ℝ)) (Y := (612385181849/4000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (953711083/500000000 : ℝ)) (τ := (457617117/500000000 : ℝ)) (σ := (248046983/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (776142269/826411669 : ℝ) ^ p + (814512297/826411669 : ℝ) ^ p := by
    exact cert_lt (x := (776142269/826411669 : ℝ)) (y := (814512297/826411669 : ℝ)) (X := (1653531535893/6250000000000 : ℝ)) (Y := (36771748088407/50000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (457617117/500000000 : ℝ)) (n' := (826411669/1000000000 : ℝ)) (Ab := (776142269/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (915537621/1000000000 : ℝ) ^ p + (992128241/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915537621/1000000000 : ℝ)) (y := (992128241/1000000000 : ℝ)) (X := (15417514996507/100000000000000 : ℝ)) (Y := (84582500003007/100000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992128241/1000000000 : ℝ) ^ p + (915537621/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992128241/1000000000 : ℝ)) (y := (915537621/1000000000 : ℝ)) (X := (84582500003007/100000000000000 : ℝ)) (Y := (15417514996507/100000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (953832931/500000000 : ℝ)) (τ := (915537621/1000000000 : ℝ)) (σ := (992128241/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (388234677/413387342 : ℝ) ^ p + (203718828/206693671 : ℝ) ^ p := by
    exact cert_lt (x := (388234677/413387342 : ℝ)) (y := (203718828/206693671 : ℝ)) (X := (6611627297629/25000000000000 : ℝ)) (Y := (3677674596937/5000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (915537621/1000000000 : ℝ)) (n' := (206693671/250000000 : ℝ)) (Ab := (388234677/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (915552871/1000000000 : ℝ) ^ p + (248031307/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (915552871/1000000000 : ℝ)) (y := (248031307/250000000 : ℝ)) (X := (7711478512201/50000000000000 : ℝ)) (Y := (21144264439029/25000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248031307/250000000 : ℝ) ^ p + (915552871/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248031307/250000000 : ℝ)) (y := (915552871/1000000000 : ℝ)) (X := (21144264439029/25000000000000 : ℝ)) (Y := (7711478512201/50000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1907678099/1000000000 : ℝ)) (τ := (915552871/1000000000 : ℝ)) (σ := (248031307/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (776485793/826792929 : ℝ) ^ p + (814893557/826792929 : ℝ) ^ p := by
    exact cert_lt (x := (776485793/826792929 : ℝ)) (y := (814893557/826792929 : ℝ)) (X := (6611501757269/25000000000000 : ℝ)) (Y := (7355399412453/10000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (915552871/1000000000 : ℝ)) (n' := (826792929/1000000000 : ℝ)) (Ab := (776485793/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (915553637/1000000000 : ℝ) ^ p + (992125077/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915553637/1000000000 : ℝ)) (y := (992125077/1000000000 : ℝ)) (X := (963951901441/6250000000000 : ℝ)) (Y := (42288392510181/50000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992125077/1000000000 : ℝ) ^ p + (915553637/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992125077/1000000000 : ℝ)) (y := (915553637/1000000000 : ℝ)) (X := (42288392510181/50000000000000 : ℝ)) (Y := (963951901441/6250000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (953839357/500000000 : ℝ)) (τ := (915553637/1000000000 : ℝ)) (σ := (992125077/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (776486618/826793845 : ℝ) ^ p + (814894473/826793845 : ℝ) ^ p := by
    exact cert_lt (x := (776486618/826793845 : ℝ)) (y := (814894473/826793845 : ℝ)) (X := (26445981581347/100000000000000 : ℝ)) (Y := (36777009668269/50000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (915553637/1000000000 : ℝ)) (n' := (165358769/200000000 : ℝ)) (Ab := (388243309/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (228888419/250000000 : ℝ) ^ p + (992125069/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (228888419/250000000 : ℝ)) (y := (992125069/1000000000 : ℝ)) (X := (3084648868591/20000000000000 : ℝ)) (Y := (84576770570809/100000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992125069/1000000000 : ℝ) ^ p + (228888419/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992125069/1000000000 : ℝ)) (y := (228888419/250000000 : ℝ)) (X := (84576770570809/100000000000000 : ℝ)) (Y := (3084648868591/20000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (381535749/200000000 : ℝ)) (τ := (228888419/250000000 : ℝ)) (σ := (992125069/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (13622573/14505156 : ℝ) ^ p + (203723630/206698473 : ℝ) ^ p := by
    exact cert_lt (x := (13622573/14505156 : ℝ)) (y := (203723630/206698473 : ℝ)) (X := (1322299037927/5000000000000 : ℝ)) (Y := (36777010315083/50000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (228888419/250000000 : ℝ)) (n' := (206698473/250000000 : ℝ)) (Ab := (776486661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (915553677/1000000000 : ℝ) ^ p + (992125069/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915553677/1000000000 : ℝ)) (y := (992125069/1000000000 : ℝ)) (X := (123385957599/800000000000 : ℝ)) (Y := (84576770570809/100000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992125069/1000000000 : ℝ) ^ p + (915553677/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992125069/1000000000 : ℝ)) (y := (915553677/1000000000 : ℝ)) (X := (84576770570809/100000000000000 : ℝ)) (Y := (123385957599/800000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (953839373/500000000 : ℝ)) (τ := (915553677/1000000000 : ℝ)) (σ := (992125069/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (776486661/826793893 : ℝ) ^ p + (814894521/826793893 : ℝ) ^ p := by
    exact cert_lt (x := (776486661/826793893 : ℝ)) (y := (814894521/826793893 : ℝ)) (X := (413218438763/1562500000000 : ℝ)) (Y := (7355402065769/10000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (915553677/1000000000 : ℝ)) (n' := (826793893/1000000000 : ℝ)) (Ab := (776486661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (953839373/500000000 : ℝ)) (τ := (915553677/1000000000 : ℝ)) (σ := (992125069/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (915553677/1000000000 : ℝ)) (n' := (826793893/1000000000 : ℝ)) (Ab := (776486661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (953839373/500000000 : ℝ)) (τ := (915553677/1000000000 : ℝ)) (σ := (992125069/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (915553677/1000000000 : ℝ)) (n' := (826793893/1000000000 : ℝ)) (Ab := (776486661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (953839373/500000000 : ℝ)) (τ := (915553677/1000000000 : ℝ)) (σ := (992125069/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (915553677/1000000000 : ℝ)) (n' := (826793893/1000000000 : ℝ)) (Ab := (776486661/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (953839373/500000000 : ℝ)) (τ := (915553677/1000000000 : ℝ)) (σ := (992125069/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (410489721/451886156 : ℝ) ^ p + (448911313/451886156 : ℝ) ^ p := by
    exact cert_lt (x := (410489721/451886156 : ℝ)) (y := (448911313/451886156 : ℝ)) (X := (13059137209571/100000000000000 : ℝ)) (Y := (86940862972249/100000000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1102947485/1192455376 : ℝ) ^ p + (295139001/298113844 : ℝ) ^ p := by
    exact cert_lt (x := (1102947485/1192455376 : ℝ)) (y := (295139001/298113844 : ℝ)) (X := (19143123757141/100000000000000 : ℝ)) (Y := (10107109595809/12500000000000 : ℝ)) 339 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992125069/1000000000 : ℝ)) (U := (74528461/62500000 : ℝ)) (Ab := (410489721/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (915553677/1000000000 : ℝ)) (σ := (992125069/1000000000 : ℝ)) (Ab := (220589497/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab005
