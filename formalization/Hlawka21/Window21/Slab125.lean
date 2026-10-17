import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 125, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab125 (p : ℝ) (hpa : (797/32 : ℝ) ≤ p) (hpb : p ≤ (399/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2084455960607/108790500000000 : ℝ) (9850501/1000000000 : ℝ) (4000000652743/21758100000000 : ℝ) (3033/2500 : ℝ) (486293681/250000000 : ℝ) (972553443/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298490441/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11163/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4651/10000 : ℝ)
      else (39/50 : ℝ) ≤ X j i ∧ X j i ≤ (11857/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2084455960607/108790500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9850501/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (461790737/500000000 : ℝ) ^ p + (24851879/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (461790737/500000000 : ℝ)) (y := (24851879/25000000 : ℝ)) (X := (430415738009/3125000000000 : ℝ)) (Y := (86226715330481/100000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (24851879/25000000 : ℝ) ^ p + (461790737/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (24851879/25000000 : ℝ)) (y := (461790737/500000000 : ℝ)) (X := (86226715330481/100000000000000 : ℝ)) (Y := (430415738009/3125000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958828317/500000000 : ℝ)) (τ := (461790737/500000000 : ℝ)) (σ := (24851879/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (788498083/832678195 : ℝ) ^ p + (822827694/832678195 : ℝ) ^ p := by
    exact cert_lt (x := (788498083/832678195 : ℝ)) (y := (822827694/832678195 : ℝ)) (X := (25678285705471/100000000000000 : ℝ)) (Y := (14864343062501/20000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (461790737/500000000 : ℝ)) (n' := (166535639/200000000 : ℝ)) (Ab := (788498083/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (929042117/1000000000 : ℝ) ^ p + (248263587/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (929042117/1000000000 : ℝ)) (y := (248263587/250000000 : ℝ)) (X := (3988621834821/25000000000000 : ℝ)) (Y := (84045529587217/100000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248263587/250000000 : ℝ) ^ p + (929042117/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248263587/250000000 : ℝ)) (y := (929042117/1000000000 : ℝ)) (X := (84045529587217/100000000000000 : ℝ)) (Y := (3988621834821/25000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (384419293/200000000 : ℝ)) (τ := (929042117/1000000000 : ℝ)) (σ := (248263587/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (397183620/419549831 : ℝ) ^ p + (829249161/839099662 : ℝ) ^ p := by
    exact cert_lt (x := (397183620/419549831 : ℝ)) (y := (829249161/839099662 : ℝ)) (X := (6377074687871/25000000000000 : ℝ)) (Y := (14898340411127/20000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (929042117/1000000000 : ℝ)) (n' := (419549831/500000000 : ℝ)) (Ab := (19859181/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (929263229/1000000000 : ℝ) ^ p + (99300933/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (929263229/1000000000 : ℝ)) (y := (99300933/100000000 : ℝ)) (X := (8024724716447/50000000000000 : ℝ)) (Y := (83950568628639/100000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99300933/100000000 : ℝ) ^ p + (929263229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99300933/100000000 : ℝ)) (y := (929263229/1000000000 : ℝ)) (X := (83950568628639/100000000000000 : ℝ)) (Y := (8024724716447/50000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1922272559/1000000000 : ℝ)) (τ := (929263229/1000000000 : ℝ)) (σ := (99300933/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (794604143/839358899 : ℝ) ^ p + (829508398/839358899 : ℝ) ^ p := by
    exact cert_lt (x := (794604143/839358899 : ℝ)) (y := (829508398/839358899 : ℝ)) (X := (12750741918313/50000000000000 : ℝ)) (Y := (18624629407447/25000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (929263229/1000000000 : ℝ)) (n' := (839358899/1000000000 : ℝ)) (Ab := (794604143/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (232318023/250000000 : ℝ) ^ p + (993007519/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232318023/250000000 : ℝ)) (y := (993007519/1000000000 : ℝ)) (X := (16053267157753/100000000000000 : ℝ)) (Y := (83946750661407/100000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993007519/1000000000 : ℝ) ^ p + (232318023/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993007519/1000000000 : ℝ)) (y := (232318023/250000000 : ℝ)) (X := (83946750661407/100000000000000 : ℝ)) (Y := (16053267157753/100000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1922279611/1000000000 : ℝ)) (τ := (232318023/250000000 : ℝ)) (σ := (993007519/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (794613637/839369289 : ℝ) ^ p + (6531644/6609207 : ℝ) ^ p := by
    exact cert_lt (x := (794613637/839369289 : ℝ)) (y := (6531644/6609207 : ℝ)) (X := (12750605063383/50000000000000 : ℝ)) (Y := (9312348839621/12500000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (232318023/250000000 : ℝ)) (n' := (839369289/1000000000 : ℝ)) (Ab := (794613637/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (7259941/7812500 : ℝ) ^ p + (496503723/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (7259941/7812500 : ℝ)) (y := (496503723/500000000 : ℝ)) (X := (501669391327/3125000000000 : ℝ)) (Y := (16789319353123/20000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496503723/500000000 : ℝ) ^ p + (7259941/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (496503723/500000000 : ℝ)) (y := (7259941/7812500 : ℝ)) (X := (16789319353123/20000000000000 : ℝ)) (Y := (501669391327/3125000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961139947/500000000 : ℝ)) (τ := (7259941/7812500 : ℝ)) (σ := (496503723/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (794614019/839369706 : ℝ) ^ p + (829519205/839369706 : ℝ) ^ p := by
    exact cert_lt (x := (794614019/839369706 : ℝ)) (y := (829519205/839369706 : ℝ)) (X := (25501199910573/100000000000000 : ℝ)) (Y := (18624700419283/25000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (7259941/7812500 : ℝ)) (n' := (419684853/500000000 : ℝ)) (Ab := (794614019/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (464636231/500000000 : ℝ) ^ p + (993007443/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464636231/500000000 : ℝ)) (y := (993007443/1000000000 : ℝ)) (X := (1605342655369/10000000000000 : ℝ)) (Y := (5246661902571/6250000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993007443/1000000000 : ℝ) ^ p + (464636231/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993007443/1000000000 : ℝ)) (y := (464636231/500000000 : ℝ)) (X := (5246661902571/6250000000000 : ℝ)) (Y := (1605342655369/10000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (384455981/200000000 : ℝ)) (τ := (464636231/500000000 : ℝ)) (σ := (993007443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (794614034/839369723 : ℝ) ^ p + (829519222/839369723 : ℝ) ^ p := by
    exact cert_lt (x := (794614034/839369723 : ℝ)) (y := (829519222/839369723 : ℝ)) (X := (6375299758849/25000000000000 : ℝ)) (Y := (74498802123949/100000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (464636231/500000000 : ℝ)) (n' := (839369723/1000000000 : ℝ)) (Ab := (397307017/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (929272463/1000000000 : ℝ) ^ p + (993007443/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (929272463/1000000000 : ℝ)) (y := (993007443/1000000000 : ℝ)) (X := (4013356746123/25000000000000 : ℝ)) (Y := (5246661902571/6250000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993007443/1000000000 : ℝ) ^ p + (929272463/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993007443/1000000000 : ℝ)) (y := (929272463/1000000000 : ℝ)) (X := (5246661902571/6250000000000 : ℝ)) (Y := (4013356746123/25000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (961139953/500000000 : ℝ)) (τ := (929272463/1000000000 : ℝ)) (σ := (993007443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (264871345/279789908 : ℝ) ^ p + (829519223/839369724 : ℝ) ^ p := by
    exact cert_lt (x := (264871345/279789908 : ℝ)) (y := (829519223/839369724 : ℝ)) (X := (25501199078069/100000000000000 : ℝ)) (Y := (9312350268779/12500000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (929272463/1000000000 : ℝ)) (n' := (209842431/250000000 : ℝ)) (Ab := (158922807/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (961139953/500000000 : ℝ)) (τ := (929272463/1000000000 : ℝ)) (σ := (993007443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (929272463/1000000000 : ℝ)) (n' := (209842431/250000000 : ℝ)) (Ab := (158922807/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (961139953/500000000 : ℝ)) (τ := (929272463/1000000000 : ℝ)) (σ := (993007443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (929272463/1000000000 : ℝ)) (n' := (209842431/250000000 : ℝ)) (Ab := (158922807/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (961139953/500000000 : ℝ)) (τ := (929272463/1000000000 : ℝ)) (σ := (993007443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (929272463/1000000000 : ℝ)) (n' := (209842431/250000000 : ℝ)) (Ab := (158922807/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (961139953/500000000 : ℝ)) (τ := (929272463/1000000000 : ℝ)) (σ := (993007443/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (415716204/451509559 : ℝ) ^ p + (1796187735/1806038236 : ℝ) ^ p := by
    exact cert_lt (x := (415716204/451509559 : ℝ)) (y := (1796187735/1806038236 : ℝ)) (X := (1593683148443/12500000000000 : ℝ)) (Y := (10906316892033/12500000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1116242381/1193961764 : ℝ) ^ p + (1184111263/1193961764 : ℝ) ^ p := by
    exact cert_lt (x := (1116242381/1193961764 : ℝ)) (y := (1184111263/1193961764 : ℝ)) (X := (18665052261861/100000000000000 : ℝ)) (Y := (81334948547277/100000000000000 : ℝ)) 399 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993007443/1000000000 : ℝ)) (U := (298490441/250000000 : ℝ)) (Ab := (103929051/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (929272463/1000000000 : ℝ)) (σ := (993007443/1000000000 : ℝ)) (Ab := (1116242381/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab125
