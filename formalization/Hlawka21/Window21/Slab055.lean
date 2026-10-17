import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 55, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab055 (p : ℝ) (hpa : (727/32 : ℝ) ≤ p) (hpb : p ≤ (91/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1054163198917/49617750000000 : ℝ) (10951941/1000000000 : ℝ) (4000000595413/19847100000000 : ℝ) (3033/2500 : ℝ) (121248933/62500000 : ℝ) (242487703/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193072899/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11089/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(181/400 : ℝ)
      else (1919/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1054163198917/49617750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10951941/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (457916897/500000000 : ℝ) ^ p + (496814941/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (457916897/500000000 : ℝ)) (y := (496814941/500000000 : ℝ)) (X := (13530976033807/100000000000000 : ℝ)) (Y := (43234520939609/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496814941/500000000 : ℝ) ^ p + (457916897/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496814941/500000000 : ℝ)) (y := (457916897/500000000 : ℝ)) (X := (43234520939609/50000000000000 : ℝ)) (Y := (13530976033807/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (477365919/250000000 : ℝ)) (τ := (457916897/500000000 : ℝ)) (σ := (496814941/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778292668/825486607 : ℝ) ^ p + (74048606/75044237 : ℝ) ^ p := by
    exact cert_lt (x := (778292668/825486607 : ℝ)) (y := (74048606/75044237 : ℝ)) (X := (13101428564727/50000000000000 : ℝ)) (Y := (36898571860721/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457916897/500000000 : ℝ)) (n' := (825486607/1000000000 : ℝ)) (Ab := (194573167/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (115199347/125000000 : ℝ) ^ p + (12407121/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (115199347/125000000 : ℝ)) (y := (12407121/12500000 : ℝ)) (X := (15605766272143/100000000000000 : ℝ)) (Y := (10549281213333/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (12407121/12500000 : ℝ) ^ p + (115199347/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (12407121/12500000 : ℝ)) (y := (115199347/125000000 : ℝ)) (X := (10549281213333/12500000000000 : ℝ)) (Y := (15605766272143/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (239270557/125000000 : ℝ)) (τ := (115199347/125000000 : ℝ)) (σ := (12407121/12500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784506207/832337551 : ℝ) ^ p + (821385610/832337551 : ℝ) ^ p := by
    exact cert_lt (x := (784506207/832337551 : ℝ)) (y := (821385610/832337551 : ℝ)) (X := (26016829946591/100000000000000 : ℝ)) (Y := (73983170807913/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (115199347/125000000 : ℝ)) (n' := (832337551/1000000000 : ℝ)) (Ab := (784506207/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115232443/125000000 : ℝ) ^ p + (496258377/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115232443/125000000 : ℝ)) (y := (496258377/500000000 : ℝ)) (X := (15708083658727/100000000000000 : ℝ)) (Y := (3371677282737/4000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496258377/500000000 : ℝ) ^ p + (115232443/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496258377/500000000 : ℝ)) (y := (115232443/125000000 : ℝ)) (X := (3371677282737/4000000000000 : ℝ)) (Y := (15708083658727/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (957188149/500000000 : ℝ)) (τ := (115232443/125000000 : ℝ)) (σ := (496258377/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (392395403/416325702 : ℝ) ^ p + (21069217/21350036 : ℝ) ^ p := by
    exact cert_lt (x := (392395403/416325702 : ℝ)) (y := (21069217/21350036 : ℝ)) (X := (13004185415567/50000000000000 : ℝ)) (Y := (7399163031677/10000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115232443/125000000 : ℝ)) (n' := (208162851/250000000 : ℝ)) (Ab := (392395403/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (46093579/50000000 : ℝ) ^ p + (992514339/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46093579/50000000 : ℝ)) (y := (992514339/1000000000 : ℝ)) (X := (15712750077327/100000000000000 : ℝ)) (Y := (42143633085397/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992514339/1000000000 : ℝ) ^ p + (46093579/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992514339/1000000000 : ℝ)) (y := (46093579/50000000 : ℝ)) (X := (42143633085397/50000000000000 : ℝ)) (Y := (15712750077327/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1914385919/1000000000 : ℝ)) (τ := (46093579/50000000 : ℝ)) (σ := (992514339/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261601247/277555223 : ℝ) ^ p + (24900416/25232293 : ℝ) ^ p := by
    exact cert_lt (x := (261601247/277555223 : ℝ)) (y := (24900416/25232293 : ℝ)) (X := (26007986288941/100000000000000 : ℝ)) (Y := (73992014682169/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (46093579/50000000 : ℝ)) (n' := (832665669/1000000000 : ℝ)) (Ab := (784803741/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921872127/1000000000 : ℝ) ^ p + (992514229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921872127/1000000000 : ℝ)) (y := (992514229/1000000000 : ℝ)) (X := (15712962183499/100000000000000 : ℝ)) (Y := (21071763412829/25000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992514229/1000000000 : ℝ) ^ p + (921872127/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992514229/1000000000 : ℝ)) (y := (921872127/1000000000 : ℝ)) (X := (21071763412829/25000000000000 : ℝ)) (Y := (15712962183499/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (478596589/250000000 : ℝ)) (τ := (921872127/1000000000 : ℝ)) (σ := (992514229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (392402165/416333159 : ℝ) ^ p + (74701307/75696938 : ℝ) ^ p := by
    exact cert_lt (x := (392402165/416333159 : ℝ)) (y := (74701307/75696938 : ℝ)) (X := (6501992294623/25000000000000 : ℝ)) (Y := (36996016084489/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921872127/1000000000 : ℝ)) (n' := (416333159/500000000 : ℝ)) (Ab := (78480433/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (115234019/125000000 : ℝ) ^ p + (62032139/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (115234019/125000000 : ℝ)) (y := (62032139/62500000 : ℝ)) (X := (1571297187763/10000000000000 : ℝ)) (Y := (10535880498919/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (62032139/62500000 : ℝ) ^ p + (115234019/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (62032139/62500000 : ℝ)) (y := (115234019/125000000 : ℝ)) (X := (10535880498919/12500000000000 : ℝ)) (Y := (1571297187763/10000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (239298297/125000000 : ℝ)) (τ := (115234019/125000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (87200484/92518483 : ℝ) ^ p + (273904802/277555449 : ℝ) ^ p := by
    exact cert_lt (x := (87200484/92518483 : ℝ)) (y := (273904802/277555449 : ℝ)) (X := (13003984086731/50000000000000 : ℝ)) (Y := (1849800823759/2500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (115234019/125000000 : ℝ)) (n' := (832666347/1000000000 : ℝ)) (Ab := (196201089/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (921872153/1000000000 : ℝ) ^ p + (62032139/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (921872153/1000000000 : ℝ)) (y := (62032139/62500000 : ℝ)) (X := (3928243066349/25000000000000 : ℝ)) (Y := (10535880498919/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (62032139/62500000 : ℝ) ^ p + (921872153/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62032139/62500000 : ℝ)) (y := (921872153/1000000000 : ℝ)) (X := (10535880498919/12500000000000 : ℝ)) (Y := (3928243066349/25000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (784804357/832666348 : ℝ) ^ p + (821714407/832666348 : ℝ) ^ p := by
    exact cert_lt (x := (784804357/832666348 : ℝ)) (y := (821714407/832666348 : ℝ)) (X := (13003984108399/50000000000000 : ℝ)) (Y := (9249004122163/12500000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (n' := (208166587/250000000 : ℝ)) (Ab := (784804357/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914386377/1000000000 : ℝ)) (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1651470866/1806927101 : ℝ) ^ p + (256567880/258132443 : ℝ) ^ p := by
    exact cert_lt (x := (1651470866/1806927101 : ℝ)) (y := (256567880/258132443 : ℝ)) (X := (1614633635993/12500000000000 : ℝ)) (Y := (43541465604793/50000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108890709/1193072899 : ℝ) ^ p + (1182120958/1193072899 : ℝ) ^ p := by
    exact cert_lt (x := (1108890709/1193072899 : ℝ)) (y := (1182120958/1193072899 : ℝ)) (X := (18925402773153/100000000000000 : ℝ)) (Y := (81074597765303/100000000000000 : ℝ)) 91 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (62032139/62500000 : ℝ)) (U := (1193072899/1000000000 : ℝ)) (Ab := (825735433/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921872153/1000000000 : ℝ)) (σ := (62032139/62500000 : ℝ)) (Ab := (1108890709/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab055
