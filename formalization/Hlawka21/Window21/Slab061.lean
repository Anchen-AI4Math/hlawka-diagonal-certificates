import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 61, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab061 (p : ℝ) (hpa : (733/32 : ℝ) ≤ p) (hpb : p ≤ (367/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (526525884617/25013625000000 : ℝ) (2712033/250000000 : ℝ) (4000000600327/20010900000000 : ℝ) (3033/2500 : ℝ) (485116539/250000000 : ℝ) (485096539/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193148647/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1387/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(4537/10000 : ℝ)
      else (7687/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11843/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (526525884617/25013625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2712033/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (916558683/1000000000 : ℝ) ^ p + (198734101/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (916558683/1000000000 : ℝ)) (y := (198734101/200000000 : ℝ)) (X := (6776747999027/50000000000000 : ℝ)) (Y := (86446521959411/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198734101/200000000 : ℝ) ^ p + (916558683/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198734101/200000000 : ℝ)) (y := (916558683/1000000000 : ℝ)) (X := (86446521959411/100000000000000 : ℝ)) (Y := (6776747999027/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (477557297/250000000 : ℝ)) (τ := (916558683/1000000000 : ℝ)) (σ := (198734101/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (779245099/826167251 : ℝ) ^ p + (815319119/826167251 : ℝ) ^ p := by
    exact cert_lt (x := (779245099/826167251 : ℝ)) (y := (815319119/826167251 : ℝ)) (X := (13076680426681/50000000000000 : ℝ)) (Y := (73846640201579/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (916558683/1000000000 : ℝ)) (n' := (826167251/1000000000 : ℝ)) (Ab := (779245099/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (922294137/1000000000 : ℝ) ^ p + (198522689/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (922294137/1000000000 : ℝ)) (y := (198522689/200000000 : ℝ)) (X := (7819211570693/50000000000000 : ℝ)) (Y := (21090398135971/25000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198522689/200000000 : ℝ) ^ p + (922294137/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198522689/200000000 : ℝ)) (y := (922294137/1000000000 : ℝ)) (X := (21090398135971/25000000000000 : ℝ)) (Y := (7819211570693/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (957453791/500000000 : ℝ)) (τ := (922294137/1000000000 : ℝ)) (σ := (198522689/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (785429024/832980689 : ℝ) ^ p + (1476001/1495477 : ℝ) ^ p := by
    exact cert_lt (x := (785429024/832980689 : ℝ)) (y := (1476001/1495477 : ℝ)) (X := (1623049642457/6250000000000 : ℝ)) (Y := (74031207203861/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (922294137/1000000000 : ℝ)) (n' := (832980689/1000000000 : ℝ)) (Ab := (24544657/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (5765967/6250000 : ℝ) ^ p + (496280633/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (5765967/6250000 : ℝ)) (y := (496280633/500000000 : ℝ)) (X := (7870042981363/50000000000000 : ℝ)) (Y := (84259931150949/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496280633/500000000 : ℝ) ^ p + (5765967/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (496280633/500000000 : ℝ)) (y := (5765967/6250000 : ℝ)) (X := (84259931150949/100000000000000 : ℝ)) (Y := (7870042981363/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (957557993/500000000 : ℝ)) (τ := (5765967/6250000 : ℝ)) (σ := (496280633/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (785709035/833289263 : ℝ) ^ p + (822441131/833289263 : ℝ) ^ p := by
    exact cert_lt (x := (785709035/833289263 : ℝ)) (y := (822441131/833289263 : ℝ)) (X := (25960496030471/100000000000000 : ℝ)) (Y := (37019752481727/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (5765967/6250000 : ℝ)) (n' := (833289263/1000000000 : ℝ)) (Ab := (157141807/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (922566433/1000000000 : ℝ) ^ p + (992558911/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (922566433/1000000000 : ℝ)) (y := (992558911/1000000000 : ℝ)) (X := (15744670438389/100000000000000 : ℝ)) (Y := (42127672810853/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992558911/1000000000 : ℝ) ^ p + (922566433/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992558911/1000000000 : ℝ)) (y := (922566433/1000000000 : ℝ)) (X := (42127672810853/50000000000000 : ℝ)) (Y := (15744670438389/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (59847667/31250000 : ℝ)) (τ := (922566433/1000000000 : ℝ)) (σ := (992558911/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (785721619/833303131 : ℝ) ^ p + (822454999/833303131 : ℝ) ^ p := by
    exact cert_lt (x := (785721619/833303131 : ℝ)) (y := (822454999/833303131 : ℝ)) (X := (6490030763389/25000000000000 : ℝ)) (Y := (37019938879877/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (922566433/1000000000 : ℝ)) (n' := (833303131/1000000000 : ℝ)) (Ab := (785721619/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (922566959/1000000000 : ℝ) ^ p + (198511761/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (922566959/1000000000 : ℝ)) (y := (198511761/200000000 : ℝ)) (X := (3936219086271/25000000000000 : ℝ)) (Y := (3370205569193/4000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198511761/200000000 : ℝ) ^ p + (922566959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198511761/200000000 : ℝ)) (y := (922566959/1000000000 : ℝ)) (X := (3370205569193/4000000000000 : ℝ)) (Y := (3936219086271/25000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (478781441/250000000 : ℝ)) (τ := (922566959/1000000000 : ℝ)) (σ := (198511761/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (87302465/92589306 : ℝ) ^ p + (45691979/46294653 : ℝ) ^ p := by
    exact cert_lt (x := (87302465/92589306 : ℝ)) (y := (45691979/46294653 : ℝ)) (X := (25960106815261/100000000000000 : ℝ)) (Y := (74039894506843/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (922566959/1000000000 : ℝ)) (n' := (416651877/500000000 : ℝ)) (Ab := (157144437/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (461283491/500000000 : ℝ) ^ p + (992558801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461283491/500000000 : ℝ)) (y := (992558801/1000000000 : ℝ)) (X := (15744885348667/100000000000000 : ℝ)) (Y := (84255131441461/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992558801/1000000000 : ℝ) ^ p + (461283491/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992558801/1000000000 : ℝ)) (y := (461283491/500000000 : ℝ)) (X := (84255131441461/100000000000000 : ℝ)) (Y := (15744885348667/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1915125783/1000000000 : ℝ)) (τ := (461283491/500000000 : ℝ)) (σ := (992558801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (261907403/277767927 : ℝ) ^ p + (91383961/92589309 : ℝ) ^ p := by
    exact cert_lt (x := (261907403/277767927 : ℝ)) (y := (91383961/92589309 : ℝ)) (X := (12980052855043/50000000000000 : ℝ)) (Y := (115687336301/156250000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (461283491/500000000 : ℝ)) (n' := (833303781/1000000000 : ℝ)) (Ab := (785722209/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (115320873/125000000 : ℝ) ^ p + (2481397/2500000 : ℝ) ^ p := by
    exact cert_lt (x := (115320873/125000000 : ℝ)) (y := (2481397/2500000 : ℝ)) (X := (3936221532897/25000000000000 : ℝ)) (Y := (84255129494371/100000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (2481397/2500000 : ℝ) ^ p + (115320873/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (2481397/2500000 : ℝ)) (y := (115320873/125000000 : ℝ)) (X := (84255129494371/100000000000000 : ℝ)) (Y := (3936221532897/25000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (785722211/833303783 : ℝ) ^ p + (822455651/833303783 : ℝ) ^ p := by
    exact cert_lt (x := (785722211/833303783 : ℝ)) (y := (822455651/833303783 : ℝ)) (X := (3245013224579/12500000000000 : ℝ)) (Y := (37019947643201/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (n' := (833303783/1000000000 : ℝ)) (Ab := (785722211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (239390723/125000000 : ℝ)) (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1652528973/1806851353 : ℝ) ^ p + (1796003221/1806851353 : ℝ) ^ p := by
    exact cert_lt (x := (1652528973/1806851353 : ℝ)) (y := (1796003221/1806851353 : ℝ)) (X := (12901388412607/100000000000000 : ℝ)) (Y := (43549305968133/50000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1109562729/1193148647 : ℝ) ^ p + (1182300515/1193148647 : ℝ) ^ p := by
    exact cert_lt (x := (1109562729/1193148647 : ℝ)) (y := (1182300515/1193148647 : ℝ)) (X := (18901204378481/100000000000000 : ℝ)) (Y := (16219759223673/20000000000000 : ℝ)) 367 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (2481397/2500000 : ℝ)) (U := (1193148647/1000000000 : ℝ)) (Ab := (1652528973/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115320873/125000000 : ℝ)) (σ := (2481397/2500000 : ℝ)) (Ab := (1109562729/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab061
