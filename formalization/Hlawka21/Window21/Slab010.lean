import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 10, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab010 (p : ℝ) (hpa : (341/16 : ℝ) ≤ p) (hpb : p ≤ (683/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1063115846803/46546500000000 : ℝ) (235949/20000000 : ℝ) (2000000279279/9309300000000 : ℝ) (3033/2500 : ℝ) (121005781/62500000 : ℝ) (968000151/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192515551/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2759/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(1107/2500 : ℝ)
      else (7581/10000 : ℝ) ≤ X j i ∧ X j i ≤ (1479/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1063115846803/46546500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (235949/20000000 : ℝ) := by norm_num
  have pc0 : 1 < (181993897/200000000 : ℝ) ^ p + (198661789/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (181993897/200000000 : ℝ)) (y := (198661789/200000000 : ℝ)) (X := (13349926640777/100000000000000 : ℝ)) (Y := (86650090160523/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198661789/200000000 : ℝ) ^ p + (181993897/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198661789/200000000 : ℝ)) (y := (181993897/200000000 : ℝ)) (X := (86650090160523/100000000000000 : ℝ)) (Y := (13349926640777/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (190327843/100000000 : ℝ)) (τ := (181993897/200000000 : ℝ)) (σ := (198661789/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (770604824/819921397 : ℝ) ^ p + (808123947/819921397 : ℝ) ^ p := by
    exact cert_lt (x := (770604824/819921397 : ℝ)) (y := (808123947/819921397 : ℝ)) (X := (5321312560749/20000000000000 : ℝ)) (Y := (7339343848627/10000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (181993897/200000000 : ℝ)) (n' := (819921397/1000000000 : ℝ)) (Ab := (96325603/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (915916639/1000000000 : ℝ) ^ p + (992227497/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915916639/1000000000 : ℝ)) (y := (992227497/1000000000 : ℝ)) (X := (7670663112761/50000000000000 : ℝ)) (Y := (1058233621089/1250000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992227497/1000000000 : ℝ) ^ p + (915916639/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992227497/1000000000 : ℝ)) (y := (915916639/1000000000 : ℝ)) (X := (1058233621089/1250000000000 : ℝ)) (Y := (7670663112761/50000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (238518017/125000000 : ℝ)) (τ := (915916639/1000000000 : ℝ)) (σ := (992227497/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (388518593/413527016 : ℝ) ^ p + (58232613/59075288 : ℝ) ^ p := by
    exact cert_lt (x := (388518593/413527016 : ℝ)) (y := (58232613/59075288 : ℝ)) (X := (26409088478653/100000000000000 : ℝ)) (Y := (73590912756231/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (915916639/1000000000 : ℝ)) (n' := (51690877/62500000 : ℝ)) (Ab := (388518593/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (916215843/1000000000 : ℝ) ^ p + (62010533/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (916215843/1000000000 : ℝ)) (y := (62010533/62500000 : ℝ)) (X := (7724324120493/50000000000000 : ℝ)) (Y := (16910273364687/20000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (62010533/62500000 : ℝ) ^ p + (916215843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62010533/62500000 : ℝ)) (y := (916215843/1000000000 : ℝ)) (X := (16910273364687/20000000000000 : ℝ)) (Y := (7724324120493/50000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1908384371/1000000000 : ℝ)) (τ := (916215843/1000000000 : ℝ)) (σ := (62010533/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (777359654/827411683 : ℝ) ^ p + (116516319/118201669 : ℝ) ^ p := by
    exact cert_lt (x := (777359654/827411683 : ℝ)) (y := (116516319/118201669 : ℝ)) (X := (26399262487309/100000000000000 : ℝ)) (Y := (14720147649047/20000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (916215843/1000000000 : ℝ)) (n' := (827411683/1000000000 : ℝ)) (Ab := (388679827/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (36649229/40000000 : ℝ) ^ p + (992165583/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (36649229/40000000 : ℝ)) (y := (992165583/1000000000 : ℝ)) (X := (15454004930433/100000000000000 : ℝ)) (Y := (42273005180289/50000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992165583/1000000000 : ℝ) ^ p + (36649229/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (992165583/1000000000 : ℝ)) (y := (36649229/40000000 : ℝ)) (X := (42273005180289/50000000000000 : ℝ)) (Y := (15454004930433/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (477099077/250000000 : ℝ)) (τ := (36649229/40000000 : ℝ)) (σ := (992165583/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (777375691/827429469 : ℝ) ^ p + (815632019/827429469 : ℝ) ^ p := by
    exact cert_lt (x := (777375691/827429469 : ℝ)) (y := (815632019/827429469 : ℝ)) (X := (5279754925129/20000000000000 : ℝ)) (Y := (73601226678149/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (36649229/40000000 : ℝ)) (n' := (827429469/1000000000 : ℝ)) (Ab := (777375691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (458115733/500000000 : ℝ) ^ p + (248041359/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (458115733/500000000 : ℝ)) (y := (248041359/250000000 : ℝ)) (X := (15454271695343/100000000000000 : ℝ)) (Y := (84545743000619/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248041359/250000000 : ℝ) ^ p + (458115733/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248041359/250000000 : ℝ)) (y := (458115733/500000000 : ℝ)) (X := (84545743000619/100000000000000 : ℝ)) (Y := (15454271695343/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (954198451/500000000 : ℝ)) (τ := (458115733/500000000 : ℝ)) (σ := (248041359/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (155475298/165486071 : ℝ) ^ p + (163126581/165486071 : ℝ) ^ p := by
    exact cert_lt (x := (155475298/165486071 : ℝ)) (y := (163126581/165486071 : ℝ)) (X := (2639875041481/10000000000000 : ℝ)) (Y := (73601251008703/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (458115733/500000000 : ℝ)) (n' := (165486071/200000000 : ℝ)) (Ab := (77737649/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (458115751/500000000 : ℝ) ^ p + (992165429/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458115751/500000000 : ℝ)) (y := (992165429/1000000000 : ℝ)) (X := (15454284655693/100000000000000 : ℝ)) (Y := (84545730269213/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992165429/1000000000 : ℝ) ^ p + (458115751/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992165429/1000000000 : ℝ)) (y := (458115751/500000000 : ℝ)) (X := (84545730269213/100000000000000 : ℝ)) (Y := (15454284655693/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1908396931/1000000000 : ℝ)) (τ := (458115751/500000000 : ℝ)) (σ := (992165429/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (388688264/413715199 : ℝ) ^ p + (407816474/413715199 : ℝ) ^ p := by
    exact cert_lt (x := (388688264/413715199 : ℝ)) (y := (407816474/413715199 : ℝ)) (X := (13199374338073/50000000000000 : ℝ)) (Y := (7360125218953/10000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (458115751/500000000 : ℝ)) (n' := (413715199/500000000 : ℝ)) (Ab := (48586033/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (57264469/62500000 : ℝ) ^ p + (992165429/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57264469/62500000 : ℝ)) (y := (992165429/1000000000 : ℝ)) (X := (15454285375713/100000000000000 : ℝ)) (Y := (84545730269213/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992165429/1000000000 : ℝ) ^ p + (57264469/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992165429/1000000000 : ℝ)) (y := (57264469/62500000 : ℝ)) (X := (84545730269213/100000000000000 : ℝ)) (Y := (15454285375713/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1908396933/1000000000 : ℝ)) (τ := (57264469/62500000 : ℝ)) (σ := (992165429/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (77737653/82743040 : ℝ) ^ p + (16312659/16548608 : ℝ) ^ p := by
    exact cert_lt (x := (77737653/82743040 : ℝ)) (y := (16312659/16548608 : ℝ)) (X := (13199374381919/50000000000000 : ℝ)) (Y := (73601252244453/100000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (57264469/62500000 : ℝ)) (n' := (64643/78125 : ℝ)) (Ab := (77737653/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1908396933/1000000000 : ℝ)) (τ := (57264469/62500000 : ℝ)) (σ := (992165429/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (57264469/62500000 : ℝ)) (n' := (64643/78125 : ℝ)) (Ab := (77737653/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1908396933/1000000000 : ℝ)) (τ := (57264469/62500000 : ℝ)) (σ := (992165429/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (57264469/62500000 : ℝ)) (n' := (64643/78125 : ℝ)) (Ab := (77737653/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1908396933/1000000000 : ℝ)) (τ := (57264469/62500000 : ℝ)) (σ := (992165429/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (57264469/62500000 : ℝ)) (n' := (64643/78125 : ℝ)) (Ab := (77737653/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1908396933/1000000000 : ℝ)) (τ := (57264469/62500000 : ℝ)) (σ := (992165429/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1642969860/1807484449 : ℝ) ^ p + (1795686999/1807484449 : ℝ) ^ p := by
    exact cert_lt (x := (1642969860/1807484449 : ℝ)) (y := (1795686999/1807484449 : ℝ)) (X := (6521970975441/50000000000000 : ℝ)) (Y := (17391211646187/20000000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1103570796/1192515551 : ℝ) ^ p + (1180718101/1192515551 : ℝ) ^ p := by
    exact cert_lt (x := (1103570796/1192515551 : ℝ)) (y := (1180718101/1192515551 : ℝ)) (X := (4779991970169/25000000000000 : ℝ)) (Y := (5055002036687/6250000000000 : ℝ)) 683 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992165429/1000000000 : ℝ)) (U := (1192515551/1000000000 : ℝ)) (Ab := (82148493/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (57264469/62500000 : ℝ)) (σ := (992165429/1000000000 : ℝ)) (Ab := (275892699/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab010
