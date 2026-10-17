import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 2, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab002 (p : ℝ) (hpa : (337/16 : ℝ) ≤ p) (hpb : p ≤ (675/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (133103903957/5750062500000 : ℝ) (5980679/500000000 : ℝ) (2000000276003/9200100000000 : ℝ) (3033/2500 : ℝ) (241918431/125000000 : ℝ) (483813273/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238483899/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5513/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4409/10000 : ℝ)
      else (3781/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11831/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (133103903957/5750062500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5980679/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (227210171/250000000 : ℝ) ^ p + (993248721/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (227210171/250000000 : ℝ)) (y := (993248721/1000000000 : ℝ)) (X := (2663061404751/20000000000000 : ℝ)) (Y := (43342354254299/50000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993248721/1000000000 : ℝ) ^ p + (227210171/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993248721/1000000000 : ℝ)) (y := (227210171/250000000 : ℝ)) (X := (43342354254299/50000000000000 : ℝ)) (Y := (2663061404751/20000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (380417881/200000000 : ℝ)) (τ := (227210171/250000000 : ℝ)) (σ := (993248721/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (256376141/272946059 : ℝ) ^ p + (806876819/818838177 : ℝ) ^ p := by
    exact cert_lt (x := (256376141/272946059 : ℝ)) (y := (806876819/818838177 : ℝ)) (X := (5336990264101/20000000000000 : ℝ)) (Y := (1832876241217/2500000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (227210171/250000000 : ℝ)) (n' := (818838177/1000000000 : ℝ)) (Ab := (769128423/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (457409709/500000000 : ℝ) ^ p + (496082021/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (457409709/500000000 : ℝ)) (y := (496082021/500000000 : ℝ)) (X := (1529037206981/10000000000000 : ℝ)) (Y := (84709642837533/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496082021/500000000 : ℝ) ^ p + (457409709/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496082021/500000000 : ℝ)) (y := (457409709/500000000 : ℝ)) (X := (84709642837533/100000000000000 : ℝ)) (Y := (1529037206981/10000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (95349173/50000000 : ℝ)) (τ := (457409709/500000000 : ℝ)) (σ := (496082021/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (775598548/826020425 : ℝ) ^ p + (814059067/826020425 : ℝ) ^ p := by
    exact cert_lt (x := (775598548/826020425 : ℝ)) (y := (814059067/826020425 : ℝ)) (X := (26485355385717/100000000000000 : ℝ)) (Y := (73514645864151/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (457409709/500000000 : ℝ)) (n' := (33040817/40000000 : ℝ)) (Ab := (193899637/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (114390669/125000000 : ℝ) ^ p + (992103913/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114390669/125000000 : ℝ)) (y := (992103913/1000000000 : ℝ)) (X := (12318876949/80000000000 : ℝ)) (Y := (10575177381173/12500000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992103913/1000000000 : ℝ) ^ p + (114390669/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992103913/1000000000 : ℝ)) (y := (114390669/125000000 : ℝ)) (X := (10575177381173/12500000000000 : ℝ)) (Y := (12318876949/80000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (381445853/200000000 : ℝ)) (τ := (114390669/125000000 : ℝ)) (σ := (992103913/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (258642815/275462237 : ℝ) ^ p + (814425353/826386711 : ℝ) ^ p := by
    exact cert_lt (x := (258642815/275462237 : ℝ)) (y := (814425353/826386711 : ℝ)) (X := (13237627767423/50000000000000 : ℝ)) (Y := (36762372888741/50000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (114390669/125000000 : ℝ)) (n' := (826386711/1000000000 : ℝ)) (Ab := (155185689/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (915140827/1000000000 : ℝ) ^ p + (992100859/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915140827/1000000000 : ℝ)) (y := (992100859/1000000000 : ℝ)) (X := (481377806511/3125000000000 : ℝ)) (Y := (21148981448213/25000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992100859/1000000000 : ℝ) ^ p + (915140827/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992100859/1000000000 : ℝ)) (y := (915140827/1000000000 : ℝ)) (X := (21148981448213/25000000000000 : ℝ)) (Y := (481377806511/3125000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (953620843/500000000 : ℝ)) (τ := (915140827/1000000000 : ℝ)) (σ := (992100859/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (775945129/826405236 : ℝ) ^ p + (407221939/413202618 : ℝ) ^ p := by
    exact cert_lt (x := (775945129/826405236 : ℝ)) (y := (407221939/413202618 : ℝ)) (X := (13237372311581/50000000000000 : ℝ)) (Y := (73525256380201/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (915140827/1000000000 : ℝ)) (n' := (206601309/250000000 : ℝ)) (Ab := (775945129/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (91514161/100000000 : ℝ) ^ p + (31003147/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (91514161/100000000 : ℝ)) (y := (31003147/31250000 : ℝ)) (X := (15404367822823/100000000000000 : ℝ)) (Y := (16919129400411/20000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (31003147/31250000 : ℝ) ^ p + (91514161/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (31003147/31250000 : ℝ)) (y := (91514161/100000000 : ℝ)) (X := (16919129400411/20000000000000 : ℝ)) (Y := (15404367822823/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (953621157/500000000 : ℝ)) (τ := (91514161/100000000 : ℝ)) (σ := (31003147/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (775945973/826406173 : ℝ) ^ p + (814444815/826406173 : ℝ) ^ p := by
    exact cert_lt (x := (775945973/826406173 : ℝ)) (y := (814444815/826406173 : ℝ)) (X := (6618679716779/25000000000000 : ℝ)) (Y := (73525282206119/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (91514161/100000000 : ℝ)) (n' := (826406173/1000000000 : ℝ)) (Ab := (775945973/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (57196353/62500000 : ℝ) ^ p + (992100697/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57196353/62500000 : ℝ)) (y := (992100697/1000000000 : ℝ)) (X := (3080876263069/20000000000000 : ℝ)) (Y := (21148908602881/25000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992100697/1000000000 : ℝ) ^ p + (57196353/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992100697/1000000000 : ℝ)) (y := (57196353/62500000 : ℝ)) (X := (21148908602881/25000000000000 : ℝ)) (Y := (3080876263069/20000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (381448469/200000000 : ℝ)) (τ := (57196353/62500000 : ℝ)) (σ := (992100697/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (775946014/826406219 : ℝ) ^ p + (814444861/826406219 : ℝ) ^ p := by
    exact cert_lt (x := (775946014/826406219 : ℝ)) (y := (814444861/826406219 : ℝ)) (X := (13237358645033/50000000000000 : ℝ)) (Y := (36762641736993/50000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (57196353/62500000 : ℝ)) (n' := (826406219/1000000000 : ℝ)) (Ab := (387973007/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (915141651/1000000000 : ℝ) ^ p + (124012587/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (915141651/1000000000 : ℝ)) (y := (124012587/125000000 : ℝ)) (X := (3080876476109/20000000000000 : ℝ)) (Y := (84595632612877/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124012587/125000000 : ℝ) ^ p + (915141651/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124012587/125000000 : ℝ)) (y := (915141651/1000000000 : ℝ)) (X := (84595632612877/100000000000000 : ℝ)) (Y := (3080876476109/20000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1907242347/1000000000 : ℝ)) (τ := (915141651/1000000000 : ℝ)) (σ := (124012587/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (775946017/826406222 : ℝ) ^ p + (407222432/413203111 : ℝ) ^ p := by
    exact cert_lt (x := (775946017/826406222 : ℝ)) (y := (407222432/413203111 : ℝ)) (X := (26474717421901/100000000000000 : ℝ)) (Y := (73525283556673/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (915141651/1000000000 : ℝ)) (n' := (413203111/500000000 : ℝ)) (Ab := (775946017/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1907242347/1000000000 : ℝ)) (τ := (915141651/1000000000 : ℝ)) (σ := (124012587/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (915141651/1000000000 : ℝ)) (n' := (413203111/500000000 : ℝ)) (Ab := (775946017/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1907242347/1000000000 : ℝ)) (τ := (915141651/1000000000 : ℝ)) (σ := (124012587/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (915141651/1000000000 : ℝ)) (n' := (413203111/500000000 : ℝ)) (Ab := (775946017/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1907242347/1000000000 : ℝ)) (τ := (915141651/1000000000 : ℝ)) (σ := (124012587/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (915141651/1000000000 : ℝ)) (n' := (413203111/500000000 : ℝ)) (Ab := (775946017/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1907242347/1000000000 : ℝ)) (τ := (915141651/1000000000 : ℝ)) (σ := (124012587/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1641345442/1807580505 : ℝ) ^ p + (1795619147/1807580505 : ℝ) ^ p := by
    exact cert_lt (x := (1641345442/1807580505 : ℝ)) (y := (1795619147/1807580505 : ℝ)) (X := (13068367340077/100000000000000 : ℝ)) (Y := (43465816440511/50000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1102570231/1192419495 : ℝ) ^ p + (1180458137/1192419495 : ℝ) ^ p := by
    exact cert_lt (x := (1102570231/1192419495 : ℝ)) (y := (1180458137/1192419495 : ℝ)) (X := (4789293589267/25000000000000 : ℝ)) (Y := (80842826291477/100000000000000 : ℝ)) 675 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124012587/125000000 : ℝ)) (U := (238483899/200000000 : ℝ)) (Ab := (820672721/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (915141651/1000000000 : ℝ)) (σ := (124012587/125000000 : ℝ)) (Ab := (1102570231/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab002
