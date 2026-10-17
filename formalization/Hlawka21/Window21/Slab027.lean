import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 27, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab027 (p : ℝ) (hpa : (699/32 : ℝ) ≤ p) (hpb : p ≤ (175/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (529799858411/23853375000000 : ℝ) (1146339/100000000 : ℝ) (4000000572481/19082700000000 : ℝ) (3033/2500 : ℝ) (242202509/125000000 : ℝ) (484383059/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192723247/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11057/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4467/10000 : ℝ)
      else (3809/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2959/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (529799858411/23853375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1146339/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (912278101/1000000000 : ℝ) ^ p + (198686733/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (912278101/1000000000 : ℝ)) (y := (198686733/200000000 : ℝ)) (X := (13420960270309/100000000000000 : ℝ)) (Y := (17315811286197/20000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198686733/200000000 : ℝ) ^ p + (912278101/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198686733/200000000 : ℝ)) (y := (912278101/1000000000 : ℝ)) (X := (17315811286197/20000000000000 : ℝ)) (Y := (13420960270309/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (952855883/500000000 : ℝ)) (τ := (912278101/1000000000 : ℝ)) (σ := (198686733/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (773627720/822124747 : ℝ) ^ p + (810661357/822124747 : ℝ) ^ p := by
    exact cert_lt (x := (773627720/822124747 : ℝ)) (y := (810661357/822124747 : ℝ)) (X := (26446934743547/100000000000000 : ℝ)) (Y := (73553066590243/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (912278101/1000000000 : ℝ)) (n' := (822124747/1000000000 : ℝ)) (Ab := (19340693/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (918156343/1000000000 : ℝ) ^ p + (992359691/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918156343/1000000000 : ℝ)) (y := (992359691/1000000000 : ℝ)) (X := (15445482325559/100000000000000 : ℝ)) (Y := (84554532957633/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992359691/1000000000 : ℝ) ^ p + (918156343/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992359691/1000000000 : ℝ)) (y := (918156343/1000000000 : ℝ)) (X := (84554532957633/100000000000000 : ℝ)) (Y := (15445482325559/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (955258017/500000000 : ℝ)) (τ := (918156343/1000000000 : ℝ)) (σ := (992359691/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (779978413/829151200 : ℝ) ^ p + (81768781/82915120 : ℝ) ^ p := by
    exact cert_lt (x := (779978413/829151200 : ℝ)) (y := (81768781/82915120 : ℝ)) (X := (5250777060311/20000000000000 : ℝ)) (Y := (4609132240669/6250000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (918156343/1000000000 : ℝ)) (n' := (1036439/1250000 : ℝ)) (Ab := (779978413/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (229610469/250000000 : ℝ) ^ p + (992303101/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229610469/250000000 : ℝ)) (y := (992303101/1000000000 : ℝ)) (X := (485965519343/3125000000000 : ℝ)) (Y := (42224559628283/50000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992303101/1000000000 : ℝ) ^ p + (229610469/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992303101/1000000000 : ℝ)) (y := (229610469/250000000 : ℝ)) (X := (42224559628283/50000000000000 : ℝ)) (Y := (485965519343/3125000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1910744977/1000000000 : ℝ)) (τ := (229610469/250000000 : ℝ)) (σ := (992303101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (780285820/829491387 : ℝ) ^ p + (272675999/276497129 : ℝ) ^ p := by
    exact cert_lt (x := (780285820/829491387 : ℝ)) (y := (272675999/276497129 : ℝ)) (X := (26244609357387/100000000000000 : ℝ)) (Y := (73755391507101/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (229610469/250000000 : ℝ)) (n' := (829491387/1000000000 : ℝ)) (Ab := (39014291/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (918455591/1000000000 : ℝ) ^ p + (248075093/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (918455591/1000000000 : ℝ)) (y := (248075093/250000000 : ℝ)) (X := (7777988611351/50000000000000 : ℝ)) (Y := (84444038950153/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248075093/250000000 : ℝ) ^ p + (918455591/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248075093/250000000 : ℝ)) (y := (918455591/1000000000 : ℝ)) (X := (84444038950153/100000000000000 : ℝ)) (Y := (7777988611351/50000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1910755963/1000000000 : ℝ)) (τ := (918455591/1000000000 : ℝ)) (σ := (248075093/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (780300584/829507725 : ℝ) ^ p + (18178763/18433505 : ℝ) ^ p := by
    exact cert_lt (x := (780300584/829507725 : ℝ)) (y := (18178763/18433505 : ℝ)) (X := (205032534093/781250000000 : ℝ)) (Y := (73755836821197/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (918455591/1000000000 : ℝ)) (n' := (33180309/40000000 : ℝ)) (Ab := (97537573/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (918456249/1000000000 : ℝ) ^ p + (992300241/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918456249/1000000000 : ℝ)) (y := (992300241/1000000000 : ℝ)) (X := (3111244202591/20000000000000 : ℝ)) (Y := (84443795087889/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992300241/1000000000 : ℝ) ^ p + (918456249/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992300241/1000000000 : ℝ)) (y := (918456249/1000000000 : ℝ)) (X := (84443795087889/100000000000000 : ℝ)) (Y := (3111244202591/20000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (191075649/100000000 : ℝ)) (τ := (918456249/1000000000 : ℝ)) (σ := (992300241/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (780301292/829508509 : ℝ) ^ p + (818045119/829508509 : ℝ) ^ p := by
    exact cert_lt (x := (780301292/829508509 : ℝ)) (y := (818045119/829508509 : ℝ)) (X := (5248828533091/20000000000000 : ℝ)) (Y := (2304870568431/3125000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (918456249/1000000000 : ℝ)) (n' := (829508509/1000000000 : ℝ)) (Ab := (195075323/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (459228141/500000000 : ℝ) ^ p + (496150117/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (459228141/500000000 : ℝ)) (y := (496150117/500000000 : ℝ)) (X := (7778116619807/50000000000000 : ℝ)) (Y := (844437820571/1000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496150117/500000000 : ℝ) ^ p + (459228141/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496150117/500000000 : ℝ)) (y := (459228141/500000000 : ℝ)) (X := (844437820571/1000000000000 : ℝ)) (Y := (7778116619807/50000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477689129/250000000 : ℝ)) (τ := (459228141/500000000 : ℝ)) (σ := (496150117/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (195075332/207377137 : ℝ) ^ p + (409022579/414754274 : ℝ) ^ p := by
    exact cert_lt (x := (195075332/207377137 : ℝ)) (y := (409022579/414754274 : ℝ)) (X := (26244142160389/100000000000000 : ℝ)) (Y := (7375585925277/10000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (459228141/500000000 : ℝ)) (n' := (207377137/250000000 : ℝ)) (Ab := (48768833/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (918456283/1000000000 : ℝ) ^ p + (496150117/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (918456283/1000000000 : ℝ)) (y := (496150117/500000000 : ℝ)) (X := (15556233610119/100000000000000 : ℝ)) (Y := (844437820571/1000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496150117/500000000 : ℝ) ^ p + (918456283/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496150117/500000000 : ℝ)) (y := (918456283/1000000000 : ℝ)) (X := (844437820571/1000000000000 : ℝ)) (Y := (15556233610119/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1910756517/1000000000 : ℝ)) (τ := (918456283/1000000000 : ℝ)) (σ := (496150117/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (780301328/829508549 : ℝ) ^ p + (818045159/829508549 : ℝ) ^ p := by
    exact cert_lt (x := (780301328/829508549 : ℝ)) (y := (818045159/829508549 : ℝ)) (X := (1640258841769/6250000000000 : ℝ)) (Y := (2950234371201/4000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (918456283/1000000000 : ℝ)) (n' := (829508549/1000000000 : ℝ)) (Ab := (48768833/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1910756517/1000000000 : ℝ)) (τ := (918456283/1000000000 : ℝ)) (σ := (496150117/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (918456283/1000000000 : ℝ)) (n' := (829508549/1000000000 : ℝ)) (Ab := (48768833/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1910756517/1000000000 : ℝ)) (τ := (918456283/1000000000 : ℝ)) (σ := (496150117/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (918456283/1000000000 : ℝ)) (n' := (829508549/1000000000 : ℝ)) (Ab := (48768833/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1910756517/1000000000 : ℝ)) (τ := (918456283/1000000000 : ℝ)) (σ := (496150117/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (918456283/1000000000 : ℝ)) (n' := (829508549/1000000000 : ℝ)) (Ab := (48768833/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1910756517/1000000000 : ℝ)) (τ := (918456283/1000000000 : ℝ)) (σ := (496150117/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1646304025/1807276753 : ℝ) ^ p + (1795813363/1807276753 : ℝ) ^ p := by
    exact cert_lt (x := (1646304025/1807276753 : ℝ)) (y := (1795813363/1807276753 : ℝ)) (X := (1624249156139/12500000000000 : ℝ)) (Y := (870060070813/1000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1105640547/1192723247 : ℝ) ^ p + (1181259857/1192723247 : ℝ) ^ p := by
    exact cert_lt (x := (1105640547/1192723247 : ℝ)) (y := (1181259857/1192723247 : ℝ)) (X := (19043629529197/100000000000000 : ℝ)) (Y := (80956370986083/100000000000000 : ℝ)) 175 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496150117/500000000 : ℝ)) (U := (1192723247/1000000000 : ℝ)) (Ab := (65852161/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (918456283/1000000000 : ℝ)) (σ := (496150117/500000000 : ℝ)) (Ab := (1105640547/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab027
