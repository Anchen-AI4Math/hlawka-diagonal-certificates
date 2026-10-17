import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 48, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab048 (p : ℝ) (hpa : (45/2 : ℝ) ≤ p) (hpb : p ≤ (721/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527741573/24570000000 : ℝ) (221511/20000000 : ℝ) (50000007371/245700000000 : ℝ) (3033/2500 : ℝ) (969704577/500000000 : ℝ) (121207893/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192984831/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11081/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4511/10000 : ℝ)
      else (3831/5000 : ℝ) ≤ X j i ∧ X j i ≤ (148/125 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527741573/24570000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (221511/20000000 : ℝ) := by norm_num
  have pc0 : 1 < (228743017/250000000 : ℝ) ^ p + (198716373/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (228743017/250000000 : ℝ)) (y := (198716373/200000000 : ℝ)) (X := (1688030633069/12500000000000 : ℝ)) (Y := (21623942863013/25000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198716373/200000000 : ℝ) ^ p + (228743017/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198716373/200000000 : ℝ)) (y := (228743017/250000000 : ℝ)) (X := (21623942863013/25000000000000 : ℝ)) (Y := (1688030633069/12500000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908553933/1000000000 : ℝ)) (τ := (228743017/250000000 : ℝ)) (σ := (198716373/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (155432215/164935078 : ℝ) ^ p + (81359984/82467539 : ℝ) ^ p := by
    exact cert_lt (x := (155432215/164935078 : ℝ)) (y := (81359984/82467539 : ℝ)) (X := (26261816112969/100000000000000 : ℝ)) (Y := (2949527403023/4000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (228743017/250000000 : ℝ)) (n' := (82467539/100000000 : ℝ)) (Ab := (31086443/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (460381343/500000000 : ℝ) ^ p + (248129519/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (460381343/500000000 : ℝ)) (y := (248129519/250000000 : ℝ)) (X := (7783467587039/50000000000000 : ℝ)) (Y := (21108270296287/25000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248129519/250000000 : ℝ) ^ p + (460381343/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248129519/250000000 : ℝ)) (y := (460381343/500000000 : ℝ)) (X := (21108270296287/25000000000000 : ℝ)) (Y := (7783467587039/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956640381/500000000 : ℝ)) (τ := (460381343/500000000 : ℝ)) (σ := (248129519/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (783409095/831570167 : ℝ) ^ p + (820494617/831570167 : ℝ) ^ p := by
    exact cert_lt (x := (783409095/831570167 : ℝ)) (y := (820494617/831570167 : ℝ)) (X := (26074065433013/100000000000000 : ℝ)) (Y := (36962967831327/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (460381343/500000000 : ℝ)) (n' := (831570167/1000000000 : ℝ)) (Ab := (156681819/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (18420649/20000000 : ℝ) ^ p + (992464263/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18420649/20000000 : ℝ)) (y := (992464263/1000000000 : ℝ)) (X := (3917505020023/25000000000000 : ℝ)) (Y := (84329996718819/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992464263/1000000000 : ℝ) ^ p + (18420649/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (992464263/1000000000 : ℝ)) (y := (18420649/20000000 : ℝ)) (X := (84329996718819/100000000000000 : ℝ)) (Y := (3917505020023/25000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1913496713/1000000000 : ℝ)) (τ := (18420649/20000000 : ℝ)) (σ := (992464263/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (783699174/831890335 : ℝ) ^ p + (164162957/166378067 : ℝ) ^ p := by
    exact cert_lt (x := (783699174/831890335 : ℝ)) (y := (164162957/166378067 : ℝ)) (X := (26065411596623/100000000000000 : ℝ)) (Y := (73934589481841/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (18420649/20000000 : ℝ)) (n' := (166378067/200000000 : ℝ)) (Ab := (391849587/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921044881/1000000000 : ℝ) ^ p + (992461773/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921044881/1000000000 : ℝ)) (y := (992461773/1000000000 : ℝ)) (X := (15674786025673/100000000000000 : ℝ)) (Y := (84325229774169/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992461773/1000000000 : ℝ) ^ p + (921044881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992461773/1000000000 : ℝ)) (y := (921044881/1000000000 : ℝ)) (X := (84325229774169/100000000000000 : ℝ)) (Y := (15674786025673/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (956753327/500000000 : ℝ)) (τ := (921044881/1000000000 : ℝ)) (σ := (992461773/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (60285580/63992699 : ℝ) ^ p + (820829537/831905087 : ℝ) ^ p := by
    exact cert_lt (x := (60285580/63992699 : ℝ)) (y := (820829537/831905087 : ℝ)) (X := (26065013371799/100000000000000 : ℝ)) (Y := (73934988076363/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921044881/1000000000 : ℝ)) (n' := (831905087/1000000000 : ℝ)) (Ab := (39185627/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (460522727/500000000 : ℝ) ^ p + (496230829/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460522727/500000000 : ℝ)) (y := (496230829/500000000 : ℝ)) (X := (3135001148533/20000000000000 : ℝ)) (Y := (10540626202537/12500000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496230829/500000000 : ℝ) ^ p + (460522727/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496230829/500000000 : ℝ)) (y := (460522727/500000000 : ℝ)) (X := (10540626202537/12500000000000 : ℝ)) (Y := (3135001148533/20000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239188389/125000000 : ℝ)) (τ := (460522727/500000000 : ℝ)) (σ := (496230829/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (783713156/831905767 : ℝ) ^ p + (820830217/831905767 : ℝ) ^ p := by
    exact cert_lt (x := (783713156/831905767 : ℝ)) (y := (820830217/831905767 : ℝ)) (X := (26064994932217/100000000000000 : ℝ)) (Y := (9241875806183/12500000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (460522727/500000000 : ℝ)) (n' := (831905767/1000000000 : ℝ)) (Ab := (195928289/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (23026137/25000000 : ℝ) ^ p + (992461653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23026137/25000000 : ℝ)) (y := (992461653/1000000000 : ℝ)) (X := (15675015712441/100000000000000 : ℝ)) (Y := (84325000048401/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992461653/1000000000 : ℝ) ^ p + (23026137/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (992461653/1000000000 : ℝ)) (y := (23026137/25000000 : ℝ)) (X := (84325000048401/100000000000000 : ℝ)) (Y := (15675015712441/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1913507133/1000000000 : ℝ)) (τ := (23026137/25000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (391856592/415952899 : ℝ) ^ p + (410415124/415952899 : ℝ) ^ p := by
    exact cert_lt (x := (391856592/415952899 : ℝ)) (y := (410415124/415952899 : ℝ)) (X := (26064994029879/100000000000000 : ℝ)) (Y := (3696750364353/5000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (23026137/25000000 : ℝ)) (n' := (415952899/500000000 : ℝ)) (Ab := (24491037/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (921045481/1000000000 : ℝ) ^ p + (992461653/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921045481/1000000000 : ℝ)) (y := (992461653/1000000000 : ℝ)) (X := (7837508047947/50000000000000 : ℝ)) (Y := (84325000048401/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992461653/1000000000 : ℝ) ^ p + (921045481/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992461653/1000000000 : ℝ)) (y := (921045481/1000000000 : ℝ)) (X := (84325000048401/100000000000000 : ℝ)) (Y := (7837508047947/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (783713185/831905799 : ℝ) ^ p + (273610083/277301933 : ℝ) ^ p := by
    exact cert_lt (x := (783713185/831905799 : ℝ)) (y := (273610083/277301933 : ℝ)) (X := (26064994073289/100000000000000 : ℝ)) (Y := (462093795713/625000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (n' := (831905799/1000000000 : ℝ)) (Ab := (156742637/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (956753567/500000000 : ℝ)) (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1650215134/1807015169 : ℝ) ^ p + (1795939619/1807015169 : ℝ) ^ p := by
    exact cert_lt (x := (1650215134/1807015169 : ℝ)) (y := (1795939619/1807015169 : ℝ)) (X := (12935712459887/100000000000000 : ℝ)) (Y := (87064287879077/100000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108096019/1192984831 : ℝ) ^ p + (1181909281/1192984831 : ℝ) ^ p := by
    exact cert_lt (x := (1108096019/1192984831 : ℝ)) (y := (1181909281/1192984831 : ℝ)) (X := (4738532396781/25000000000000 : ℝ)) (Y := (40522935567701/50000000000000 : ℝ)) 721 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992461653/1000000000 : ℝ)) (U := (1192984831/1000000000 : ℝ)) (Ab := (825107567/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921045481/1000000000 : ℝ)) (σ := (992461653/1000000000 : ℝ)) (Ab := (1108096019/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab048
