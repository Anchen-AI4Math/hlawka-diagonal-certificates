import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 7, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab007 (p : ℝ) (hpa : (679/32 : ℝ) ≤ p) (hpb : p ≤ (85/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (212750888807/9268350000000 : ℝ) (2964599/250000000 : ℝ) (4000000556101/18536700000000 : ℝ) (3033/2500 : ℝ) (483953781/250000000 : ℝ) (120982633/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192479389/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1379/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(4421/10000 : ℝ)
      else (3787/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1479/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (212750888807/9268350000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2964599/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (454774731/500000000 : ℝ) ^ p + (496643239/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (454774731/500000000 : ℝ)) (y := (496643239/500000000 : ℝ)) (X := (1333703613493/10000000000000 : ℝ)) (Y := (43331490127387/50000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496643239/500000000 : ℝ) ^ p + (454774731/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496643239/500000000 : ℝ)) (y := (454774731/500000000 : ℝ)) (X := (43331490127387/50000000000000 : ℝ)) (Y := (1333703613493/10000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (95141797/50000000 : ℝ)) (τ := (454774731/500000000 : ℝ)) (σ := (496643239/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (770055335/819518786 : ℝ) ^ p + (403830195/409759393 : ℝ) ^ p := by
    exact cert_lt (x := (770055335/819518786 : ℝ)) (y := (403830195/409759393 : ℝ)) (X := (13317852230769/50000000000000 : ℝ)) (Y := (73364296382823/100000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (454774731/500000000 : ℝ)) (n' := (409759393/500000000 : ℝ)) (Ab := (154011067/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (91550853/100000000 : ℝ) ^ p + (198440759/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (91550853/100000000 : ℝ)) (y := (198440759/200000000 : ℝ)) (X := (7661184118529/50000000000000 : ℝ)) (Y := (21169411716831/25000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198440759/200000000 : ℝ) ^ p + (91550853/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198440759/200000000 : ℝ)) (y := (91550853/100000000 : ℝ)) (X := (21169411716831/25000000000000 : ℝ)) (Y := (7661184118529/50000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (76308493/40000000 : ℝ)) (τ := (91550853/100000000 : ℝ)) (σ := (198440759/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (776501917/826670061 : ℝ) ^ p + (814811665/826670061 : ℝ) ^ p := by
    exact cert_lt (x := (776501917/826670061 : ℝ)) (y := (814811665/826670061 : ℝ)) (X := (26437437718917/100000000000000 : ℝ)) (Y := (36781281758111/50000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (91550853/100000000 : ℝ)) (n' := (826670061/1000000000 : ℝ)) (Ab := (776501917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (228952559/250000000 : ℝ) ^ p + (496072197/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (228952559/250000000 : ℝ)) (y := (496072197/500000000 : ℝ)) (X := (3857507168411/25000000000000 : ℝ)) (Y := (845699861283/1000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496072197/500000000 : ℝ) ^ p + (228952559/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496072197/500000000 : ℝ)) (y := (228952559/250000000 : ℝ)) (X := (845699861283/1000000000000 : ℝ)) (Y := (3857507168411/25000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (190795463/100000000 : ℝ)) (τ := (228952559/250000000 : ℝ)) (σ := (496072197/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (258942382/275676973 : ℝ) ^ p + (74106593/75184629 : ℝ) ^ p := by
    exact cert_lt (x := (258942382/275676973 : ℝ)) (y := (74106593/75184629 : ℝ)) (X := (26427510525501/100000000000000 : ℝ)) (Y := (73572490721803/100000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (228952559/250000000 : ℝ)) (n' := (827030919/1000000000 : ℝ)) (Ab := (388413573/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (114478167/125000000 : ℝ) ^ p + (992141409/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114478167/125000000 : ℝ)) (y := (992141409/1000000000 : ℝ)) (X := (15435435838681/100000000000000 : ℝ)) (Y := (16912915887791/20000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992141409/1000000000 : ℝ) ^ p + (114478167/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992141409/1000000000 : ℝ)) (y := (114478167/125000000 : ℝ)) (X := (16912915887791/20000000000000 : ℝ)) (Y := (15435435838681/100000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (381593349/200000000 : ℝ)) (τ := (114478167/125000000 : ℝ)) (σ := (992141409/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (194210855/206762244 : ℝ) ^ p + (203797645/206762244 : ℝ) ^ p := by
    exact cert_lt (x := (194210855/206762244 : ℝ)) (y := (203797645/206762244 : ℝ)) (X := (26427013984707/100000000000000 : ℝ)) (Y := (18393246818977/25000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (114478167/125000000 : ℝ)) (n' := (51690561/62500000 : ℝ)) (Ab := (38842171/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (915826091/1000000000 : ℝ) ^ p + (49607063/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (915826091/1000000000 : ℝ)) (y := (49607063/50000000 : ℝ)) (X := (7717853122163/50000000000000 : ℝ)) (Y := (4228215478297/5000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (49607063/50000000 : ℝ) ^ p + (915826091/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49607063/50000000 : ℝ)) (y := (915826091/1000000000 : ℝ)) (X := (4228215478297/5000000000000 : ℝ)) (Y := (7717853122163/50000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1907967351/1000000000 : ℝ)) (τ := (915826091/1000000000 : ℝ)) (σ := (49607063/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (86316026/91894431 : ℝ) ^ p + (815191483/827049879 : ℝ) ^ p := by
    exact cert_lt (x := (86316026/91894431 : ℝ)) (y := (815191483/827049879 : ℝ)) (X := (13213494636743/50000000000000 : ℝ)) (Y := (73573012107253/100000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (915826091/1000000000 : ℝ)) (n' := (827049879/1000000000 : ℝ)) (Ab := (388422117/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (91582613/100000000 : ℝ) ^ p + (248035313/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (91582613/100000000 : ℝ)) (y := (248035313/250000000 : ℝ)) (X := (7717860106211/50000000000000 : ℝ)) (Y := (84564295076137/100000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248035313/250000000 : ℝ) ^ p + (91582613/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248035313/250000000 : ℝ)) (y := (91582613/100000000 : ℝ)) (X := (84564295076137/100000000000000 : ℝ)) (Y := (7717860106211/50000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (953983691/500000000 : ℝ)) (τ := (91582613/100000000 : ℝ)) (σ := (248035313/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (388422138/413524963 : ℝ) ^ p + (407595765/413524963 : ℝ) ^ p := by
    exact cert_lt (x := (388422138/413524963 : ℝ)) (y := (407595765/413524963 : ℝ)) (X := (330337346519/1250000000000 : ℝ)) (Y := (73573013399691/100000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (91582613/100000000 : ℝ)) (n' := (413524963/500000000 : ℝ)) (Ab := (194211069/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (915826131/1000000000 : ℝ) ^ p + (248035313/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (915826131/1000000000 : ℝ)) (y := (248035313/250000000 : ℝ)) (X := (7717860285289/50000000000000 : ℝ)) (Y := (84564295076137/100000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248035313/250000000 : ℝ) ^ p + (915826131/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248035313/250000000 : ℝ)) (y := (915826131/1000000000 : ℝ)) (X := (84564295076137/100000000000000 : ℝ)) (Y := (7717860285289/50000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1907967383/1000000000 : ℝ)) (τ := (915826131/1000000000 : ℝ)) (σ := (248035313/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (70622207/75186357 : ℝ) ^ p + (74108321/75186357 : ℝ) ^ p := by
    exact cert_lt (x := (70622207/75186357 : ℝ)) (y := (74108321/75186357 : ℝ)) (X := (26426987765403/100000000000000 : ℝ)) (Y := (7357301342719/10000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (915826131/1000000000 : ℝ)) (n' := (827049927/1000000000 : ℝ)) (Ab := (776844277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1907967383/1000000000 : ℝ)) (τ := (915826131/1000000000 : ℝ)) (σ := (248035313/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (915826131/1000000000 : ℝ)) (n' := (827049927/1000000000 : ℝ)) (Ab := (776844277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1907967383/1000000000 : ℝ)) (τ := (915826131/1000000000 : ℝ)) (σ := (248035313/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (915826131/1000000000 : ℝ)) (n' := (827049927/1000000000 : ℝ)) (Ab := (776844277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1907967383/1000000000 : ℝ)) (τ := (915826131/1000000000 : ℝ)) (σ := (248035313/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (915826131/1000000000 : ℝ)) (n' := (827049927/1000000000 : ℝ)) (Ab := (776844277/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1907967383/1000000000 : ℝ)) (τ := (915826131/1000000000 : ℝ)) (σ := (248035313/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1642364975/1807520611 : ℝ) ^ p + (1795662215/1807520611 : ℝ) ^ p := by
    exact cert_lt (x := (1642364975/1807520611 : ℝ)) (y := (1795662215/1807520611 : ℝ)) (X := (6526515217441/50000000000000 : ℝ)) (Y := (10868371232663/12500000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1103197617/1192479389 : ℝ) ^ p + (1180620993/1192479389 : ℝ) ^ p := by
    exact cert_lt (x := (1103197617/1192479389 : ℝ)) (y := (1180620993/1192479389 : ℝ)) (X := (19133821406179/100000000000000 : ℝ)) (Y := (20216544773537/25000000000000 : ℝ)) 85 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248035313/250000000 : ℝ)) (U := (1192479389/1000000000 : ℝ)) (Ab := (65694599/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (915826131/1000000000 : ℝ)) (σ := (248035313/250000000 : ℝ)) (Ab := (1103197617/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab007
