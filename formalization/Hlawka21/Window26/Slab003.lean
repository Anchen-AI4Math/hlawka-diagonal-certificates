import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 3, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab003 (p : ℝ) (hpa : (419/16 : ℝ) ≤ p) (hpb : p ≤ (105/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (727136701151/46404250000000 : ℝ) (8044953/1000000000 : ℝ) (3200000556851/18561700000000 : ℝ) (591/500 : ℝ) (973939973/500000000 : ℝ) (243469649/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1155472391/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2159/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(5469/10000 : ℝ)
      else (8123/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11467/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (727136701151/46404250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (8044953/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (58357691/62500000 : ℝ) ^ p + (248285329/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (58357691/62500000 : ℝ)) (y := (248285329/250000000 : ℝ)) (X := (4132041565187/25000000000000 : ℝ)) (Y := (10433981497243/12500000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248285329/250000000 : ℝ) ^ p + (58357691/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248285329/250000000 : ℝ)) (y := (58357691/62500000 : ℝ)) (X := (10433981497243/12500000000000 : ℝ)) (Y := (4132041565187/25000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (481716093/250000000 : ℝ)) (τ := (58357691/62500000 : ℝ)) (σ := (248285329/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (813859267/862471707 : ℝ) ^ p + (284808918/287490569 : ℝ) ^ p := by
    exact cert_lt (x := (813859267/862471707 : ℝ)) (y := (284808918/287490569 : ℝ)) (X := (4361611309547/20000000000000 : ℝ)) (Y := (39095972289321/50000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (58357691/62500000 : ℝ)) (n' := (862471707/1000000000 : ℝ)) (Ab := (813859267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (58576879/62500000 : ℝ) ^ p + (992358863/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (58576879/62500000 : ℝ)) (y := (992358863/1000000000 : ℝ)) (X := (3647481018259/20000000000000 : ℝ)) (Y := (81762612926261/100000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992358863/1000000000 : ℝ) ^ p + (58576879/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992358863/1000000000 : ℝ)) (y := (58576879/62500000 : ℝ)) (X := (81762612926261/100000000000000 : ℝ)) (Y := (3647481018259/20000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1929588927/1000000000 : ℝ)) (τ := (58576879/62500000 : ℝ)) (σ := (992358863/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (817555671/866526125 : ℝ) ^ p + (858481172/866526125 : ℝ) ^ p := by
    exact cert_lt (x := (817555671/866526125 : ℝ)) (y := (858481172/866526125 : ℝ)) (X := (2171758133167/10000000000000 : ℝ)) (Y := (78282419544071/100000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (58576879/62500000 : ℝ)) (n' := (6932209/8000000 : ℝ)) (Ab := (817555671/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (46867071/50000000 : ℝ) ^ p + (198466503/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (46867071/50000000 : ℝ)) (y := (198466503/200000000 : ℝ)) (X := (4573592629463/25000000000000 : ℝ)) (Y := (20426411676627/25000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198466503/200000000 : ℝ) ^ p + (46867071/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (198466503/200000000 : ℝ)) (y := (46867071/50000000 : ℝ)) (X := (20426411676627/25000000000000 : ℝ)) (Y := (4573592629463/25000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (385934787/200000000 : ℝ)) (τ := (46867071/50000000 : ℝ)) (σ := (198466503/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (817672806/866654617 : ℝ) ^ p + (858609664/866654617 : ℝ) ^ p := by
    exact cert_lt (x := (817672806/866654617 : ℝ)) (y := (858609664/866654617 : ℝ)) (X := (5428681536143/25000000000000 : ℝ)) (Y := (39142637330623/50000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (46867071/50000000 : ℝ)) (n' := (866654617/1000000000 : ℝ)) (Ab := (408836403/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (468672467/500000000 : ℝ) ^ p + (496165841/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (468672467/500000000 : ℝ)) (y := (496165841/500000000 : ℝ)) (X := (285877670739/1562500000000 : ℝ)) (Y := (40851923162473/50000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496165841/500000000 : ℝ) ^ p + (468672467/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496165841/500000000 : ℝ)) (y := (468672467/500000000 : ℝ)) (X := (40851923162473/50000000000000 : ℝ)) (Y := (285877670739/1562500000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (241209577/125000000 : ℝ)) (τ := (468672467/500000000 : ℝ)) (σ := (496165841/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (817676502/866658671 : ℝ) ^ p + (858613718/866658671 : ℝ) ^ p := by
    exact cert_lt (x := (817676502/866658671 : ℝ)) (y := (858613718/866658671 : ℝ)) (X := (21714636304559/100000000000000 : ℝ)) (Y := (15657072945953/20000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (468672467/500000000 : ℝ)) (n' := (866658671/1000000000 : ℝ)) (Ab := (408838251/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (234336261/250000000 : ℝ) ^ p + (124041457/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (234336261/250000000 : ℝ)) (y := (124041457/125000000 : ℝ)) (X := (4574056822227/25000000000000 : ℝ)) (Y := (40851895065589/50000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124041457/125000000 : ℝ) ^ p + (234336261/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124041457/125000000 : ℝ)) (y := (234336261/250000000 : ℝ)) (X := (40851895065589/50000000000000 : ℝ)) (Y := (4574056822227/25000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (19296767/10000000 : ℝ)) (τ := (234336261/250000000 : ℝ)) (σ := (124041457/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (408838309/433329399 : ℝ) ^ p + (286204615/288886266 : ℝ) ^ p := by
    exact cert_lt (x := (408838309/433329399 : ℝ)) (y := (286204615/288886266 : ℝ)) (X := (10857316820049/50000000000000 : ℝ)) (Y := (39142683775669/50000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (234336261/250000000 : ℝ)) (n' := (433329399/500000000 : ℝ)) (Ab := (408838309/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (117168131/125000000 : ℝ) ^ p + (198466331/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (117168131/125000000 : ℝ)) (y := (198466331/200000000 : ℝ)) (X := (731849173537/4000000000000 : ℝ)) (Y := (2042594699247/2500000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198466331/200000000 : ℝ) ^ p + (117168131/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (198466331/200000000 : ℝ)) (y := (117168131/125000000 : ℝ)) (X := (2042594699247/2500000000000 : ℝ)) (Y := (731849173537/4000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1929676703/1000000000 : ℝ)) (τ := (117168131/125000000 : ℝ)) (σ := (198466331/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (817676622/866658803 : ℝ) ^ p + (858613850/866658803 : ℝ) ^ p := by
    exact cert_lt (x := (817676622/866658803 : ℝ)) (y := (858613850/866658803 : ℝ)) (X := (21714633139987/100000000000000 : ℝ)) (Y := (78285367662423/100000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (117168131/125000000 : ℝ)) (n' := (866658803/1000000000 : ℝ)) (Ab := (408838311/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1929676703/1000000000 : ℝ)) (τ := (117168131/125000000 : ℝ)) (σ := (198466331/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (117168131/125000000 : ℝ)) (n' := (866658803/1000000000 : ℝ)) (Ab := (408838311/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1929676703/1000000000 : ℝ)) (τ := (117168131/125000000 : ℝ)) (σ := (198466331/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (117168131/125000000 : ℝ)) (n' := (866658803/1000000000 : ℝ)) (Ab := (408838311/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1929676703/1000000000 : ℝ)) (τ := (117168131/125000000 : ℝ)) (σ := (198466331/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (117168131/125000000 : ℝ)) (n' := (866658803/1000000000 : ℝ)) (Ab := (408838311/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1929676703/1000000000 : ℝ)) (τ := (117168131/125000000 : ℝ)) (σ := (198466331/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (117168131/125000000 : ℝ)) (n' := (866658803/1000000000 : ℝ)) (Ab := (408838311/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1929676703/1000000000 : ℝ)) (τ := (117168131/125000000 : ℝ)) (σ := (198466331/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1694824549/1844527609 : ℝ) ^ p + (1836482656/1844527609 : ℝ) ^ p := by
    exact cert_lt (x := (1694824549/1844527609 : ℝ)) (y := (1836482656/1844527609 : ℝ)) (X := (10840245758979/100000000000000 : ℝ)) (Y := (44579877239913/50000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1079456124/1155472391 : ℝ) ^ p + (1147427438/1155472391 : ℝ) ^ p := by
    exact cert_lt (x := (1079456124/1155472391 : ℝ)) (y := (1147427438/1155472391 : ℝ)) (X := (4189211890331/25000000000000 : ℝ)) (Y := (8324315285593/10000000000000 : ℝ)) 105 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198466331/200000000 : ℝ)) (U := (1155472391/1000000000 : ℝ)) (Ab := (1694824549/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (117168131/125000000 : ℝ)) (σ := (198466331/200000000 : ℝ)) (Ab := (269864031/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab003
