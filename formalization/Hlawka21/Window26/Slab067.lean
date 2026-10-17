import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 67, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab067 (p : ℝ) (hpa : (483/16 : ℝ) ≤ p) (hpb : p ≤ (121/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (285769822001/21396900000000 : ℝ) (6832939/1000000000 : ℝ) (3200000641907/21396900000000 : ℝ) (591/500 : ℝ) (39093863/20000000 : ℝ) (977300209/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157931379/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2727/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(701/1250 : ℝ)
      else (1653/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11501/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (285769822001/21396900000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6832939/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (188577299/200000000 : ℝ) ^ p + (99390637/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (188577299/200000000 : ℝ)) (y := (99390637/100000000 : ℝ)) (X := (16880966763039/100000000000000 : ℝ)) (Y := (83119053535971/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99390637/100000000 : ℝ) ^ p + (188577299/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (99390637/100000000 : ℝ)) (y := (188577299/200000000 : ℝ)) (X := (83119053535971/100000000000000 : ℝ)) (Y := (16880966763039/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (387358573/200000000 : ℝ)) (τ := (188577299/200000000 : ℝ)) (σ := (99390637/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (826444614/869897585 : ℝ) ^ p + (863064646/869897585 : ℝ) ^ p := by
    exact cert_lt (x := (826444614/869897585 : ℝ)) (y := (863064646/869897585 : ℝ)) (X := (21222926148753/100000000000000 : ℝ)) (Y := (78777074818753/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (188577299/200000000 : ℝ)) (n' := (173979517/200000000 : ℝ)) (Ab := (413222307/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (236515801/250000000 : ℝ) ^ p + (993184067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236515801/250000000 : ℝ)) (y := (993184067/1000000000 : ℝ)) (X := (584029255967/3125000000000 : ℝ)) (Y := (1270485687987/1562500000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993184067/1000000000 : ℝ) ^ p + (236515801/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993184067/1000000000 : ℝ)) (y := (236515801/250000000 : ℝ)) (X := (1270485687987/1562500000000 : ℝ)) (Y := (584029255967/3125000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1939247271/1000000000 : ℝ)) (τ := (236515801/250000000 : ℝ)) (σ := (993184067/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (414892255/436759887 : ℝ) ^ p + (866686835/873519774 : ℝ) ^ p := by
    exact cert_lt (x := (414892255/436759887 : ℝ)) (y := (866686835/873519774 : ℝ)) (X := (5286164052951/25000000000000 : ℝ)) (Y := (78855345000983/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (236515801/250000000 : ℝ)) (n' := (436759887/500000000 : ℝ)) (Ab := (82978451/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (946147159/1000000000 : ℝ) ^ p + (993163777/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946147159/1000000000 : ℝ)) (y := (993163777/1000000000 : ℝ)) (X := (18739170464493/100000000000000 : ℝ)) (Y := (81260850040413/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993163777/1000000000 : ℝ) ^ p + (946147159/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163777/1000000000 : ℝ)) (y := (946147159/1000000000 : ℝ)) (X := (81260850040413/100000000000000 : ℝ)) (Y := (18739170464493/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (242413867/125000000 : ℝ)) (τ := (946147159/1000000000 : ℝ)) (σ := (993163777/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (414936310/436807669 : ℝ) ^ p + (866782399/873615338 : ℝ) ^ p := by
    exact cert_lt (x := (414936310/436807669 : ℝ)) (y := (866782399/873615338 : ℝ)) (X := (21142598935579/100000000000000 : ℝ)) (Y := (78857402224149/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (946147159/1000000000 : ℝ)) (n' := (436807669/500000000 : ℝ)) (Ab := (41493631/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (189229873/200000000 : ℝ) ^ p + (993163243/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (189229873/200000000 : ℝ)) (y := (993163243/1000000000 : ℝ)) (X := (18740492178123/100000000000000 : ℝ)) (Y := (81259528368349/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993163243/1000000000 : ℝ) ^ p + (189229873/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163243/1000000000 : ℝ)) (y := (189229873/200000000 : ℝ)) (X := (81259528368349/100000000000000 : ℝ)) (Y := (18740492178123/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (60603519/31250000 : ℝ)) (τ := (189229873/200000000 : ℝ)) (σ := (993163243/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (829874935/873617849 : ℝ) ^ p + (866784910/873617849 : ℝ) ^ p := by
    exact cert_lt (x := (829874935/873617849 : ℝ)) (y := (866784910/873617849 : ℝ)) (X := (660704524339/3125000000000 : ℝ)) (Y := (39428728136761/50000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (189229873/200000000 : ℝ)) (n' := (873617849/1000000000 : ℝ)) (Ab := (165974987/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (59134339/62500000 : ℝ) ^ p + (248290807/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (59134339/62500000 : ℝ)) (y := (248290807/250000000 : ℝ)) (X := (18740527528909/100000000000000 : ℝ)) (Y := (81259491243029/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248290807/250000000 : ℝ) ^ p + (59134339/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248290807/250000000 : ℝ)) (y := (59134339/62500000 : ℝ)) (X := (81259491243029/100000000000000 : ℝ)) (Y := (18740527528909/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (484828163/250000000 : ℝ)) (τ := (59134339/62500000 : ℝ)) (σ := (248290807/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (276624999/291205972 : ℝ) ^ p + (866784977/873617916 : ℝ) ^ p := by
    exact cert_lt (x := (276624999/291205972 : ℝ)) (y := (866784977/873617916 : ℝ)) (X := (21142543510903/100000000000000 : ℝ)) (Y := (4928591107231/6250000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (59134339/62500000 : ℝ)) (n' := (218404479/250000000 : ℝ)) (Ab := (829874997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (37845977/40000000 : ℝ) ^ p + (248290807/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (37845977/40000000 : ℝ)) (y := (248290807/250000000 : ℝ)) (X := (749621125123/4000000000000 : ℝ)) (Y := (81259491243029/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248290807/250000000 : ℝ) ^ p + (37845977/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (248290807/250000000 : ℝ)) (y := (37845977/40000000 : ℝ)) (X := (81259491243029/100000000000000 : ℝ)) (Y := (749621125123/4000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1939312653/1000000000 : ℝ)) (τ := (37845977/40000000 : ℝ)) (σ := (248290807/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (829874999/873617918 : ℝ) ^ p + (866784979/873617918 : ℝ) ^ p := by
    exact cert_lt (x := (829874999/873617918 : ℝ)) (y := (866784979/873617918 : ℝ)) (X := (264281794851/1250000000000 : ℝ)) (Y := (39428728879373/50000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (37845977/40000000 : ℝ)) (n' := (436808959/500000000 : ℝ)) (Ab := (829874999/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1939312653/1000000000 : ℝ)) (τ := (37845977/40000000 : ℝ)) (σ := (248290807/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (37845977/40000000 : ℝ)) (n' := (436808959/500000000 : ℝ)) (Ab := (829874999/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1939312653/1000000000 : ℝ)) (τ := (37845977/40000000 : ℝ)) (σ := (248290807/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (37845977/40000000 : ℝ)) (n' := (436808959/500000000 : ℝ)) (Ab := (829874999/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1939312653/1000000000 : ℝ)) (τ := (37845977/40000000 : ℝ)) (σ := (248290807/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (37845977/40000000 : ℝ)) (n' := (436808959/500000000 : ℝ)) (Ab := (829874999/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1939312653/1000000000 : ℝ)) (τ := (37845977/40000000 : ℝ)) (σ := (248290807/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (37845977/40000000 : ℝ)) (n' := (436808959/500000000 : ℝ)) (Ab := (829874999/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1939312653/1000000000 : ℝ)) (τ := (37845977/40000000 : ℝ)) (σ := (248290807/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1710523285/1842068621 : ℝ) ^ p + (1835235682/1842068621 : ℝ) ^ p := by
    exact cert_lt (x := (1710523285/1842068621 : ℝ)) (y := (1835235682/1842068621 : ℝ)) (X := (5316445664789/50000000000000 : ℝ)) (Y := (89367108923667/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1090737987/1157931379 : ℝ) ^ p + (1151098440/1157931379 : ℝ) ^ p := by
    exact cert_lt (x := (1090737987/1157931379 : ℝ)) (y := (1151098440/1157931379 : ℝ)) (X := (512256983307/3125000000000 : ℝ)) (Y := (83607777224017/100000000000000 : ℝ)) 121 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248290807/250000000 : ℝ)) (U := (1157931379/1000000000 : ℝ)) (Ab := (342104657/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (37845977/40000000 : ℝ)) (σ := (248290807/250000000 : ℝ)) (Ab := (1090737987/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab067
