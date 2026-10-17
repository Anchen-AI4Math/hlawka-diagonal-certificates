import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 151, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab151 (p : ℝ) (hpa : (823/32 : ℝ) ≤ p) (hpb : p ≤ (103/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2076614055263/112339500000000 : ℝ) (9495067/1000000000 : ℝ) (4000000674037/22467900000000 : ℝ) (3033/2500 : ℝ) (973440733/500000000 : ℝ) (973408893/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194289991/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2797/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(4691/10000 : ℝ)
      else (98/125 : ℝ) ≤ X j i ∧ X j i ≤ (5931/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2076614055263/112339500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9495067/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (463054471/500000000 : ℝ) ^ p + (994225801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (463054471/500000000 : ℝ)) (y := (994225801/1000000000 : ℝ)) (X := (6926574357327/50000000000000 : ℝ)) (Y := (86146870134509/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994225801/1000000000 : ℝ) ^ p + (463054471/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (994225801/1000000000 : ℝ)) (y := (463054471/500000000 : ℝ)) (X := (86146870134509/100000000000000 : ℝ)) (Y := (6926574357327/50000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1920334743/1000000000 : ℝ)) (τ := (463054471/500000000 : ℝ)) (σ := (994225801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (791840107/834984417 : ℝ) ^ p + (825489350/834984417 : ℝ) ^ p := by
    exact cert_lt (x := (791840107/834984417 : ℝ)) (y := (825489350/834984417 : ℝ)) (X := (1275461824917/5000000000000 : ℝ)) (Y := (37245382232357/50000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (463054471/500000000 : ℝ)) (n' := (834984417/1000000000 : ℝ)) (Ab := (791840107/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (186291773/200000000 : ℝ) ^ p + (993220587/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186291773/200000000 : ℝ)) (y := (993220587/1000000000 : ℝ)) (X := (160681090261/1000000000000 : ℝ)) (Y := (83931909795291/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993220587/1000000000 : ℝ) ^ p + (186291773/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993220587/1000000000 : ℝ)) (y := (186291773/200000000 : ℝ)) (X := (83931909795291/100000000000000 : ℝ)) (Y := (160681090261/1000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (481169863/250000000 : ℝ)) (τ := (186291773/200000000 : ℝ)) (σ := (993220587/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (159516813/168250553 : ℝ) ^ p + (831757698/841252765 : ℝ) ^ p := by
    exact cert_lt (x := (159516813/168250553 : ℝ)) (y := (831757698/841252765 : ℝ)) (X := (25344665927451/100000000000000 : ℝ)) (Y := (74655335539821/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (186291773/200000000 : ℝ)) (n' := (168250553/200000000 : ℝ)) (Ab := (159516813/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (232916577/250000000 : ℝ) ^ p + (993178101/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232916577/250000000 : ℝ)) (y := (993178101/1000000000 : ℝ)) (X := (16160509561311/100000000000000 : ℝ)) (Y := (20959877309399/25000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993178101/1000000000 : ℝ) ^ p + (232916577/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993178101/1000000000 : ℝ)) (y := (232916577/250000000 : ℝ)) (X := (20959877309399/25000000000000 : ℝ)) (Y := (16160509561311/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1924844409/1000000000 : ℝ)) (τ := (232916577/250000000 : ℝ)) (σ := (993178101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797806100/841495107 : ℝ) ^ p + (832000040/841495107 : ℝ) ^ p := by
    exact cert_lt (x := (797806100/841495107 : ℝ)) (y := (832000040/841495107 : ℝ)) (X := (12669172837353/50000000000000 : ℝ)) (Y := (74661655786823/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (232916577/250000000 : ℝ)) (n' := (841495107/1000000000 : ℝ)) (Ab := (7978061/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (931674273/1000000000 : ℝ) ^ p + (62073529/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (931674273/1000000000 : ℝ)) (y := (62073529/62500000 : ℝ)) (X := (16164067542283/100000000000000 : ℝ)) (Y := (41917975484831/50000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (62073529/62500000 : ℝ) ^ p + (931674273/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62073529/62500000 : ℝ)) (y := (931674273/1000000000 : ℝ)) (X := (41917975484831/50000000000000 : ℝ)) (Y := (16164067542283/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924850737/1000000000 : ℝ)) (τ := (931674273/1000000000 : ℝ)) (σ := (62073529/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (797814624/841504411 : ℝ) ^ p + (832009344/841504411 : ℝ) ^ p := by
    exact cert_lt (x := (797814624/841504411 : ℝ)) (y := (832009344/841504411 : ℝ)) (X := (6334525706247/25000000000000 : ℝ)) (Y := (74661898371587/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (931674273/1000000000 : ℝ)) (n' := (841504411/1000000000 : ℝ)) (Ab := (24931707/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (931674579/1000000000 : ℝ) ^ p + (993176401/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931674579/1000000000 : ℝ)) (y := (993176401/1000000000 : ℝ)) (X := (3232840849619/20000000000000 : ℝ)) (Y := (83835814032501/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993176401/1000000000 : ℝ) ^ p + (931674579/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993176401/1000000000 : ℝ)) (y := (931674579/1000000000 : ℝ)) (X := (83835814032501/100000000000000 : ℝ)) (Y := (3232840849619/20000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (96242549/50000000 : ℝ)) (τ := (931674579/1000000000 : ℝ)) (σ := (993176401/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797814952/841504769 : ℝ) ^ p + (832009702/841504769 : ℝ) ^ p := by
    exact cert_lt (x := (797814952/841504769 : ℝ)) (y := (832009702/841504769 : ℝ)) (X := (25338093491299/100000000000000 : ℝ)) (Y := (74661907705689/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (931674579/1000000000 : ℝ)) (n' := (841504769/1000000000 : ℝ)) (Ab := (99726869/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (93167459/100000000 : ℝ) ^ p + (993176399/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (93167459/100000000 : ℝ)) (y := (993176399/1000000000 : ℝ)) (X := (16164209162377/100000000000000 : ℝ)) (Y := (83835809685293/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993176399/1000000000 : ℝ) ^ p + (93167459/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993176399/1000000000 : ℝ)) (y := (93167459/100000000 : ℝ)) (X := (83835809685293/100000000000000 : ℝ)) (Y := (16164209162377/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1924850989/1000000000 : ℝ)) (τ := (93167459/100000000 : ℝ)) (σ := (993176399/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (398907482/420752391 : ℝ) ^ p + (832009715/841504782 : ℝ) ^ p := by
    exact cert_lt (x := (398907482/420752391 : ℝ)) (y := (832009715/841504782 : ℝ)) (X := (12669046612733/50000000000000 : ℝ)) (Y := (74661908044637/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (93167459/100000000 : ℝ)) (n' := (420752391/500000000 : ℝ)) (Ab := (199453741/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (29114831/31250000 : ℝ) ^ p + (496588199/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (29114831/31250000 : ℝ)) (y := (496588199/500000000 : ℝ)) (X := (16164210055883/100000000000000 : ℝ)) (Y := (83835807511689/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496588199/500000000 : ℝ) ^ p + (29114831/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (496588199/500000000 : ℝ)) (y := (29114831/31250000 : ℝ)) (X := (83835807511689/100000000000000 : ℝ)) (Y := (16164210055883/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (192485099/100000000 : ℝ)) (τ := (29114831/31250000 : ℝ)) (σ := (496588199/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (398907483/420752392 : ℝ) ^ p + (832009717/841504784 : ℝ) ^ p := by
    exact cert_lt (x := (398907483/420752392 : ℝ)) (y := (832009717/841504784 : ℝ)) (X := (1583630831899/6250000000000 : ℝ)) (Y := (74661908096783/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (29114831/31250000 : ℝ)) (n' := (52594049/62500000 : ℝ)) (Ab := (398907483/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (192485099/100000000 : ℝ)) (τ := (29114831/31250000 : ℝ)) (σ := (496588199/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (29114831/31250000 : ℝ)) (n' := (52594049/62500000 : ℝ)) (Ab := (398907483/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (192485099/100000000 : ℝ)) (τ := (29114831/31250000 : ℝ)) (σ := (496588199/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (29114831/31250000 : ℝ)) (n' := (52594049/62500000 : ℝ)) (Ab := (398907483/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (192485099/100000000 : ℝ)) (τ := (29114831/31250000 : ℝ)) (σ := (496588199/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (29114831/31250000 : ℝ)) (n' := (52594049/62500000 : ℝ)) (Ab := (398907483/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (192485099/100000000 : ℝ)) (τ := (29114831/31250000 : ℝ)) (σ := (496588199/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1666622855/1805710009 : ℝ) ^ p + (1796214942/1805710009 : ℝ) ^ p := by
    exact cert_lt (x := (1666622855/1805710009 : ℝ)) (y := (1796214942/1805710009 : ℝ)) (X := (12694780372843/100000000000000 : ℝ)) (Y := (87305220000913/100000000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1118723034/1194289991 : ℝ) ^ p + (1184794924/1194289991 : ℝ) ^ p := by
    exact cert_lt (x := (1118723034/1194289991 : ℝ)) (y := (1184794924/1194289991 : ℝ)) (X := (4644824253483/25000000000000 : ℝ)) (Y := (162841407009/200000000000 : ℝ)) 103 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496588199/500000000 : ℝ)) (U := (1194289991/1000000000 : ℝ)) (Ab := (333324571/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (29114831/31250000 : ℝ)) (σ := (496588199/500000000 : ℝ)) (Ab := (559361517/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab151
