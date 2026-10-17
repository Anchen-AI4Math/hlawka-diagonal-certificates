import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 38, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab038 (p : ℝ) (hpa : (227/8 : ℝ) ≤ p) (hpb : p ≤ (455/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (359872105873/25140250000000 : ℝ) (3667141/500000000 : ℝ) (1600000301683/10056100000000 : ℝ) (591/500 : ℝ) (975920251/500000000 : ℝ) (60991741/62500000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156864409/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(543/500 : ℝ) ≤ X j i ∧ X j i ≤ -(5551/10000 : ℝ)
      else (4103/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5743/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (359872105873/25140250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3667141/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (234767061/250000000 : ℝ) ^ p + (496790681/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (234767061/250000000 : ℝ)) (y := (496790681/500000000 : ℝ)) (X := (1673305854031/10000000000000 : ℝ)) (Y := (83266961678957/100000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496790681/500000000 : ℝ) ^ p + (234767061/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496790681/500000000 : ℝ)) (y := (234767061/250000000 : ℝ)) (X := (83266961678957/100000000000000 : ℝ)) (Y := (1673305854031/10000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (966324803/500000000 : ℝ)) (τ := (234767061/250000000 : ℝ)) (σ := (496790681/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (821182577/866840056 : ℝ) ^ p + (429752887/433420028 : ℝ) ^ p := by
    exact cert_lt (x := (821182577/866840056 : ℝ)) (y := (429752887/433420028 : ℝ)) (X := (21465460829787/100000000000000 : ℝ)) (Y := (15706908060807/20000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (234767061/250000000 : ℝ)) (n' := (108355007/125000000 : ℝ)) (Ab := (821182577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (235597559/250000000 : ℝ) ^ p + (992831957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (235597559/250000000 : ℝ)) (y := (992831957/1000000000 : ℝ)) (X := (9250341108191/50000000000000 : ℝ)) (Y := (81499336718933/100000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992831957/1000000000 : ℝ) ^ p + (235597559/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992831957/1000000000 : ℝ)) (y := (235597559/250000000 : ℝ)) (X := (81499336718933/100000000000000 : ℝ)) (Y := (9250341108191/50000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1935222193/1000000000 : ℝ)) (τ := (235597559/250000000 : ℝ)) (σ := (992831957/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (824678683/870649767 : ℝ) ^ p + (863315485/870649767 : ℝ) ^ p := by
    exact cert_lt (x := (824678683/870649767 : ℝ)) (y := (863315485/870649767 : ℝ)) (X := (21382029084027/100000000000000 : ℝ)) (Y := (39308986084157/50000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (235597559/250000000 : ℝ)) (n' := (870649767/1000000000 : ℝ)) (Ab := (824678683/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (471242629/500000000 : ℝ) ^ p + (992809193/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471242629/500000000 : ℝ)) (y := (992809193/1000000000 : ℝ)) (X := (18553804093499/100000000000000 : ℝ)) (Y := (4072310691303/5000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992809193/1000000000 : ℝ) ^ p + (471242629/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992809193/1000000000 : ℝ)) (y := (471242629/500000000 : ℝ)) (X := (4072310691303/5000000000000 : ℝ)) (Y := (18553804093499/100000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1935294451/1000000000 : ℝ)) (τ := (471242629/500000000 : ℝ)) (σ := (992809193/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (137463083/145126424 : ℝ) ^ p + (431712131/435379272 : ℝ) ^ p := by
    exact cert_lt (x := (137463083/145126424 : ℝ)) (y := (431712131/435379272 : ℝ)) (X := (10689828231101/50000000000000 : ℝ)) (Y := (7862034489099/10000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (471242629/500000000 : ℝ)) (n' := (54422409/62500000 : ℝ)) (Ab := (412389249/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (23562199/25000000 : ℝ) ^ p + (198561709/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (23562199/25000000 : ℝ)) (y := (198561709/200000000 : ℝ)) (X := (9277658395763/50000000000000 : ℝ)) (Y := (81444702119/100000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198561709/200000000 : ℝ) ^ p + (23562199/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (198561709/200000000 : ℝ)) (y := (23562199/25000000 : ℝ)) (X := (81444702119/100000000000 : ℝ)) (Y := (9277658395763/50000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (387059301/200000000 : ℝ)) (τ := (23562199/25000000 : ℝ)) (σ := (198561709/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (274927112/290253879 : ℝ) ^ p + (863427355/870761637 : ℝ) ^ p := by
    exact cert_lt (x := (274927112/290253879 : ℝ)) (y := (863427355/870761637 : ℝ)) (X := (21379588884183/100000000000000 : ℝ)) (Y := (9827551543761/12500000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (23562199/25000000 : ℝ)) (n' := (870761637/1000000000 : ℝ)) (Ab := (103097667/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (235622009/250000000 : ℝ) ^ p + (992808527/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (235622009/250000000 : ℝ)) (y := (992808527/1000000000 : ℝ)) (X := (9277679670689/50000000000000 : ℝ)) (Y := (20361165031881/25000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992808527/1000000000 : ℝ) ^ p + (235622009/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992808527/1000000000 : ℝ)) (y := (235622009/250000000 : ℝ)) (X := (20361165031881/25000000000000 : ℝ)) (Y := (9277679670689/50000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1935296563/1000000000 : ℝ)) (τ := (235622009/250000000 : ℝ)) (σ := (992808527/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (206195354/217690431 : ℝ) ^ p + (431713721/435380862 : ℝ) ^ p := by
    exact cert_lt (x := (206195354/217690431 : ℝ)) (y := (431713721/435380862 : ℝ)) (X := (10689793555311/50000000000000 : ℝ)) (Y := (78620414247573/100000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (235622009/250000000 : ℝ)) (n' := (217690431/250000000 : ℝ)) (Ab := (103097677/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (942488039/1000000000 : ℝ) ^ p + (496404263/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (942488039/1000000000 : ℝ)) (y := (496404263/500000000 : ℝ)) (X := (18555361020979/100000000000000 : ℝ)) (Y := (16288931558933/20000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496404263/500000000 : ℝ) ^ p + (942488039/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496404263/500000000 : ℝ)) (y := (942488039/1000000000 : ℝ)) (X := (16288931558933/20000000000000 : ℝ)) (Y := (18555361020979/100000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (387059313/200000000 : ℝ)) (τ := (942488039/1000000000 : ℝ)) (σ := (496404263/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (824781418/870761727 : ℝ) ^ p + (863427445/870761727 : ℝ) ^ p := by
    exact cert_lt (x := (824781418/870761727 : ℝ)) (y := (863427445/870761727 : ℝ)) (X := (21379586490253/100000000000000 : ℝ)) (Y := (19655103578251/25000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (942488039/1000000000 : ℝ)) (n' := (870761727/1000000000 : ℝ)) (Ab := (412390709/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (387059313/200000000 : ℝ)) (τ := (942488039/1000000000 : ℝ)) (σ := (496404263/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (942488039/1000000000 : ℝ)) (n' := (870761727/1000000000 : ℝ)) (Ab := (412390709/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (387059313/200000000 : ℝ)) (τ := (942488039/1000000000 : ℝ)) (σ := (496404263/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (942488039/1000000000 : ℝ)) (n' := (870761727/1000000000 : ℝ)) (Ab := (412390709/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (387059313/200000000 : ℝ)) (τ := (942488039/1000000000 : ℝ)) (σ := (496404263/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (942488039/1000000000 : ℝ)) (n' := (870761727/1000000000 : ℝ)) (Ab := (412390709/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (387059313/200000000 : ℝ)) (τ := (942488039/1000000000 : ℝ)) (σ := (496404263/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (942488039/1000000000 : ℝ)) (n' := (870761727/1000000000 : ℝ)) (Ab := (412390709/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (387059313/200000000 : ℝ)) (τ := (942488039/1000000000 : ℝ)) (σ := (496404263/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1703936171/1843135591 : ℝ) ^ p + (1835801309/1843135591 : ℝ) ^ p := by
    exact cert_lt (x := (1703936171/1843135591 : ℝ)) (y := (1835801309/1843135591 : ℝ)) (X := (10719352304071/100000000000000 : ℝ)) (Y := (11160080995337/12500000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1085942785/1156864409 : ℝ) ^ p + (1149530127/1156864409 : ℝ) ^ p := by
    exact cert_lt (x := (1085942785/1156864409 : ℝ)) (y := (1149530127/1156864409 : ℝ)) (X := (16544933063507/100000000000000 : ℝ)) (Y := (16691013513369/20000000000000 : ℝ)) 455 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496404263/500000000 : ℝ)) (U := (1156864409/1000000000 : ℝ)) (Ab := (1703936171/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (942488039/1000000000 : ℝ)) (σ := (496404263/500000000 : ℝ)) (Ab := (217188557/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab038
