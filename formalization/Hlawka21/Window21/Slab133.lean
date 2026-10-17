import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 133, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab133 (p : ℝ) (hpa : (805/32 : ℝ) ≤ p) (hpb : p ≤ (403/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (416397939871/21976500000000 : ℝ) (77907/8000000 : ℝ) (800000131859/4395300000000 : ℝ) (3033/2500 : ℝ) (972855721/500000000 : ℝ) (972822463/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597031533/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11171/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4663/10000 : ℝ)
      else (1953/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5929/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (416397939871/21976500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (77907/8000000 : ℝ) := by norm_num
  have pc0 : 1 < (924377323/1000000000 : ℝ) ^ p + (15533161/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (924377323/1000000000 : ℝ)) (y := (15533161/15625000 : ℝ)) (X := (3449600624259/25000000000000 : ℝ)) (Y := (5387601004357/6250000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (15533161/15625000 : ℝ) ^ p + (924377323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (15533161/15625000 : ℝ)) (y := (924377323/1000000000 : ℝ)) (X := (5387601004357/6250000000000 : ℝ)) (Y := (3449600624259/25000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1918499627/1000000000 : ℝ)) (τ := (924377323/1000000000 : ℝ)) (σ := (15533161/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (263183239/277802166 : ℝ) ^ p + (274556041/277802166 : ℝ) ^ p := by
    exact cert_lt (x := (263183239/277802166 : ℝ)) (y := (274556041/277802166 : ℝ)) (X := (12812473782977/50000000000000 : ℝ)) (Y := (3718752663641/5000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (924377323/1000000000 : ℝ)) (n' := (416703249/500000000 : ℝ)) (Ab := (789549717/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (929803761/1000000000 : ℝ) ^ p + (993106259/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (929803761/1000000000 : ℝ)) (y := (993106259/1000000000 : ℝ)) (X := (499695977919/3125000000000 : ℝ)) (Y := (8400974621539/10000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993106259/1000000000 : ℝ) ^ p + (929803761/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993106259/1000000000 : ℝ)) (y := (929803761/1000000000 : ℝ)) (X := (8400974621539/10000000000000 : ℝ)) (Y := (499695977919/3125000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (96145501/50000000 : ℝ)) (τ := (929803761/1000000000 : ℝ)) (σ := (993106259/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (397690057/419890206 : ℝ) ^ p + (276680679/279926804 : ℝ) ^ p := by
    exact cert_lt (x := (397690057/419890206 : ℝ)) (y := (276680679/279926804 : ℝ)) (X := (2545665808509/10000000000000 : ℝ)) (Y := (3727167166219/5000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (929803761/1000000000 : ℝ)) (n' := (209945103/250000000 : ℝ)) (Ab := (397690057/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (116252567/125000000 : ℝ) ^ p + (993062041/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116252567/125000000 : ℝ)) (y := (993062041/1000000000 : ℝ)) (X := (16084435051839/100000000000000 : ℝ)) (Y := (83915582350827/100000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993062041/1000000000 : ℝ) ^ p + (116252567/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993062041/1000000000 : ℝ)) (y := (116252567/125000000 : ℝ)) (X := (83915582350827/100000000000000 : ℝ)) (Y := (16084435051839/100000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1923082577/1000000000 : ℝ)) (τ := (116252567/125000000 : ℝ)) (σ := (993062041/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795612295/840034277 : ℝ) ^ p + (830295902/840034277 : ℝ) ^ p := by
    exact cert_lt (x := (795612295/840034277 : ℝ)) (y := (830295902/840034277 : ℝ)) (X := (25450000729039/100000000000000 : ℝ)) (Y := (9318750090797/12500000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (116252567/125000000 : ℝ)) (n' := (840034277/1000000000 : ℝ)) (Ab := (159122459/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (930029109/1000000000 : ℝ) ^ p + (496530143/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (930029109/1000000000 : ℝ)) (y := (496530143/500000000 : ℝ)) (X := (2011021244623/12500000000000 : ℝ)) (Y := (83911847105481/100000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496530143/500000000 : ℝ) ^ p + (930029109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496530143/500000000 : ℝ)) (y := (930029109/1000000000 : ℝ)) (X := (83911847105481/100000000000000 : ℝ)) (Y := (2011021244623/12500000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (384617879/200000000 : ℝ)) (τ := (930029109/1000000000 : ℝ)) (σ := (496530143/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (198905369/210011079 : ℝ) ^ p + (276768647/280014772 : ℝ) ^ p := by
    exact cert_lt (x := (198905369/210011079 : ℝ)) (y := (276768647/280014772 : ℝ)) (X := (25449737169211/100000000000000 : ℝ)) (Y := (37275131959983/50000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (930029109/1000000000 : ℝ)) (n' := (210011079/250000000 : ℝ)) (Ab := (198905369/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (116253681/125000000 : ℝ) ^ p + (993060217/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116253681/125000000 : ℝ)) (y := (993060217/1000000000 : ℝ)) (X := (16088317662523/100000000000000 : ℝ)) (Y := (83911700252943/100000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993060217/1000000000 : ℝ) ^ p + (116253681/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993060217/1000000000 : ℝ)) (y := (116253681/125000000 : ℝ)) (X := (83911700252943/100000000000000 : ℝ)) (Y := (16088317662523/100000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (384617933/200000000 : ℝ)) (τ := (116253681/125000000 : ℝ)) (σ := (993060217/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (795621839/840044713 : ℝ) ^ p + (830306338/840044713 : ℝ) ^ p := by
    exact cert_lt (x := (795621839/840044713 : ℝ)) (y := (830306338/840044713 : ℝ)) (X := (25449726690539/100000000000000 : ℝ)) (Y := (4659392145503/6250000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (116253681/125000000 : ℝ)) (n' := (840044713/1000000000 : ℝ)) (Ab := (795621839/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (465014731/500000000 : ℝ) ^ p + (496530107/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465014731/500000000 : ℝ)) (y := (496530107/500000000 : ℝ)) (X := (3217664752497/20000000000000 : ℝ)) (Y := (16782338773611/20000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496530107/500000000 : ℝ) ^ p + (465014731/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496530107/500000000 : ℝ)) (y := (465014731/500000000 : ℝ)) (X := (16782338773611/20000000000000 : ℝ)) (Y := (3217664752497/20000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (480772419/250000000 : ℝ)) (τ := (465014731/500000000 : ℝ)) (σ := (496530107/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795621854/840044729 : ℝ) ^ p + (830306354/840044729 : ℝ) ^ p := by
    exact cert_lt (x := (795621854/840044729 : ℝ)) (y := (830306354/840044729 : ℝ)) (X := (25449726566549/100000000000000 : ℝ)) (Y := (74550274747517/100000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (465014731/500000000 : ℝ)) (n' := (840044729/1000000000 : ℝ)) (Ab := (397810927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (480772419/250000000 : ℝ)) (τ := (465014731/500000000 : ℝ)) (σ := (496530107/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (465014731/500000000 : ℝ)) (n' := (840044729/1000000000 : ℝ)) (Ab := (397810927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (480772419/250000000 : ℝ)) (τ := (465014731/500000000 : ℝ)) (σ := (496530107/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (465014731/500000000 : ℝ)) (n' := (840044729/1000000000 : ℝ)) (Ab := (397810927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (480772419/250000000 : ℝ)) (τ := (465014731/500000000 : ℝ)) (σ := (496530107/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (465014731/500000000 : ℝ)) (n' := (840044729/1000000000 : ℝ)) (Ab := (397810927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (480772419/250000000 : ℝ)) (τ := (465014731/500000000 : ℝ)) (σ := (496530107/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (465014731/500000000 : ℝ)) (n' := (840044729/1000000000 : ℝ)) (Ab := (397810927/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (480772419/250000000 : ℝ)) (τ := (465014731/500000000 : ℝ)) (σ := (496530107/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1664045939/1805936934 : ℝ) ^ p + (598732853/601978978 : ℝ) ^ p := by
    exact cert_lt (x := (1664045939/1805936934 : ℝ)) (y := (598732853/601978978 : ℝ)) (X := (12732246891637/100000000000000 : ℝ)) (Y := (43633876710549/50000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (558509519/597031533 : ℝ) ^ p + (394774897/398021022 : ℝ) ^ p := by
    exact cert_lt (x := (558509519/597031533 : ℝ)) (y := (394774897/398021022 : ℝ)) (X := (18638093780517/100000000000000 : ℝ)) (Y := (81361907035423/100000000000000 : ℝ)) 403 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496530107/500000000 : ℝ)) (U := (597031533/500000000 : ℝ)) (Ab := (1664045939/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (465014731/500000000 : ℝ)) (σ := (496530107/500000000 : ℝ)) (Ab := (558509519/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab133
