import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 79, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab079 (p : ℝ) (hpa : (495/16 : ℝ) ≤ p) (hpb : p ≤ (31 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (284961736841/21928500000000 : ℝ) (6644739/1000000000 : ℝ) (640000131571/4385700000000 : ℝ) (591/500 : ℝ) (977888537/500000000 : ℝ) (195568873/200000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158350891/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5463/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(563/1000 : ℝ)
      else (8287/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5753/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (284961736841/21928500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6644739/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (7377581/7812500 : ℝ) ^ p + (994031641/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7377581/7812500 : ℝ)) (y := (994031641/1000000000 : ℝ)) (X := (16937239852593/100000000000000 : ℝ)) (Y := (41531390519861/50000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994031641/1000000000 : ℝ) ^ p + (7377581/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (994031641/1000000000 : ℝ)) (y := (7377581/7812500 : ℝ)) (X := (41531390519861/50000000000000 : ℝ)) (Y := (16937239852593/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1938362009/1000000000 : ℝ)) (τ := (7377581/7812500 : ℝ)) (σ := (994031641/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (46024521/48391112 : ℝ) ^ p + (16948927/17079216 : ℝ) ^ p := by
    exact cert_lt (x := (46024521/48391112 : ℝ)) (y := (16948927/17079216 : ℝ)) (X := (10565837721507/50000000000000 : ℝ)) (Y := (78868325647727/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (7377581/7812500 : ℝ)) (n' := (54440001/62500000 : ℝ)) (Ab := (414220689/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (473724701/500000000 : ℝ) ^ p + (496660167/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (473724701/500000000 : ℝ)) (y := (496660167/500000000 : ℝ)) (X := (18760171586083/100000000000000 : ℝ)) (Y := (40619924042867/50000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496660167/500000000 : ℝ) ^ p + (473724701/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496660167/500000000 : ℝ)) (y := (473724701/500000000 : ℝ)) (X := (40619924042867/50000000000000 : ℝ)) (Y := (18760171586083/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (242596217/125000000 : ℝ)) (τ := (473724701/500000000 : ℝ)) (σ := (496660167/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (831719471/874588708 : ℝ) ^ p + (867943969/874588708 : ℝ) ^ p := by
    exact cert_lt (x := (831719471/874588708 : ℝ)) (y := (867943969/874588708 : ℝ)) (X := (21055380283841/100000000000000 : ℝ)) (Y := (78944620898239/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (473724701/500000000 : ℝ)) (n' := (218647177/250000000 : ℝ)) (Ab := (831719471/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (473764657/500000000 : ℝ) ^ p + (993300957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (473764657/500000000 : ℝ)) (y := (993300957/1000000000 : ℝ)) (X := (146947542513/781250000000 : ℝ)) (Y := (81190734579863/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993300957/1000000000 : ℝ) ^ p + (473764657/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993300957/1000000000 : ℝ)) (y := (473764657/500000000 : ℝ)) (X := (81190734579863/100000000000000 : ℝ)) (Y := (146947542513/781250000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1940830271/1000000000 : ℝ)) (τ := (473764657/500000000 : ℝ)) (σ := (993300957/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (207950828/218669869 : ℝ) ^ p + (868034737/874679476 : ℝ) ^ p := by
    exact cert_lt (x := (207950828/218669869 : ℝ)) (y := (868034737/874679476 : ℝ)) (X := (10526717993101/50000000000000 : ℝ)) (Y := (19736641295311/25000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (473764657/500000000 : ℝ)) (n' := (218669869/250000000 : ℝ)) (Ab := (51987707/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (947531351/1000000000 : ℝ) ^ p + (496650231/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (947531351/1000000000 : ℝ)) (y := (496650231/500000000 : ℝ)) (X := (2351317375657/12500000000000 : ℝ)) (Y := (81189480314979/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496650231/500000000 : ℝ) ^ p + (947531351/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496650231/500000000 : ℝ)) (y := (947531351/1000000000 : ℝ)) (X := (81189480314979/100000000000000 : ℝ)) (Y := (2351317375657/12500000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1940831813/1000000000 : ℝ)) (τ := (947531351/1000000000 : ℝ)) (σ := (496650231/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (831805448/874681789 : ℝ) ^ p + (868037050/874681789 : ℝ) ^ p := by
    exact cert_lt (x := (831805448/874681789 : ℝ)) (y := (868037050/874681789 : ℝ)) (X := (4210677213919/20000000000000 : ℝ)) (Y := (9868326840233/12500000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (947531351/1000000000 : ℝ)) (n' := (874681789/1000000000 : ℝ)) (Ab := (103975681/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (473765701/500000000 : ℝ) ^ p + (19866009/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (473765701/500000000 : ℝ)) (y := (19866009/20000000 : ℝ)) (X := (9405285195769/50000000000000 : ℝ)) (Y := (8118944990879/10000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (19866009/20000000 : ℝ) ^ p + (473765701/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (19866009/20000000 : ℝ)) (y := (473765701/500000000 : ℝ)) (X := (8118944990879/10000000000000 : ℝ)) (Y := (9405285195769/50000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (485207963/250000000 : ℝ)) (τ := (473765701/500000000 : ℝ)) (σ := (19866009/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (831805502/874681847 : ℝ) ^ p + (868037108/874681847 : ℝ) ^ p := by
    exact cert_lt (x := (831805502/874681847 : ℝ)) (y := (868037108/874681847 : ℝ)) (X := (21053385161881/100000000000000 : ℝ)) (Y := (631572927713/800000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (473765701/500000000 : ℝ)) (n' := (874681847/1000000000 : ℝ)) (Ab := (415902751/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (947531403/1000000000 : ℝ) ^ p + (19866009/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (947531403/1000000000 : ℝ)) (y := (19866009/20000000 : ℝ)) (X := (4702642751739/25000000000000 : ℝ)) (Y := (8118944990879/10000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (19866009/20000000 : ℝ) ^ p + (947531403/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19866009/20000000 : ℝ)) (y := (947531403/1000000000 : ℝ)) (X := (8118944990879/10000000000000 : ℝ)) (Y := (4702642751739/25000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1940831853/1000000000 : ℝ)) (τ := (947531403/1000000000 : ℝ)) (σ := (19866009/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (277268501/291560616 : ℝ) ^ p + (289345703/291560616 : ℝ) ^ p := by
    exact cert_lt (x := (277268501/291560616 : ℝ)) (y := (289345703/291560616 : ℝ)) (X := (10526692600171/50000000000000 : ℝ)) (Y := (78946615985543/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (947531403/1000000000 : ℝ)) (n' := (109335231/125000000 : ℝ)) (Ab := (831805503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1940831853/1000000000 : ℝ)) (τ := (947531403/1000000000 : ℝ)) (σ := (19866009/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (947531403/1000000000 : ℝ)) (n' := (109335231/125000000 : ℝ)) (Ab := (831805503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1940831853/1000000000 : ℝ)) (τ := (947531403/1000000000 : ℝ)) (σ := (19866009/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (947531403/1000000000 : ℝ)) (n' := (109335231/125000000 : ℝ)) (Ab := (831805503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1940831853/1000000000 : ℝ)) (τ := (947531403/1000000000 : ℝ)) (σ := (19866009/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (947531403/1000000000 : ℝ)) (n' := (109335231/125000000 : ℝ)) (Ab := (831805503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1940831853/1000000000 : ℝ)) (τ := (947531403/1000000000 : ℝ)) (σ := (19866009/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (947531403/1000000000 : ℝ)) (n' := (109335231/125000000 : ℝ)) (Ab := (831805503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1940831853/1000000000 : ℝ)) (τ := (947531403/1000000000 : ℝ)) (σ := (19866009/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1713031577/1841649109 : ℝ) ^ p + (1835004370/1841649109 : ℝ) ^ p := by
    exact cert_lt (x := (1713031577/1841649109 : ℝ)) (y := (1835004370/1841649109 : ℝ)) (X := (5300086107797/50000000000000 : ℝ)) (Y := (22349957031109/25000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1092587396/1158350891 : ℝ) ^ p + (1151706152/1158350891 : ℝ) ^ p := by
    exact cert_lt (x := (1092587396/1158350891 : ℝ)) (y := (1151706152/1158350891 : ℝ)) (X := (8167093513511/50000000000000 : ℝ)) (Y := (83665813556373/100000000000000 : ℝ)) 31 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (19866009/20000000 : ℝ)) (U := (1158350891/1000000000 : ℝ)) (Ab := (1713031577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (947531403/1000000000 : ℝ)) (σ := (19866009/20000000 : ℝ)) (Ab := (273146849/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab079
