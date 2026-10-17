import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 120, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab120 (p : ℝ) (hpa : (99/4 : ℝ) ≤ p) (hpb : p ≤ (793/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (26075277979/1351350000000 : ℝ) (248047/25000000 : ℝ) (500000081081/2702700000000 : ℝ) (3033/2500 : ℝ) (972416927/500000000 : ℝ) (121547823/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596949169/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5579/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2321/5000 : ℝ)
      else (7791/10000 : ℝ) ≤ X j i ∧ X j i ≤ (741/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (26075277979/1351350000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (248047/25000000 : ℝ) := by norm_num
  have pc0 : 1 < (184615107/200000000 : ℝ) ^ p + (994045327/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184615107/200000000 : ℝ)) (y := (994045327/1000000000 : ℝ)) (X := (6878684250943/50000000000000 : ℝ)) (Y := (43121325451709/50000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994045327/1000000000 : ℝ) ^ p + (184615107/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (994045327/1000000000 : ℝ)) (y := (184615107/200000000 : ℝ)) (X := (43121325451709/50000000000000 : ℝ)) (Y := (6878684250943/50000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958560431/500000000 : ℝ)) (τ := (184615107/200000000 : ℝ)) (σ := (994045327/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (787829866/832214187 : ℝ) ^ p + (822292307/832214187 : ℝ) ^ p := by
    exact cert_lt (x := (787829866/832214187 : ℝ)) (y := (822292307/832214187 : ℝ)) (X := (6428060869883/25000000000000 : ℝ)) (Y := (37143878685757/50000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184615107/200000000 : ℝ)) (n' := (832214187/1000000000 : ℝ)) (Ab := (393914933/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185711521/200000000 : ℝ) ^ p + (496510777/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (185711521/200000000 : ℝ)) (y := (496510777/500000000 : ℝ)) (X := (3186347158537/20000000000000 : ℝ)) (Y := (84068281329291/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496510777/500000000 : ℝ) ^ p + (185711521/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496510777/500000000 : ℝ)) (y := (185711521/200000000 : ℝ)) (X := (84068281329291/100000000000000 : ℝ)) (Y := (3186347158537/20000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1921579159/1000000000 : ℝ)) (τ := (185711521/200000000 : ℝ)) (σ := (496510777/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (793723345/838665563 : ℝ) ^ p + (828743683/838665563 : ℝ) ^ p := by
    exact cert_lt (x := (793723345/838665563 : ℝ)) (y := (828743683/838665563 : ℝ)) (X := (6385295779677/25000000000000 : ℝ)) (Y := (9307352302571/12500000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185711521/200000000 : ℝ)) (n' := (838665563/1000000000 : ℝ)) (Ab := (158744669/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (928781491/1000000000 : ℝ) ^ p + (39719041/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (928781491/1000000000 : ℝ)) (y := (39719041/40000000 : ℝ)) (X := (801360103563/5000000000000 : ℝ)) (Y := (83972815474247/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39719041/40000000 : ℝ) ^ p + (928781491/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39719041/40000000 : ℝ)) (y := (928781491/1000000000 : ℝ)) (X := (83972815474247/100000000000000 : ℝ)) (Y := (801360103563/5000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (480439379/250000000 : ℝ)) (τ := (928781491/1000000000 : ℝ)) (σ := (39719041/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (793963267/838928240 : ℝ) ^ p + (1219127/1233718 : ℝ) ^ p := by
    exact cert_lt (x := (793963267/838928240 : ℝ)) (y := (1219127/1233718 : ℝ)) (X := (6383566367317/25000000000000 : ℝ)) (Y := (18616433902543/25000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (928781491/1000000000 : ℝ)) (n' := (10486603/12500000 : ℝ)) (Ab := (793963267/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (464395271/500000000 : ℝ) ^ p + (496487089/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (464395271/500000000 : ℝ)) (y := (496487089/500000000 : ℝ)) (X := (16031072991821/100000000000000 : ℝ)) (Y := (83968944855009/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496487089/500000000 : ℝ) ^ p + (464395271/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496487089/500000000 : ℝ)) (y := (464395271/500000000 : ℝ)) (X := (83968944855009/100000000000000 : ℝ)) (Y := (16031072991821/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (24022059/12500000 : ℝ)) (τ := (464395271/500000000 : ℝ)) (σ := (496487089/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (264657655/279646286 : ℝ) ^ p + (414508489/419469429 : ℝ) ^ p := by
    exact cert_lt (x := (264657655/279646286 : ℝ)) (y := (414508489/419469429 : ℝ)) (X := (12467766513/48828125000 : ℝ)) (Y := (74466015140539/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (464395271/500000000 : ℝ)) (n' := (419469429/500000000 : ℝ)) (Ab := (158794593/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (232197727/250000000 : ℝ) ^ p + (992974103/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232197727/250000000 : ℝ)) (y := (992974103/1000000000 : ℝ)) (X := (4007807385281/25000000000000 : ℝ)) (Y := (83968787686757/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992974103/1000000000 : ℝ) ^ p + (232197727/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992974103/1000000000 : ℝ)) (y := (232197727/250000000 : ℝ)) (X := (83968787686757/100000000000000 : ℝ)) (Y := (4007807385281/25000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1921765011/1000000000 : ℝ)) (τ := (232197727/250000000 : ℝ)) (σ := (992974103/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (396986679/419469644 : ℝ) ^ p + (103627176/104867411 : ℝ) ^ p := by
    exact cert_lt (x := (396986679/419469644 : ℝ)) (y := (103627176/104867411 : ℝ)) (X := (5106794939791/20000000000000 : ℝ)) (Y := (74466026460627/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (232197727/250000000 : ℝ)) (n' := (104867411/125000000 : ℝ)) (Ab := (396986679/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (928790923/1000000000 : ℝ) ^ p + (9929741/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (928790923/1000000000 : ℝ)) (y := (9929741/10000000 : ℝ)) (X := (1603123595711/10000000000000 : ℝ)) (Y := (83968781400033/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (9929741/10000000 : ℝ) ^ p + (928790923/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (9929741/10000000 : ℝ)) (y := (928790923/1000000000 : ℝ)) (X := (83968781400033/100000000000000 : ℝ)) (Y := (1603123595711/10000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921765023/1000000000 : ℝ)) (τ := (928790923/1000000000 : ℝ)) (σ := (9929741/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (793973374/838939305 : ℝ) ^ p + (165803485/167787861 : ℝ) ^ p := by
    exact cert_lt (x := (793973374/838939305 : ℝ)) (y := (165803485/167787861 : ℝ)) (X := (5106794925633/20000000000000 : ℝ)) (Y := (14893205381633/20000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (928790923/1000000000 : ℝ)) (n' := (167787861/200000000 : ℝ)) (Ab := (396986687/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1921765023/1000000000 : ℝ)) (τ := (928790923/1000000000 : ℝ)) (σ := (9929741/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (928790923/1000000000 : ℝ)) (n' := (167787861/200000000 : ℝ)) (Ab := (396986687/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1921765023/1000000000 : ℝ)) (τ := (928790923/1000000000 : ℝ)) (σ := (9929741/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (928790923/1000000000 : ℝ)) (n' := (167787861/200000000 : ℝ)) (Ab := (396986687/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1921765023/1000000000 : ℝ)) (τ := (928790923/1000000000 : ℝ)) (σ := (9929741/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (928790923/1000000000 : ℝ)) (n' := (167787861/200000000 : ℝ)) (Ab := (396986687/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1921765023/1000000000 : ℝ)) (τ := (928790923/1000000000 : ℝ)) (σ := (9929741/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (928790923/1000000000 : ℝ)) (n' := (167787861/200000000 : ℝ)) (Ab := (396986687/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1921765023/1000000000 : ℝ)) (τ := (928790923/1000000000 : ℝ)) (σ := (9929741/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (831057497/903050831 : ℝ) ^ p + (898089891/903050831 : ℝ) ^ p := by
    exact cert_lt (x := (831057497/903050831 : ℝ)) (y := (898089891/903050831 : ℝ)) (X := (6380204898961/50000000000000 : ℝ)) (Y := (3489583622237/4000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (557875374/596949169 : ℝ) ^ p + (34822837/35114657 : ℝ) ^ p := by
    exact cert_lt (x := (557875374/596949169 : ℝ)) (y := (34822837/35114657 : ℝ)) (X := (18682167482977/100000000000000 : ℝ)) (Y := (81317832936471/100000000000000 : ℝ)) 793 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (9929741/10000000 : ℝ)) (U := (596949169/500000000 : ℝ)) (Ab := (831057497/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (928790923/1000000000 : ℝ)) (σ := (9929741/10000000 : ℝ)) (Ab := (278937687/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab120
