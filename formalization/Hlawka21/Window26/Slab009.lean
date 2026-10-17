import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 9, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab009 (p : ℝ) (hpa : (425/16 : ℝ) ≤ p) (hpb : p ≤ (213/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (7257837539/470687500000 : ℝ) (3956831/500000000 : ℝ) (128000022593/753100000000 : ℝ) (591/500 : ℝ) (974302259/500000000 : ℝ) (487121289/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (577859641/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10807/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1371/2500 : ℝ)
      else (4069/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1147/1000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (7257837539/470687500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3956831/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (934704767/1000000000 : ℝ) ^ p + (248305213/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (934704767/1000000000 : ℝ)) (y := (248305213/250000000 : ℝ)) (X := (8282805017913/50000000000000 : ℝ)) (Y := (83434408049937/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248305213/250000000 : ℝ) ^ p + (934704767/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248305213/250000000 : ℝ)) (y := (934704767/1000000000 : ℝ)) (X := (83434408049937/100000000000000 : ℝ)) (Y := (8282805017913/50000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1927925619/1000000000 : ℝ)) (τ := (934704767/1000000000 : ℝ)) (σ := (248305213/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (815200627/863281667 : ℝ) ^ p + (855368005/863281667 : ℝ) ^ p := by
    exact cert_lt (x := (815200627/863281667 : ℝ)) (y := (855368005/863281667 : ℝ)) (X := (434897234699/2000000000000 : ℝ)) (Y := (15651027828823/20000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (934704767/1000000000 : ℝ)) (n' := (863281667/1000000000 : ℝ)) (Ab := (815200627/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (18763589/20000000 : ℝ) ^ p + (248111009/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (18763589/20000000 : ℝ)) (y := (248111009/250000000 : ℝ)) (X := (9142869364297/50000000000000 : ℝ)) (Y := (4085713904199/5000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248111009/250000000 : ℝ) ^ p + (18763589/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (248111009/250000000 : ℝ)) (y := (18763589/20000000 : ℝ)) (X := (4085713904199/5000000000000 : ℝ)) (Y := (9142869364297/50000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (965311743/500000000 : ℝ)) (τ := (18763589/20000000 : ℝ)) (σ := (248111009/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (818861905/867292777 : ℝ) ^ p + (859379115/867292777 : ℝ) ^ p := by
    exact cert_lt (x := (818861905/867292777 : ℝ)) (y := (859379115/867292777 : ℝ)) (X := (2706957791169/12500000000000 : ℝ)) (Y := (78344338954543/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (18763589/20000000 : ℝ)) (n' := (867292777/1000000000 : ℝ)) (Ab := (163772381/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (938287737/1000000000 : ℝ) ^ p + (248104589/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (938287737/1000000000 : ℝ)) (y := (248104589/250000000 : ℝ)) (X := (9171008122487/50000000000000 : ℝ)) (Y := (16331600174169/20000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248104589/250000000 : ℝ) ^ p + (938287737/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248104589/250000000 : ℝ)) (y := (938287737/1000000000 : ℝ)) (X := (16331600174169/20000000000000 : ℝ)) (Y := (9171008122487/50000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1930706093/1000000000 : ℝ)) (τ := (938287737/1000000000 : ℝ)) (σ := (248104589/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (818975781/867417545 : ℝ) ^ p + (859503883/867417545 : ℝ) ^ p := by
    exact cert_lt (x := (818975781/867417545 : ℝ)) (y := (859503883/867417545 : ℝ)) (X := (21652899359423/100000000000000 : ℝ)) (Y := (78347101900057/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (938287737/1000000000 : ℝ)) (n' := (173483509/200000000 : ℝ)) (Ab := (818975781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (234572773/250000000 : ℝ) ^ p + (992417559/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (234572773/250000000 : ℝ)) (y := (992417559/1000000000 : ℝ)) (X := (18343762521721/100000000000000 : ℝ)) (Y := (81656254858041/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992417559/1000000000 : ℝ) ^ p + (234572773/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992417559/1000000000 : ℝ)) (y := (234572773/250000000 : ℝ)) (X := (81656254858041/100000000000000 : ℝ)) (Y := (18343762521721/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1930708651/1000000000 : ℝ)) (τ := (234572773/250000000 : ℝ)) (σ := (992417559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (818979309/867421411 : ℝ) ^ p + (859507749/867421411 : ℝ) ^ p := by
    exact cert_lt (x := (818979309/867421411 : ℝ)) (y := (859507749/867421411 : ℝ)) (X := (10826406704717/50000000000000 : ℝ)) (Y := (78347187500133/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (234572773/250000000 : ℝ)) (n' := (867421411/1000000000 : ℝ)) (Ab := (818979309/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (234572799/250000000 : ℝ) ^ p + (496208767/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (234572799/250000000 : ℝ)) (y := (496208767/500000000 : ℝ)) (X := (9171908328127/50000000000000 : ℝ)) (Y := (81656200090341/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496208767/500000000 : ℝ) ^ p + (234572799/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496208767/500000000 : ℝ)) (y := (234572799/250000000 : ℝ)) (X := (81656200090341/100000000000000 : ℝ)) (Y := (9171908328127/50000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (193070873/100000000 : ℝ)) (τ := (234572799/250000000 : ℝ)) (σ := (496208767/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (409489709/433710765 : ℝ) ^ p + (429753934/433710765 : ℝ) ^ p := by
    exact cert_lt (x := (409489709/433710765 : ℝ)) (y := (429753934/433710765 : ℝ)) (X := (676650345257/3125000000000 : ℝ)) (Y := (4896699383437/6250000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (234572799/250000000 : ℝ)) (n' := (86742153/100000000 : ℝ)) (Ab := (409489709/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (469145599/500000000 : ℝ) ^ p + (496208767/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (469145599/500000000 : ℝ)) (y := (496208767/500000000 : ℝ)) (X := (2292977212163/12500000000000 : ℝ)) (Y := (81656200090341/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496208767/500000000 : ℝ) ^ p + (469145599/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496208767/500000000 : ℝ)) (y := (469145599/500000000 : ℝ)) (X := (81656200090341/100000000000000 : ℝ)) (Y := (2292977212163/12500000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (482677183/250000000 : ℝ)) (τ := (469145599/500000000 : ℝ)) (σ := (496208767/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (818979421/867421533 : ℝ) ^ p + (859507871/867421533 : ℝ) ^ p := by
    exact cert_lt (x := (818979421/867421533 : ℝ)) (y := (859507871/867421533 : ℝ)) (X := (270660139577/1250000000000 : ℝ)) (Y := (78347190201417/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (469145599/500000000 : ℝ)) (n' := (867421533/1000000000 : ℝ)) (Ab := (818979421/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (482677183/250000000 : ℝ)) (τ := (469145599/500000000 : ℝ)) (σ := (496208767/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (469145599/500000000 : ℝ)) (n' := (867421533/1000000000 : ℝ)) (Ab := (818979421/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (482677183/250000000 : ℝ)) (τ := (469145599/500000000 : ℝ)) (σ := (496208767/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (469145599/500000000 : ℝ)) (n' := (867421533/1000000000 : ℝ)) (Ab := (818979421/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (482677183/250000000 : ℝ)) (τ := (469145599/500000000 : ℝ)) (σ := (496208767/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (469145599/500000000 : ℝ)) (n' := (867421533/1000000000 : ℝ)) (Ab := (818979421/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (482677183/250000000 : ℝ)) (τ := (469145599/500000000 : ℝ)) (σ := (496208767/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (469145599/500000000 : ℝ)) (n' := (867421533/1000000000 : ℝ)) (Ab := (818979421/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (482677183/250000000 : ℝ)) (τ := (469145599/500000000 : ℝ)) (σ := (496208767/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (848244286/922140359 : ℝ) ^ p + (918183528/922140359 : ℝ) ^ p := by
    exact cert_lt (x := (848244286/922140359 : ℝ)) (y := (918183528/922140359 : ℝ)) (X := (10818054795883/100000000000000 : ℝ)) (Y := (17836389086839/20000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1080628139/1155719282 : ℝ) ^ p + (573902810/577859641 : ℝ) ^ p := by
    exact cert_lt (x := (1080628139/1155719282 : ℝ)) (y := (573902810/577859641 : ℝ)) (X := (104488068813/625000000000 : ℝ)) (Y := (83281909450073/100000000000000 : ℝ)) 213 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496208767/500000000 : ℝ)) (U := (577859641/500000000 : ℝ)) (Ab := (424122143/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (469145599/500000000 : ℝ)) (σ := (496208767/500000000 : ℝ)) (Ab := (1080628139/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab009
