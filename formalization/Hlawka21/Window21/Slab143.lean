import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 143, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab143 (p : ℝ) (hpa : (815/32 : ℝ) ≤ p) (hpb : p ≤ (51/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (207897424373/11124750000000 : ℝ) (9601707/1000000000 : ℝ) (800000133497/4449900000000 : ℝ) (3033/2500 : ℝ) (973183871/500000000 : ℝ) (243287853/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597094663/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(559/500 : ℝ) ≤ X j i ∧ X j i ≤ -(4679/10000 : ℝ)
      else (1957/2500 : ℝ) ≤ X j i ∧ X j i ≤ (593/500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (207897424373/11124750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9601707/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (462674597/500000000 : ℝ) ^ p + (248545059/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (462674597/500000000 : ℝ)) (y := (248545059/250000000 : ℝ)) (X := (6914552928293/50000000000000 : ℝ)) (Y := (43085456438417/50000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248545059/250000000 : ℝ) ^ p + (462674597/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248545059/250000000 : ℝ)) (y := (462674597/500000000 : ℝ)) (X := (43085456438417/50000000000000 : ℝ)) (Y := (6914552928293/50000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (191952943/100000000 : ℝ)) (τ := (462674597/500000000 : ℝ)) (σ := (248545059/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (790834819/834293242 : ℝ) ^ p + (824691535/834293242 : ℝ) ^ p := by
    exact cert_lt (x := (790834819/834293242 : ℝ)) (y := (824691535/834293242 : ℝ)) (X := (25559946596269/100000000000000 : ℝ)) (Y := (37220027301549/50000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462674597/500000000 : ℝ)) (n' := (417146621/500000000 : ℝ)) (Ab := (790834819/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (930733039/1000000000 : ℝ) ^ p + (62073137/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (930733039/1000000000 : ℝ)) (y := (62073137/62500000 : ℝ)) (X := (4008490340947/25000000000000 : ℝ)) (Y := (83966055840013/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (62073137/62500000 : ℝ) ^ p + (930733039/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62073137/62500000 : ℝ)) (y := (930733039/1000000000 : ℝ)) (X := (83966055840013/100000000000000 : ℝ)) (Y := (4008490340947/25000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1923903231/1000000000 : ℝ)) (τ := (930733039/1000000000 : ℝ)) (σ := (62073137/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (398308527/420304129 : ℝ) ^ p + (831006551/840608258 : ℝ) ^ p := by
    exact cert_lt (x := (398308527/420304129 : ℝ)) (y := (831006551/840608258 : ℝ)) (X := (25393739465849/100000000000000 : ℝ)) (Y := (74606261857469/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (930733039/1000000000 : ℝ)) (n' := (420304129/500000000 : ℝ)) (Ab := (398308527/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (465472279/500000000 : ℝ) ^ p + (248281737/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (465472279/500000000 : ℝ)) (y := (248281737/250000000 : ℝ)) (X := (806356983241/5000000000000 : ℝ)) (Y := (83872877603157/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248281737/250000000 : ℝ) ^ p + (465472279/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248281737/250000000 : ℝ)) (y := (465472279/500000000 : ℝ)) (X := (83872877603157/100000000000000 : ℝ)) (Y := (806356983241/5000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (962035753/500000000 : ℝ)) (τ := (465472279/500000000 : ℝ)) (σ := (248281737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (796843519/840855628 : ℝ) ^ p + (831253921/840855628 : ℝ) ^ p := by
    exact cert_lt (x := (796843519/840855628 : ℝ)) (y := (831253921/840855628 : ℝ)) (X := (25387272188891/100000000000000 : ℝ)) (Y := (596901830893/800000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (465472279/500000000 : ℝ)) (n' := (210213907/250000000 : ℝ)) (Ab := (796843519/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (465476393/500000000 : ℝ) ^ p + (49656263/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (465476393/500000000 : ℝ)) (y := (49656263/50000000 : ℝ)) (X := (16130774753537/100000000000000 : ℝ)) (Y := (2096731061743/2500000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49656263/50000000 : ℝ) ^ p + (465476393/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (49656263/50000000 : ℝ)) (y := (465476393/500000000 : ℝ)) (X := (2096731061743/2500000000000 : ℝ)) (Y := (16130774753537/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (962039023/500000000 : ℝ)) (τ := (465476393/500000000 : ℝ)) (σ := (49656263/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (796852327/840865249 : ℝ) ^ p + (831263542/840865249 : ℝ) ^ p := by
    exact cert_lt (x := (796852327/840865249 : ℝ)) (y := (831263542/840865249 : ℝ)) (X := (25387020814821/100000000000000 : ℝ)) (Y := (74612980317831/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (465476393/500000000 : ℝ)) (n' := (840865249/1000000000 : ℝ)) (Ab := (796852327/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465476553/500000000 : ℝ) ^ p + (198625039/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (465476553/500000000 : ℝ)) (y := (198625039/200000000 : ℝ)) (X := (16130916143819/100000000000000 : ℝ)) (Y := (83869102494267/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198625039/200000000 : ℝ) ^ p + (465476553/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198625039/200000000 : ℝ)) (y := (465476553/500000000 : ℝ)) (X := (83869102494267/100000000000000 : ℝ)) (Y := (16130916143819/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1924078301/1000000000 : ℝ)) (τ := (465476553/500000000 : ℝ)) (σ := (198625039/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (398426335/420432812 : ℝ) ^ p + (831263917/840865624 : ℝ) ^ p := by
    exact cert_lt (x := (398426335/420432812 : ℝ)) (y := (831263917/840865624 : ℝ)) (X := (507740215281/2000000000000 : ℝ)) (Y := (186532475297/250000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465476553/500000000 : ℝ)) (n' := (105108203/125000000 : ℝ)) (Ab := (79685267/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (930953119/1000000000 : ℝ) ^ p + (124140649/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (930953119/1000000000 : ℝ)) (y := (124140649/125000000 : ℝ)) (X := (1008182617989/6250000000000 : ℝ)) (Y := (83869096033867/100000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124140649/125000000 : ℝ) ^ p + (930953119/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124140649/125000000 : ℝ)) (y := (930953119/1000000000 : ℝ)) (X := (83869096033867/100000000000000 : ℝ)) (Y := (1008182617989/6250000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1924078311/1000000000 : ℝ)) (τ := (930953119/1000000000 : ℝ)) (σ := (124140649/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (796852684/840865639 : ℝ) ^ p + (831263932/840865639 : ℝ) ^ p := by
    exact cert_lt (x := (796852684/840865639 : ℝ)) (y := (831263932/840865639 : ℝ)) (X := (25387010589493/100000000000000 : ℝ)) (Y := (37306495255419/50000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (930953119/1000000000 : ℝ)) (n' := (840865639/1000000000 : ℝ)) (Ab := (199213171/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1924078311/1000000000 : ℝ)) (τ := (930953119/1000000000 : ℝ)) (σ := (124140649/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (930953119/1000000000 : ℝ)) (n' := (840865639/1000000000 : ℝ)) (Ab := (199213171/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1924078311/1000000000 : ℝ)) (τ := (930953119/1000000000 : ℝ)) (σ := (124140649/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (930953119/1000000000 : ℝ)) (n' := (840865639/1000000000 : ℝ)) (Ab := (199213171/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1924078311/1000000000 : ℝ)) (τ := (930953119/1000000000 : ℝ)) (σ := (124140649/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (930953119/1000000000 : ℝ)) (n' := (840865639/1000000000 : ℝ)) (Ab := (199213171/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1924078311/1000000000 : ℝ)) (τ := (930953119/1000000000 : ℝ)) (σ := (124140649/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (930953119/1000000000 : ℝ)) (n' := (840865639/1000000000 : ℝ)) (Ab := (199213171/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1924078311/1000000000 : ℝ)) (τ := (930953119/1000000000 : ℝ)) (σ := (124140649/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (832745522/902905337 : ℝ) ^ p + (1796208967/1805810674 : ℝ) ^ p := by
    exact cert_lt (x := (832745522/902905337 : ℝ)) (y := (1796208967/1805810674 : ℝ)) (X := (6355609338031/50000000000000 : ℝ)) (Y := (21822195383321/25000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1117973009/1194189326 : ℝ) ^ p + (1184587619/1194189326 : ℝ) ^ p := by
    exact cert_lt (x := (1117973009/1194189326 : ℝ)) (y := (1184587619/1194189326 : ℝ)) (X := (18605117029531/100000000000000 : ℝ)) (Y := (40697441813011/50000000000000 : ℝ)) 51 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124140649/125000000 : ℝ)) (U := (597094663/500000000 : ℝ)) (Ab := (416372761/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (930953119/1000000000 : ℝ)) (σ := (124140649/125000000 : ℝ)) (Ab := (1117973009/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab143
