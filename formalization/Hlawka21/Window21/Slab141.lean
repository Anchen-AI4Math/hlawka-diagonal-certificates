import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 141, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab141 (p : ℝ) (hpa : (813/32 : ℝ) ≤ p) (hpb : p ≤ (407/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2079571623149/110974500000000 : ℝ) (4814369/500000000 : ℝ) (4000000665847/22194900000000 : ℝ) (3033/2500 : ℝ) (973118877/500000000 : ℝ) (973086261/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (74635257/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(5589/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1169/2500 : ℝ)
      else (313/400 : ℝ) ≤ X j i ∧ X j i ≤ (593/500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2079571623149/110974500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4814369/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (462578407/500000000 : ℝ) ^ p + (497084369/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (462578407/500000000 : ℝ)) (y := (497084369/500000000 : ℝ)) (X := (13823022433019/100000000000000 : ℝ)) (Y := (86176997067763/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497084369/500000000 : ℝ) ^ p + (462578407/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (497084369/500000000 : ℝ)) (y := (462578407/500000000 : ℝ)) (X := (86176997067763/100000000000000 : ℝ)) (Y := (13823022433019/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (119957847/62500000 : ℝ)) (τ := (462578407/500000000 : ℝ)) (σ := (497084369/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (263526787/278039314 : ℝ) ^ p + (58892086/59579853 : ℝ) ^ p := by
    exact cert_lt (x := (263526787/278039314 : ℝ)) (y := (58892086/59579853 : ℝ)) (X := (6393200803899/25000000000000 : ℝ)) (Y := (37213598831253/50000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462578407/500000000 : ℝ)) (n' := (417058971/500000000 : ℝ)) (Ab := (790580361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (465274581/500000000 : ℝ) ^ p + (99315749/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (465274581/500000000 : ℝ)) (y := (99315749/100000000 : ℝ)) (X := (16025312695321/100000000000000 : ℝ)) (Y := (83974704472353/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99315749/100000000 : ℝ) ^ p + (465274581/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99315749/100000000 : ℝ)) (y := (465274581/500000000 : ℝ)) (X := (83974704472353/100000000000000 : ℝ)) (Y := (16025312695321/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (480926663/250000000 : ℝ)) (τ := (465274581/500000000 : ℝ)) (σ := (99315749/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (796372201/840444688 : ℝ) ^ p + (415407975/420222344 : ℝ) ^ p := by
    exact cert_lt (x := (796372201/840444688 : ℝ)) (y := (415407975/420222344 : ℝ)) (X := (25406182895787/100000000000000 : ℝ)) (Y := (582764204111/781250000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (465274581/500000000 : ℝ)) (n' := (52527793/62500000 : ℝ)) (Ab := (796372201/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (465380859/500000000 : ℝ) ^ p + (496557027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465380859/500000000 : ℝ)) (y := (496557027/500000000 : ℝ)) (X := (2014835880231/12500000000000 : ℝ)) (Y := (41940665603421/50000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496557027/500000000 : ℝ) ^ p + (465380859/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496557027/500000000 : ℝ)) (y := (465380859/500000000 : ℝ)) (X := (41940665603421/50000000000000 : ℝ)) (Y := (2014835880231/12500000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (480968943/250000000 : ℝ)) (τ := (465380859/500000000 : ℝ)) (σ := (496557027/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (398299897/420346669 : ℝ) ^ p + (415532300/420346669 : ℝ) ^ p := by
    exact cert_lt (x := (398299897/420346669 : ℝ)) (y := (415532300/420346669 : ℝ)) (X := (6349919734553/25000000000000 : ℝ)) (Y := (74600322580341/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (465380859/500000000 : ℝ)) (n' := (420346669/500000000 : ℝ)) (Ab := (398299897/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (465385007/500000000 : ℝ) ^ p + (993112353/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465385007/500000000 : ℝ)) (y := (993112353/1000000000 : ℝ)) (X := (8061170996677/50000000000000 : ℝ)) (Y := (41938838320303/50000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993112353/1000000000 : ℝ) ^ p + (465385007/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993112353/1000000000 : ℝ)) (y := (465385007/500000000 : ℝ)) (X := (41938838320303/50000000000000 : ℝ)) (Y := (8061170996677/50000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1923882367/1000000000 : ℝ)) (τ := (465385007/500000000 : ℝ)) (σ := (993112353/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (398304338/420351521 : ℝ) ^ p + (415537152/420351521 : ℝ) ^ p := by
    exact cert_lt (x := (398304338/420351521 : ℝ)) (y := (415537152/420351521 : ℝ)) (X := (2539942504691/10000000000000 : ℝ)) (Y := (18650144090261/25000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (465385007/500000000 : ℝ)) (n' := (420351521/500000000 : ℝ)) (Ab := (199152169/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465385169/500000000 : ℝ) ^ p + (496556143/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465385169/500000000 : ℝ)) (y := (496556143/500000000 : ℝ)) (X := (4030621188379/25000000000000 : ℝ)) (Y := (20969383173877/25000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496556143/500000000 : ℝ) ^ p + (465385169/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496556143/500000000 : ℝ)) (y := (465385169/500000000 : ℝ)) (X := (20969383173877/25000000000000 : ℝ)) (Y := (4030621188379/25000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (15030333/7812500 : ℝ)) (τ := (465385169/500000000 : ℝ)) (σ := (496556143/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (796609023/840703421 : ℝ) ^ p + (831074683/840703421 : ℝ) ^ p := by
    exact cert_lt (x := (796609023/840703421 : ℝ)) (y := (831074683/840703421 : ℝ)) (X := (50798830431/200000000000 : ℝ)) (Y := (9325073284077/12500000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465385169/500000000 : ℝ)) (n' := (840703421/1000000000 : ℝ)) (Ab := (796609023/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (18615407/20000000 : ℝ) ^ p + (248278071/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (18615407/20000000 : ℝ)) (y := (248278071/250000000 : ℝ)) (X := (2015311255119/12500000000000 : ℝ)) (Y := (83877528398643/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248278071/250000000 : ℝ) ^ p + (18615407/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (248278071/250000000 : ℝ)) (y := (18615407/20000000 : ℝ)) (X := (83877528398643/100000000000000 : ℝ)) (Y := (2015311255119/12500000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (961941317/500000000 : ℝ)) (τ := (18615407/20000000 : ℝ)) (σ := (248278071/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (159321807/168140687 : ℝ) ^ p + (831074697/840703435 : ℝ) ^ p := by
    exact cert_lt (x := (159321807/168140687 : ℝ)) (y := (831074697/840703435 : ℝ)) (X := (5079882837787/20000000000000 : ℝ)) (Y := (74600586638743/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (18615407/20000000 : ℝ)) (n' := (168140687/200000000 : ℝ)) (Ab := (159321807/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (58173147/62500000 : ℝ) ^ p + (993112283/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (58173147/62500000 : ℝ)) (y := (993112283/1000000000 : ℝ)) (X := (1007655682637/6250000000000 : ℝ)) (Y := (83877526250211/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993112283/1000000000 : ℝ) ^ p + (58173147/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (993112283/1000000000 : ℝ)) (y := (58173147/62500000 : ℝ)) (X := (83877526250211/100000000000000 : ℝ)) (Y := (1007655682637/6250000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (384776527/200000000 : ℝ)) (τ := (58173147/62500000 : ℝ)) (σ := (993112283/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (113801291/120100491 : ℝ) ^ p + (118724957/120100491 : ℝ) ^ p := by
    exact cert_lt (x := (113801291/120100491 : ℝ)) (y := (118724957/120100491 : ℝ)) (X := (12699707137007/50000000000000 : ℝ)) (Y := (74600586691047/100000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (58173147/62500000 : ℝ)) (n' := (840703437/1000000000 : ℝ)) (Ab := (796609037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (384776527/200000000 : ℝ)) (τ := (58173147/62500000 : ℝ)) (σ := (993112283/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (58173147/62500000 : ℝ)) (n' := (840703437/1000000000 : ℝ)) (Ab := (796609037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (384776527/200000000 : ℝ)) (τ := (58173147/62500000 : ℝ)) (σ := (993112283/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (58173147/62500000 : ℝ)) (n' := (840703437/1000000000 : ℝ)) (Ab := (796609037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (384776527/200000000 : ℝ)) (τ := (58173147/62500000 : ℝ)) (σ := (993112283/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (58173147/62500000 : ℝ)) (n' := (840703437/1000000000 : ℝ)) (Ab := (796609037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (384776527/200000000 : ℝ)) (τ := (58173147/62500000 : ℝ)) (σ := (993112283/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (138767063/150486324 : ℝ) ^ p + (898103575/902917944 : ℝ) ^ p := by
    exact cert_lt (x := (138767063/150486324 : ℝ)) (y := (898103575/902917944 : ℝ)) (X := (6357691118677/50000000000000 : ℝ)) (Y := (17456923603863/20000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (372594565/398054704 : ℝ) ^ p + (592267687/597082056 : ℝ) ^ p := by
    exact cert_lt (x := (372594565/398054704 : ℝ)) (y := (592267687/597082056 : ℝ)) (X := (1163228171027/6250000000000 : ℝ)) (Y := (16277669980671/20000000000000 : ℝ)) 407 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993112283/1000000000 : ℝ)) (U := (74635257/62500000 : ℝ)) (Ab := (416301189/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (58173147/62500000 : ℝ)) (σ := (993112283/1000000000 : ℝ)) (Ab := (223556739/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab141
