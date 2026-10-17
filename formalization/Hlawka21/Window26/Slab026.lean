import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 26, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab026 (p : ℝ) (hpa : (221/8 : ℝ) ≤ p) (hpb : p ≤ (443/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (5777183803/391612000000 : ℝ) (7563577/1000000000 : ℝ) (1600000293709/9790300000000 : ℝ) (591/500 : ℝ) (243819027/125000000 : ℝ) (975220869/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156400201/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10839/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(221/400 : ℝ)
      else (8179/10000 : ℝ) ≤ X j i ∧ X j i ≤ (287/250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (5777183803/391612000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7563577/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (937335183/1000000000 : ℝ) ^ p + (310449/312500 : ℝ) ^ p := by
    exact cert_lt (x := (937335183/1000000000 : ℝ)) (y := (310449/312500 : ℝ)) (X := (8333176184049/50000000000000 : ℝ)) (Y := (83333667243383/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (310449/312500 : ℝ) ^ p + (937335183/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (310449/312500 : ℝ)) (y := (937335183/1000000000 : ℝ)) (X := (83333667243383/100000000000000 : ℝ)) (Y := (8333176184049/50000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1930771983/1000000000 : ℝ)) (τ := (937335183/1000000000 : ℝ)) (σ := (310449/312500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (818802757/865434929 : ℝ) ^ p + (857871352/865434929 : ℝ) ^ p := by
    exact cert_lt (x := (818802757/865434929 : ℝ)) (y := (857871352/865434929 : ℝ)) (X := (21576141440719/100000000000000 : ℝ)) (Y := (39211929649007/50000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (937335183/1000000000 : ℝ)) (n' := (865434929/1000000000 : ℝ)) (Ab := (818802757/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (470359779/500000000 : ℝ) ^ p + (19853521/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (470359779/500000000 : ℝ)) (y := (19853521/20000000 : ℝ)) (X := (9207644702013/50000000000000 : ℝ)) (Y := (81584728396473/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (19853521/20000000 : ℝ) ^ p + (470359779/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (19853521/20000000 : ℝ)) (y := (470359779/500000000 : ℝ)) (X := (81584728396473/100000000000000 : ℝ)) (Y := (9207644702013/50000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (241674451/125000000 : ℝ)) (τ := (470359779/500000000 : ℝ)) (σ := (19853521/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822366205/869326332 : ℝ) ^ p + (123108965/124189476 : ℝ) ^ p := by
    exact cert_lt (x := (822366205/869326332 : ℝ)) (y := (123108965/124189476 : ℝ)) (X := (5372600093049/25000000000000 : ℝ)) (Y := (78509600412861/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (470359779/500000000 : ℝ)) (n' := (217331583/250000000 : ℝ)) (Ab := (164473241/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37632791/40000000 : ℝ) ^ p + (496326069/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (37632791/40000000 : ℝ)) (y := (496326069/500000000 : ℝ)) (X := (18469684657891/100000000000000 : ℝ)) (Y := (407651665477/500000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496326069/500000000 : ℝ) ^ p + (37632791/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496326069/500000000 : ℝ)) (y := (37632791/40000000 : ℝ)) (X := (407651665477/500000000000 : ℝ)) (Y := (18469684657891/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1933471913/1000000000 : ℝ)) (τ := (37632791/40000000 : ℝ)) (σ := (496326069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (822471523/869441352 : ℝ) ^ p + (861877775/869441352 : ℝ) ^ p := by
    exact cert_lt (x := (822471523/869441352 : ℝ)) (y := (861877775/869441352 : ℝ)) (X := (268598457577/1250000000000 : ℝ)) (Y := (78512124392359/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37632791/40000000 : ℝ)) (n' := (108680169/125000000 : ℝ)) (Ab := (822471523/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (37632909/40000000 : ℝ) ^ p + (992651433/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (37632909/40000000 : ℝ)) (y := (992651433/1000000000 : ℝ)) (X := (2308911023433/12500000000000 : ℝ)) (Y := (509554561773/625000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992651433/1000000000 : ℝ) ^ p + (37632909/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (992651433/1000000000 : ℝ)) (y := (37632909/40000000 : ℝ)) (X := (509554561773/625000000000 : ℝ)) (Y := (2308911023433/12500000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (966737079/500000000 : ℝ)) (τ := (37632909/40000000 : ℝ)) (σ := (992651433/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (822474623/869444737 : ℝ) ^ p + (4245720/4282979 : ℝ) ^ p := by
    exact cert_lt (x := (822474623/869444737 : ℝ)) (y := (4245720/4282979 : ℝ)) (X := (10743901363969/50000000000000 : ℝ)) (Y := (78512198663297/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (37632909/40000000 : ℝ)) (n' := (869444737/1000000000 : ℝ)) (Ab := (822474623/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (235205703/250000000 : ℝ) ^ p + (248162853/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (235205703/250000000 : ℝ)) (y := (248162853/250000000 : ℝ)) (X := (3694267096007/20000000000000 : ℝ)) (Y := (81528682128903/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248162853/250000000 : ℝ) ^ p + (235205703/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248162853/250000000 : ℝ)) (y := (235205703/250000000 : ℝ)) (X := (81528682128903/100000000000000 : ℝ)) (Y := (3694267096007/20000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (120842139/62500000 : ℝ)) (τ := (235205703/250000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (822474714/869444837 : ℝ) ^ p + (861881260/869444837 : ℝ) ^ p := by
    exact cert_lt (x := (822474714/869444837 : ℝ)) (y := (861881260/869444837 : ℝ)) (X := (10743900062761/50000000000000 : ℝ)) (Y := (78512200857409/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (235205703/250000000 : ℝ)) (n' := (869444837/1000000000 : ℝ)) (Ab := (411237357/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470411407/500000000 : ℝ) ^ p + (248162853/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (470411407/500000000 : ℝ)) (y := (248162853/250000000 : ℝ)) (X := (18471336567221/100000000000000 : ℝ)) (Y := (81528682128903/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248162853/250000000 : ℝ) ^ p + (470411407/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248162853/250000000 : ℝ)) (y := (470411407/500000000 : ℝ)) (X := (81528682128903/100000000000000 : ℝ)) (Y := (18471336567221/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (822474716/869444839 : ℝ) ^ p + (861881262/869444839 : ℝ) ^ p := by
    exact cert_lt (x := (822474716/869444839 : ℝ)) (y := (861881262/869444839 : ℝ)) (X := (10743900101839/50000000000000 : ℝ)) (Y := (78512200901291/100000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (n' := (869444839/1000000000 : ℝ)) (Ab := (205618679/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (966737113/500000000 : ℝ)) (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1700968054/1843599799 : ℝ) ^ p + (1836036222/1843599799 : ℝ) ^ p := by
    exact cert_lt (x := (1700968054/1843599799 : ℝ)) (y := (1836036222/1843599799 : ℝ)) (X := (10758566822489/100000000000000 : ℝ)) (Y := (557758958683/625000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083811150/1156400201 : ℝ) ^ p + (39615056/39875869 : ℝ) ^ p := by
    exact cert_lt (x := (1083811150/1156400201 : ℝ)) (y := (39615056/39875869 : ℝ)) (X := (4153469975777/25000000000000 : ℝ)) (Y := (20846530184997/25000000000000 : ℝ)) 443 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248162853/250000000 : ℝ)) (U := (1156400201/1000000000 : ℝ)) (Ab := (850484027/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470411407/500000000 : ℝ)) (σ := (248162853/250000000 : ℝ)) (Ab := (21676223/20000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab026
