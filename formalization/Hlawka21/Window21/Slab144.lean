import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 144, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab144 (p : ℝ) (hpa : (51/2 : ℝ) ≤ p) (hpb : p ≤ (817/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (32479329161/1740375000000 : ℝ) (38353/4000000 : ℝ) (250000041769/1392300000000 : ℝ) (3033/2500 : ℝ) (778573/400000 : ℝ) (97318387/100000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597100967/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11181/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(117/250 : ℝ)
      else (7829/10000 : ℝ) ≤ X j i ∧ X j i ≤ (593/500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (32479329161/1740375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (38353/4000000 : ℝ) := by norm_num
  have pc0 : 1 < (925445009/1000000000 : ℝ) ^ p + (99418597/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (925445009/1000000000 : ℝ)) (y := (99418597/100000000 : ℝ)) (X := (13832134559543/100000000000000 : ℝ)) (Y := (21541971088361/25000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99418597/100000000 : ℝ) ^ p + (925445009/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99418597/100000000 : ℝ)) (y := (925445009/1000000000 : ℝ)) (X := (21541971088361/25000000000000 : ℝ)) (Y := (13832134559543/100000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1919630979/1000000000 : ℝ)) (τ := (925445009/1000000000 : ℝ)) (σ := (99418597/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (790961571/834380503 : ℝ) ^ p + (824792253/834380503 : ℝ) ^ p := by
    exact cert_lt (x := (790961571/834380503 : ℝ)) (y := (824792253/834380503 : ℝ)) (X := (159709691627/625000000000 : ℝ)) (Y := (18611612575917/25000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (925445009/1000000000 : ℝ)) (n' := (834380503/1000000000 : ℝ)) (Ab := (790961571/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (465412303/500000000 : ℝ) ^ p + (993176529/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465412303/500000000 : ℝ)) (y := (993176529/1000000000 : ℝ)) (X := (12529895757/78125000000 : ℝ)) (Y := (20990437961143/25000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993176529/1000000000 : ℝ) ^ p + (465412303/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993176529/1000000000 : ℝ)) (y := (465412303/500000000 : ℝ)) (X := (20990437961143/25000000000000 : ℝ)) (Y := (12529895757/78125000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (384800227/200000000 : ℝ)) (τ := (465412303/500000000 : ℝ)) (σ := (993176529/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (132789835/140114944 : ℝ) ^ p + (415550707/420344832 : ℝ) ^ p := by
    exact cert_lt (x := (132789835/140114944 : ℝ)) (y := (415550707/420344832 : ℝ)) (X := (25387549964313/100000000000000 : ℝ)) (Y := (74612451628789/100000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (465412303/500000000 : ℝ)) (n' := (1641972/1953125 : ℝ)) (Ab := (79673901/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (931035609/1000000000 : ℝ) ^ p + (993133381/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931035609/1000000000 : ℝ)) (y := (993133381/1000000000 : ℝ)) (X := (16131346975197/100000000000000 : ℝ)) (Y := (83868671842261/100000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993133381/1000000000 : ℝ) ^ p + (931035609/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993133381/1000000000 : ℝ)) (y := (931035609/1000000000 : ℝ)) (X := (83868671842261/100000000000000 : ℝ)) (Y := (16131346975197/100000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192416899/100000000 : ℝ)) (τ := (931035609/1000000000 : ℝ)) (σ := (993133381/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (265654971/280312132 : ℝ) ^ p + (415674073/420468198 : ℝ) ^ p := by
    exact cert_lt (x := (265654971/280312132 : ℝ)) (y := (415674073/420468198 : ℝ)) (X := (25381101281097/100000000000000 : ℝ)) (Y := (18654724996463/25000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (931035609/1000000000 : ℝ)) (n' := (210234099/250000000 : ℝ)) (Ab := (796964913/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (232760951/250000000 : ℝ) ^ p + (993131699/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232760951/250000000 : ℝ)) (y := (993131699/1000000000 : ℝ)) (X := (403374312789/2500000000000 : ℝ)) (Y := (83865045396103/100000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993131699/1000000000 : ℝ) ^ p + (232760951/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993131699/1000000000 : ℝ)) (y := (232760951/250000000 : ℝ)) (X := (83865045396103/100000000000000 : ℝ)) (Y := (403374312789/2500000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924175503/1000000000 : ℝ)) (τ := (232760951/250000000 : ℝ)) (σ := (993131699/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (398486843/420472989 : ℝ) ^ p + (415678864/420472989 : ℝ) ^ p := by
    exact cert_lt (x := (398486843/420472989 : ℝ)) (y := (415678864/420472989 : ℝ)) (X := (3172606359433/12500000000000 : ℝ)) (Y := (37309575173261/50000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (232760951/250000000 : ℝ)) (n' := (420472989/500000000 : ℝ)) (Ab := (398486843/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465522061/500000000 : ℝ) ^ p + (496565817/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465522061/500000000 : ℝ)) (y := (496565817/500000000 : ℝ)) (X := (2016889151649/12500000000000 : ℝ)) (Y := (41932452628517/50000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496565817/500000000 : ℝ) ^ p + (465522061/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496565817/500000000 : ℝ)) (y := (465522061/500000000 : ℝ)) (X := (41932452628517/50000000000000 : ℝ)) (Y := (2016889151649/12500000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481043939/250000000 : ℝ)) (τ := (465522061/500000000 : ℝ)) (σ := (496565817/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (9160621/9666050 : ℝ) ^ p + (16627162/16818927 : ℝ) ^ p := by
    exact cert_lt (x := (9160621/9666050 : ℝ)) (y := (16627162/16818927 : ℝ)) (X := (40609346377/160000000000 : ℝ)) (Y := (18654790016531/25000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465522061/500000000 : ℝ)) (n' := (16818927/20000000 : ℝ)) (Ab := (796974027/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186208827/200000000 : ℝ) ^ p + (993131631/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186208827/200000000 : ℝ)) (y := (993131631/1000000000 : ℝ)) (X := (1613511896517/10000000000000 : ℝ)) (Y := (41932449394541/50000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993131631/1000000000 : ℝ) ^ p + (186208827/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993131631/1000000000 : ℝ)) (y := (186208827/200000000 : ℝ)) (X := (41932449394541/50000000000000 : ℝ)) (Y := (1613511896517/10000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962087883/500000000 : ℝ)) (τ := (186208827/200000000 : ℝ)) (σ := (993131631/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (159394808/168189273 : ℝ) ^ p + (23753089/24027039 : ℝ) ^ p := by
    exact cert_lt (x := (159394808/168189273 : ℝ)) (y := (23753089/24027039 : ℝ)) (X := (3172605062149/12500000000000 : ℝ)) (Y := (74619160458043/100000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186208827/200000000 : ℝ)) (n' := (168189273/200000000 : ℝ)) (Ab := (19924351/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962087883/500000000 : ℝ)) (τ := (186208827/200000000 : ℝ)) (σ := (993131631/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (186208827/200000000 : ℝ)) (n' := (168189273/200000000 : ℝ)) (Ab := (19924351/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962087883/500000000 : ℝ)) (τ := (186208827/200000000 : ℝ)) (σ := (993131631/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (186208827/200000000 : ℝ)) (n' := (168189273/200000000 : ℝ)) (Ab := (19924351/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962087883/500000000 : ℝ)) (τ := (186208827/200000000 : ℝ)) (σ := (993131631/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (186208827/200000000 : ℝ)) (n' := (168189273/200000000 : ℝ)) (Ab := (19924351/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962087883/500000000 : ℝ)) (τ := (186208827/200000000 : ℝ)) (σ := (993131631/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (186208827/200000000 : ℝ)) (n' := (168189273/200000000 : ℝ)) (Ab := (19924351/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962087883/500000000 : ℝ)) (τ := (186208827/200000000 : ℝ)) (σ := (993131631/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (832816846/902899033 : ℝ) ^ p + (898104908/902899033 : ℝ) ^ p := by
    exact cert_lt (x := (832816846/902899033 : ℝ)) (y := (898104908/902899033 : ℝ)) (X := (12709148120581/100000000000000 : ℝ)) (Y := (87290852207189/100000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (559033705/597100967 : ℝ) ^ p + (592306842/597100967 : ℝ) ^ p := by
    exact cert_lt (x := (559033705/597100967 : ℝ)) (y := (592306842/597100967 : ℝ)) (X := (18601866125039/100000000000000 : ℝ)) (Y := (40699067311969/50000000000000 : ℝ)) 817 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993131631/1000000000 : ℝ)) (U := (597100967/500000000 : ℝ)) (Ab := (416408423/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (186208827/200000000 : ℝ)) (σ := (993131631/1000000000 : ℝ)) (Ab := (111806741/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab144
