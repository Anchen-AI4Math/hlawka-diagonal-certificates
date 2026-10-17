import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 129, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab129 (p : ℝ) (hpa : (801/32 : ℝ) ≤ p) (hpb : p ≤ (401/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2083216459799/109336500000000 : ℝ) (244853/25000000 : ℝ) (4000000656019/21867300000000 : ℝ) (3033/2500 : ℝ) (972722201/500000000 : ℝ) (194537723/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194012437/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11167/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4657/10000 : ℝ)
      else (3903/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11857/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2083216459799/109336500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (244853/25000000 : ℝ) := by norm_num
  have pc0 : 1 < (461990739/500000000 : ℝ) ^ p + (994098821/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (461990739/500000000 : ℝ)) (y := (994098821/1000000000 : ℝ)) (X := (6892957424239/50000000000000 : ℝ)) (Y := (17242820660761/20000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994098821/1000000000 : ℝ) ^ p + (461990739/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (994098821/1000000000 : ℝ)) (y := (461990739/500000000 : ℝ)) (X := (17242820660761/20000000000000 : ℝ)) (Y := (6892957424239/50000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1918080299/1000000000 : ℝ)) (τ := (461990739/500000000 : ℝ)) (σ := (994098821/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (789026566/833044497 : ℝ) ^ p + (823250377/833044497 : ℝ) ^ p := by
    exact cert_lt (x := (789026566/833044497 : ℝ)) (y := (823250377/833044497 : ℝ)) (X := (12825730772059/50000000000000 : ℝ)) (Y := (74348539994439/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (461990739/500000000 : ℝ)) (n' := (833044497/1000000000 : ℝ)) (Ab := (394513283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (232356251/250000000 : ℝ) ^ p + (993080389/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232356251/250000000 : ℝ)) (y := (993080389/1000000000 : ℝ)) (X := (3993118559777/25000000000000 : ℝ)) (Y := (42013771753269/50000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993080389/1000000000 : ℝ) ^ p + (232356251/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993080389/1000000000 : ℝ)) (y := (232356251/250000000 : ℝ)) (X := (42013771753269/50000000000000 : ℝ)) (Y := (3993118559777/25000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1922505393/1000000000 : ℝ)) (τ := (232356251/250000000 : ℝ)) (σ := (993080389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (132479386/139907023 : ℝ) ^ p + (414824009/419721069 : ℝ) ^ p := by
    exact cert_lt (x := (132479386/139907023 : ℝ)) (y := (414824009/419721069 : ℝ)) (X := (2548232646833/10000000000000 : ℝ)) (Y := (18629418725299/25000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (232356251/250000000 : ℝ)) (n' := (419721069/500000000 : ℝ)) (Ab := (198719079/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (929643933/1000000000 : ℝ) ^ p + (993035773/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (929643933/1000000000 : ℝ)) (y := (993035773/1000000000 : ℝ)) (X := (2008379534063/12500000000000 : ℝ)) (Y := (83932981309681/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993035773/1000000000 : ℝ) ^ p + (929643933/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993035773/1000000000 : ℝ)) (y := (929643933/1000000000 : ℝ)) (X := (83932981309681/100000000000000 : ℝ)) (Y := (2008379534063/12500000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (961339853/500000000 : ℝ)) (τ := (929643933/1000000000 : ℝ)) (σ := (993035773/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795110841/839698670 : ℝ) ^ p + (82990455/83969867 : ℝ) ^ p := by
    exact cert_lt (x := (795110841/839698670 : ℝ)) (y := (82990455/83969867 : ℝ)) (X := (25475590153711/100000000000000 : ℝ)) (Y := (74524410747247/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (929643933/1000000000 : ℝ)) (n' := (83969867/100000000 : ℝ)) (Ab := (795110841/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (929652651/1000000000 : ℝ) ^ p + (99303399/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (929652651/1000000000 : ℝ)) (y := (99303399/100000000 : ℝ)) (X := (8035406472781/50000000000000 : ℝ)) (Y := (83929204421673/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99303399/100000000 : ℝ) ^ p + (929652651/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99303399/100000000 : ℝ)) (y := (929652651/1000000000 : ℝ)) (X := (83929204421673/100000000000000 : ℝ)) (Y := (8035406472781/50000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1922686641/1000000000 : ℝ)) (τ := (929652651/1000000000 : ℝ)) (σ := (99303399/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (113588597/119958412 : ℝ) ^ p + (4234259/4284229 : ℝ) ^ p := by
    exact cert_lt (x := (113588597/119958412 : ℝ)) (y := (4234259/4284229 : ℝ)) (X := (25475322243123/100000000000000 : ℝ)) (Y := (4657792429159/6250000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (929652651/1000000000 : ℝ)) (n' := (209927221/250000000 : ℝ)) (Ab := (795120179/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464826499/500000000 : ℝ) ^ p + (993033919/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464826499/500000000 : ℝ)) (y := (993033919/1000000000 : ℝ)) (X := (16070963285009/100000000000000 : ℝ)) (Y := (4196452701369/5000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993033919/1000000000 : ℝ) ^ p + (464826499/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993033919/1000000000 : ℝ)) (y := (464826499/500000000 : ℝ)) (X := (4196452701369/5000000000000 : ℝ)) (Y := (16070963285009/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1922686917/1000000000 : ℝ)) (τ := (464826499/500000000 : ℝ)) (σ := (993033919/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (795120551/839709291 : ℝ) ^ p + (829915171/839709291 : ℝ) ^ p := by
    exact cert_lt (x := (795120551/839709291 : ℝ)) (y := (829915171/839709291 : ℝ)) (X := (12737655746247/50000000000000 : ℝ)) (Y := (74524689550249/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464826499/500000000 : ℝ)) (n' := (839709291/1000000000 : ℝ)) (Ab := (795120551/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232413253/250000000 : ℝ) ^ p + (248258479/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (232413253/250000000 : ℝ)) (y := (248258479/250000000 : ℝ)) (X := (8035484675303/50000000000000 : ℝ)) (Y := (83929047672697/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248258479/250000000 : ℝ) ^ p + (232413253/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248258479/250000000 : ℝ)) (y := (232413253/250000000 : ℝ)) (X := (83929047672697/100000000000000 : ℝ)) (Y := (8035484675303/50000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (120167933/62500000 : ℝ)) (τ := (232413253/250000000 : ℝ)) (σ := (248258479/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795120566/839709307 : ℝ) ^ p + (829915187/839709307 : ℝ) ^ p := by
    exact cert_lt (x := (795120566/839709307 : ℝ)) (y := (829915187/839709307 : ℝ)) (X := (25475311371727/100000000000000 : ℝ)) (Y := (9315586246281/12500000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232413253/250000000 : ℝ)) (n' := (839709307/1000000000 : ℝ)) (Ab := (397560283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (120167933/62500000 : ℝ)) (τ := (232413253/250000000 : ℝ)) (σ := (248258479/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (232413253/250000000 : ℝ)) (n' := (839709307/1000000000 : ℝ)) (Ab := (397560283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (120167933/62500000 : ℝ)) (τ := (232413253/250000000 : ℝ)) (σ := (248258479/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (232413253/250000000 : ℝ)) (n' := (839709307/1000000000 : ℝ)) (Ab := (397560283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (120167933/62500000 : ℝ)) (τ := (232413253/250000000 : ℝ)) (σ := (248258479/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (232413253/250000000 : ℝ)) (n' := (839709307/1000000000 : ℝ)) (Ab := (397560283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (120167933/62500000 : ℝ)) (τ := (232413253/250000000 : ℝ)) (σ := (248258479/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (232413253/250000000 : ℝ)) (n' := (839709307/1000000000 : ℝ)) (Ab := (397560283/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (120167933/62500000 : ℝ)) (τ := (232413253/250000000 : ℝ)) (σ := (248258479/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1663458201/1805987563 : ℝ) ^ p + (94536497/95051977 : ℝ) ^ p := by
    exact cert_lt (x := (1663458201/1805987563 : ℝ)) (y := (94536497/95051977 : ℝ)) (X := (6370404471633/50000000000000 : ℝ)) (Y := (87259191260619/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1116632212/1194012437 : ℝ) ^ p + (1184218317/1194012437 : ℝ) ^ p := by
    exact cert_lt (x := (1116632212/1194012437 : ℝ)) (y := (1184218317/1194012437 : ℝ)) (X := (18651504474977/100000000000000 : ℝ)) (Y := (81348495944519/100000000000000 : ℝ)) 401 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248258479/250000000 : ℝ)) (U := (1194012437/1000000000 : ℝ)) (Ab := (1663458201/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (232413253/250000000 : ℝ)) (σ := (248258479/250000000 : ℝ)) (Ab := (279158053/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab129
