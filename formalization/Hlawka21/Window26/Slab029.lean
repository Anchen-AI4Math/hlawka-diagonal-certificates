import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 29, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab029 (p : ℝ) (hpa : (445/16 : ℝ) ≤ p) (hpb : p ≤ (223/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (72153490103/4928375000000 : ℝ) (7504939/1000000000 : ℝ) (640000118281/3942700000000 : ℝ) (591/500 : ℝ) (975440353/500000000 : ℝ) (487692923/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156517517/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2711/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(5531/10000 : ℝ)
      else (4093/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11481/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (72153490103/4928375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7504939/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (586111/625000 : ℝ) ^ p + (993473529/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (586111/625000 : ℝ)) (y := (993473529/1000000000 : ℝ)) (X := (16683357419603/100000000000000 : ℝ)) (Y := (833166613827/1000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993473529/1000000000 : ℝ) ^ p + (586111/625000 : ℝ) ^ p := by
    exact cert_lt (x := (993473529/1000000000 : ℝ)) (y := (586111/625000 : ℝ)) (X := (833166613827/1000000000000 : ℝ)) (Y := (16683357419603/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1931251129/1000000000 : ℝ)) (τ := (586111/625000 : ℝ)) (σ := (993473529/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819409777/865794659 : ℝ) ^ p + (858289720/865794659 : ℝ) ^ p := by
    exact cert_lt (x := (819409777/865794659 : ℝ)) (y := (858289720/865794659 : ℝ)) (X := (21547848682849/100000000000000 : ℝ)) (Y := (78452152206097/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (586111/625000 : ℝ)) (n' := (865794659/1000000000 : ℝ)) (Ab := (819409777/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (117643283/125000000 : ℝ) ^ p + (992715619/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (117643283/125000000 : ℝ)) (y := (992715619/1000000000 : ℝ)) (X := (18437086455397/100000000000000 : ℝ)) (Y := (20390733119363/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992715619/1000000000 : ℝ) ^ p + (117643283/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992715619/1000000000 : ℝ)) (y := (117643283/125000000 : ℝ)) (X := (20390733119363/25000000000000 : ℝ)) (Y := (18437086455397/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1933861883/1000000000 : ℝ)) (τ := (117643283/125000000 : ℝ)) (σ := (992715619/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (822956250/869665417 : ℝ) ^ p + (862160478/869665417 : ℝ) ^ p := by
    exact cert_lt (x := (822956250/869665417 : ℝ)) (y := (862160478/869665417 : ℝ)) (X := (21462695432021/100000000000000 : ℝ)) (Y := (9817163248797/12500000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (117643283/125000000 : ℝ)) (n' := (869665417/1000000000 : ℝ)) (Ab := (131673/160000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (188249029/200000000 : ℝ) ^ p + (992692001/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188249029/200000000 : ℝ)) (y := (992692001/1000000000 : ℝ)) (X := (9245579459483/50000000000000 : ℝ)) (Y := (2547151832717/3125000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992692001/1000000000 : ℝ) ^ p + (188249029/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992692001/1000000000 : ℝ)) (y := (188249029/200000000 : ℝ)) (X := (2547151832717/3125000000000 : ℝ)) (Y := (9245579459483/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (966968573/500000000 : ℝ)) (τ := (188249029/200000000 : ℝ)) (σ := (992692001/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823060151/869778828 : ℝ) ^ p + (862273889/869778828 : ℝ) ^ p := by
    exact cert_lt (x := (823060151/869778828 : ℝ)) (y := (862273889/869778828 : ℝ)) (X := (10730105259421/50000000000000 : ℝ)) (Y := (3141591634239/4000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (188249029/200000000 : ℝ)) (n' := (217444707/250000000 : ℝ)) (Ab := (823060151/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (94124803/100000000 : ℝ) ^ p + (992691311/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94124803/100000000 : ℝ)) (y := (992691311/1000000000 : ℝ)) (X := (4623184714167/25000000000000 : ℝ)) (Y := (40753639699719/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992691311/1000000000 : ℝ) ^ p + (94124803/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992691311/1000000000 : ℝ)) (y := (94124803/100000000 : ℝ)) (X := (40753639699719/50000000000000 : ℝ)) (Y := (4623184714167/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1933939341/1000000000 : ℝ)) (τ := (94124803/100000000 : ℝ)) (σ := (992691311/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (274354394/289927379 : ℝ) ^ p + (862277198/869782137 : ℝ) ^ p := by
    exact cert_lt (x := (274354394/289927379 : ℝ)) (y := (862277198/869782137 : ℝ)) (X := (536503441197/2500000000000 : ℝ)) (Y := (39269931674233/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (94124803/100000000 : ℝ)) (n' := (869782137/1000000000 : ℝ)) (Ab := (411531591/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (470624057/500000000 : ℝ) ^ p + (992691291/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470624057/500000000 : ℝ)) (y := (992691291/1000000000 : ℝ)) (X := (18492784860271/100000000000000 : ℝ)) (Y := (20376808406147/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992691291/1000000000 : ℝ) ^ p + (470624057/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992691291/1000000000 : ℝ)) (y := (470624057/500000000 : ℝ)) (X := (20376808406147/25000000000000 : ℝ)) (Y := (18492784860271/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (386787881/200000000 : ℝ)) (τ := (470624057/500000000 : ℝ)) (σ := (992691291/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (823063270/869782233 : ℝ) ^ p + (862277294/869782233 : ℝ) ^ p := by
    exact cert_lt (x := (823063270/869782233 : ℝ)) (y := (862277294/869782233 : ℝ)) (X := (10730067790609/50000000000000 : ℝ)) (Y := (19634966362899/25000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (470624057/500000000 : ℝ)) (n' := (869782233/1000000000 : ℝ)) (Ab := (82306327/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (941248117/1000000000 : ℝ) ^ p + (99269129/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (941248117/1000000000 : ℝ)) (y := (99269129/100000000 : ℝ)) (X := (9246393251629/50000000000000 : ℝ)) (Y := (40753615667923/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99269129/100000000 : ℝ) ^ p + (941248117/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99269129/100000000 : ℝ)) (y := (941248117/1000000000 : ℝ)) (X := (40753615667923/50000000000000 : ℝ)) (Y := (9246393251629/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (823063274/869782237 : ℝ) ^ p + (50722194/51163661 : ℝ) ^ p := by
    exact cert_lt (x := (823063274/869782237 : ℝ)) (y := (50722194/51163661 : ℝ)) (X := (10730067868687/50000000000000 : ℝ)) (Y := (39269932769613/50000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (n' := (869782237/1000000000 : ℝ)) (Ab := (411531637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933939407/1000000000 : ℝ)) (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1701724474/1843482483 : ℝ) ^ p + (1835977544/1843482483 : ℝ) ^ p := by
    exact cert_lt (x := (1701724474/1843482483 : ℝ)) (y := (1835977544/1843482483 : ℝ)) (X := (5374278340809/50000000000000 : ℝ)) (Y := (89251443659597/100000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1084352677/1156517517 : ℝ) ^ p + (1149012578/1156517517 : ℝ) ^ p := by
    exact cert_lt (x := (1084352677/1156517517 : ℝ)) (y := (1149012578/1156517517 : ℝ)) (X := (16596299020673/100000000000000 : ℝ)) (Y := (16680740296129/20000000000000 : ℝ)) 223 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99269129/100000000 : ℝ)) (U := (1156517517/1000000000 : ℝ)) (Ab := (850862237/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (941248117/1000000000 : ℝ)) (σ := (99269129/100000000 : ℝ)) (Ab := (1084352677/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab029
