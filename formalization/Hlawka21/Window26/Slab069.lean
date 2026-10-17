import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 69, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab069 (p : ℝ) (hpa : (485/16 : ℝ) ≤ p) (hpb : p ≤ (243/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (71408088557/5371375000000 : ℝ) (1360169/200000000 : ℝ) (640000128913/4297100000000 : ℝ) (591/500 : ℝ) (977438739/500000000 : ℝ) (3909571/4000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (115800217/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10911/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1403/2500 : ℝ)
      else (8269/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5751/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (71408088557/5371375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1360169/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (943132307/1000000000 : ℝ) ^ p + (248481901/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (943132307/1000000000 : ℝ)) (y := (248481901/250000000 : ℝ)) (X := (16890534352311/100000000000000 : ℝ)) (Y := (83109486768419/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248481901/250000000 : ℝ) ^ p + (943132307/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248481901/250000000 : ℝ)) (y := (943132307/1000000000 : ℝ)) (X := (83109486768419/100000000000000 : ℝ)) (Y := (16890534352311/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1937059911/1000000000 : ℝ)) (τ := (943132307/1000000000 : ℝ)) (σ := (248481901/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (23622408/24859789 : ℝ) ^ p + (172658354/174018523 : ℝ) ^ p := by
    exact cert_lt (x := (23622408/24859789 : ℝ)) (y := (172658354/174018523 : ℝ)) (X := (21207372501057/100000000000000 : ℝ)) (Y := (15758525681323/20000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (943132307/1000000000 : ℝ)) (n' := (174018523/200000000 : ℝ)) (Ab := (20669607/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (946299303/1000000000 : ℝ) ^ p + (993207143/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946299303/1000000000 : ℝ)) (y := (993207143/1000000000 : ℝ)) (X := (29921701359/160000000000 : ℝ)) (Y := (2032473888259/2500000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993207143/1000000000 : ℝ) ^ p + (946299303/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993207143/1000000000 : ℝ)) (y := (946299303/1000000000 : ℝ)) (X := (2032473888259/2500000000000 : ℝ)) (Y := (29921701359/160000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (969753223/500000000 : ℝ)) (τ := (946299303/1000000000 : ℝ)) (σ := (993207143/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (830113759/873702390 : ℝ) ^ p + (173380309/174740478 : ℝ) ^ p := by
    exact cert_lt (x := (830113759/873702390 : ℝ)) (y := (173380309/174740478 : ℝ)) (X := (5282359429191/25000000000000 : ℝ)) (Y := (7887056319977/10000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (946299303/1000000000 : ℝ)) (n' := (87370239/100000000 : ℝ)) (Ab := (830113759/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (946382563/1000000000 : ℝ) ^ p + (99318701/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (946382563/1000000000 : ℝ)) (y := (99318701/100000000 : ℝ)) (X := (7324651299/39062500000 : ℝ)) (Y := (40624456421903/50000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99318701/100000000 : ℝ) ^ p + (946382563/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99318701/100000000 : ℝ)) (y := (946382563/1000000000 : ℝ)) (X := (40624456421903/50000000000000 : ℝ)) (Y := (7324651299/39062500000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1939569573/1000000000 : ℝ)) (τ := (946382563/1000000000 : ℝ)) (σ := (99318701/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (830201136/873797129 : ℝ) ^ p + (866996284/873797129 : ℝ) ^ p := by
    exact cert_lt (x := (830201136/873797129 : ℝ)) (y := (866996284/873797129 : ℝ)) (X := (10563700186353/50000000000000 : ℝ)) (Y := (78872600935859/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (946382563/1000000000 : ℝ)) (n' := (873797129/1000000000 : ℝ)) (Ab := (51887571/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (946384739/1000000000 : ℝ) ^ p + (993186483/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946384739/1000000000 : ℝ)) (y := (993186483/1000000000 : ℝ)) (X := (9376208479859/50000000000000 : ℝ)) (Y := (8124760333011/10000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993186483/1000000000 : ℝ) ^ p + (946384739/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993186483/1000000000 : ℝ)) (y := (946384739/1000000000 : ℝ)) (X := (8124760333011/10000000000000 : ℝ)) (Y := (9376208479859/50000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (969785611/500000000 : ℝ)) (τ := (946384739/1000000000 : ℝ)) (σ := (993186483/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (276734473/291266535 : ℝ) ^ p + (173399752/174759921 : ℝ) ^ p := by
    exact cert_lt (x := (276734473/291266535 : ℝ)) (y := (173399752/174759921 : ℝ)) (X := (4225469335157/20000000000000 : ℝ)) (Y := (4929540886673/6250000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (946384739/1000000000 : ℝ)) (n' := (174759921/200000000 : ℝ)) (Ab := (830203419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (946384797/1000000000 : ℝ) ^ p + (993186469/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946384797/1000000000 : ℝ)) (y := (993186469/1000000000 : ℝ)) (X := (937622593423/5000000000000 : ℝ)) (Y := (81247568542549/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993186469/1000000000 : ℝ) ^ p + (946384797/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993186469/1000000000 : ℝ)) (y := (946384797/1000000000 : ℝ)) (X := (81247568542549/100000000000000 : ℝ)) (Y := (937622593423/5000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (969785633/500000000 : ℝ)) (τ := (946384797/1000000000 : ℝ)) (σ := (993186469/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (830203480/873799671 : ℝ) ^ p + (866998826/873799671 : ℝ) ^ p := by
    exact cert_lt (x := (830203480/873799671 : ℝ)) (y := (866998826/873799671 : ℝ)) (X := (21127345356217/100000000000000 : ℝ)) (Y := (15774531121243/20000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (946384797/1000000000 : ℝ)) (n' := (873799671/1000000000 : ℝ)) (Ab := (20755087/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (946384799/1000000000 : ℝ) ^ p + (248296617/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (946384799/1000000000 : ℝ)) (y := (248296617/250000000 : ℝ)) (X := (18752453072211/100000000000000 : ℝ)) (Y := (81247566057723/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248296617/250000000 : ℝ) ^ p + (946384799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248296617/250000000 : ℝ)) (y := (946384799/1000000000 : ℝ)) (X := (81247566057723/100000000000000 : ℝ)) (Y := (18752453072211/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1939571267/1000000000 : ℝ)) (τ := (946384799/1000000000 : ℝ)) (σ := (248296617/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (830203482/873799673 : ℝ) ^ p + (866998828/873799673 : ℝ) ^ p := by
    exact cert_lt (x := (830203482/873799673 : ℝ)) (y := (866998828/873799673 : ℝ)) (X := (21127345433351/100000000000000 : ℝ)) (Y := (78872655649229/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (946384799/1000000000 : ℝ)) (n' := (873799673/1000000000 : ℝ)) (Ab := (415101741/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1939571267/1000000000 : ℝ)) (τ := (946384799/1000000000 : ℝ)) (σ := (248296617/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (946384799/1000000000 : ℝ)) (n' := (873799673/1000000000 : ℝ)) (Ab := (415101741/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1939571267/1000000000 : ℝ)) (τ := (946384799/1000000000 : ℝ)) (σ := (248296617/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (946384799/1000000000 : ℝ)) (n' := (873799673/1000000000 : ℝ)) (Ab := (415101741/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1939571267/1000000000 : ℝ)) (τ := (946384799/1000000000 : ℝ)) (σ := (248296617/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (946384799/1000000000 : ℝ)) (n' := (873799673/1000000000 : ℝ)) (Ab := (415101741/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1939571267/1000000000 : ℝ)) (τ := (946384799/1000000000 : ℝ)) (σ := (248296617/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (946384799/1000000000 : ℝ)) (n' := (873799673/1000000000 : ℝ)) (Ab := (415101741/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1939571267/1000000000 : ℝ)) (τ := (946384799/1000000000 : ℝ)) (σ := (248296617/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (855474814/920998915 : ℝ) ^ p + (367039397/368399566 : ℝ) ^ p := by
    exact cert_lt (x := (855474814/920998915 : ℝ)) (y := (367039397/368399566 : ℝ)) (X := (10627321632313/100000000000000 : ℝ)) (Y := (89372678681719/100000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1091051419/1158002170 : ℝ) ^ p + (230240265/231600434 : ℝ) ^ p := by
    exact cert_lt (x := (1091051419/1158002170 : ℝ)) (y := (230240265/231600434 : ℝ)) (X := (3276470748893/20000000000000 : ℝ)) (Y := (41808823495883/50000000000000 : ℝ)) 243 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248296617/250000000 : ℝ)) (U := (115800217/100000000 : ℝ)) (Ab := (427737407/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (946384799/1000000000 : ℝ)) (σ := (248296617/250000000 : ℝ)) (Ab := (1091051419/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab069
