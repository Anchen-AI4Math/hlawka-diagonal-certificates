import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 23, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab023 (p : ℝ) (hpa : (439/16 : ℝ) ≤ p) (hpb : p ≤ (55/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (180692363579/12154812500000 : ℝ) (12197/1600000 : ℝ) (3200000583431/19447700000000 : ℝ) (591/500 : ℝ) (975109651/500000000 : ℝ) (487526833/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156282039/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10833/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2759/5000 : ℝ)
      else (2043/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5739/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (180692363579/12154812500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (12197/1600000 : ℝ) := by norm_num
  have pc0 : 1 < (18737729/20000000 : ℝ) ^ p + (993399667/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (18737729/20000000 : ℝ)) (y := (993399667/1000000000 : ℝ)) (X := (16649122231641/100000000000000 : ℝ)) (Y := (10418862105877/12500000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993399667/1000000000 : ℝ) ^ p + (18737729/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (993399667/1000000000 : ℝ)) (y := (18737729/20000000 : ℝ)) (X := (10418862105877/12500000000000 : ℝ)) (Y := (16649122231641/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1930286117/1000000000 : ℝ)) (τ := (18737729/20000000 : ℝ)) (σ := (993399667/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (818187419/865069343 : ℝ) ^ p + (857446218/865069343 : ℝ) ^ p := by
    exact cert_lt (x := (818187419/865069343 : ℝ)) (y := (857446218/865069343 : ℝ)) (X := (21604866351269/100000000000000 : ℝ)) (Y := (78395134839907/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (18737729/20000000 : ℝ)) (n' := (865069343/1000000000 : ℝ)) (Ab := (818187419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (940286607/1000000000 : ℝ) ^ p + (496318039/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (940286607/1000000000 : ℝ)) (y := (496318039/500000000 : ℝ)) (X := (3678636519641/20000000000000 : ℝ)) (Y := (1020085440991/1250000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496318039/500000000 : ℝ) ^ p + (940286607/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496318039/500000000 : ℝ)) (y := (940286607/1000000000 : ℝ)) (X := (1020085440991/1250000000000 : ℝ)) (Y := (3678636519641/20000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (386584537/200000000 : ℝ)) (τ := (940286607/1000000000 : ℝ)) (σ := (496318039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (821767933/868981538 : ℝ) ^ p + (861358413/868981538 : ℝ) ^ p := by
    exact cert_lt (x := (821767933/868981538 : ℝ)) (y := (861358413/868981538 : ℝ)) (X := (21518530704329/100000000000000 : ℝ)) (Y := (78481470107819/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (940286607/1000000000 : ℝ)) (n' := (434490769/500000000 : ℝ)) (Ab := (821767933/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (117548523/125000000 : ℝ) ^ p + (992611867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (117548523/125000000 : ℝ)) (y := (992611867/1000000000 : ℝ)) (X := (4611975661521/25000000000000 : ℝ)) (Y := (81552115850523/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992611867/1000000000 : ℝ) ^ p + (117548523/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992611867/1000000000 : ℝ)) (y := (117548523/125000000 : ℝ)) (X := (81552115850523/100000000000000 : ℝ)) (Y := (4611975661521/25000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1933000051/1000000000 : ℝ)) (τ := (117548523/125000000 : ℝ)) (σ := (992611867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (205468673/217274549 : ℝ) ^ p + (861475071/869098196 : ℝ) ^ p := by
    exact cert_lt (x := (205468673/217274549 : ℝ)) (y := (861475071/869098196 : ℝ)) (X := (5378991774679/25000000000000 : ℝ)) (Y := (78484034010159/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (117548523/125000000 : ℝ)) (n' := (217274549/250000000 : ℝ)) (Ab := (205468673/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (1175489/1250000 : ℝ) ^ p + (992611147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (1175489/1250000 : ℝ)) (y := (992611147/1000000000 : ℝ)) (X := (9224764888171/50000000000000 : ℝ)) (Y := (40775244557807/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992611147/1000000000 : ℝ) ^ p + (1175489/1250000 : ℝ) ^ p := by
    exact cert_lt (x := (992611147/1000000000 : ℝ)) (y := (1175489/1250000 : ℝ)) (X := (40775244557807/50000000000000 : ℝ)) (Y := (9224764888171/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1933002347/1000000000 : ℝ)) (τ := (1175489/1250000 : ℝ)) (σ := (992611147/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (410938931/434550830 : ℝ) ^ p + (172295707/173820332 : ℝ) ^ p := by
    exact cert_lt (x := (410938931/434550830 : ℝ)) (y := (172295707/173820332 : ℝ)) (X := (21515890945819/100000000000000 : ℝ)) (Y := (78484110132449/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (1175489/1250000 : ℝ)) (n' := (43455083/50000000 : ℝ)) (Ab := (410938931/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (94039129/100000000 : ℝ) ^ p + (7940889/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (94039129/100000000 : ℝ)) (y := (7940889/8000000 : ℝ)) (X := (3689915666683/20000000000000 : ℝ)) (Y := (81550439410317/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (7940889/8000000 : ℝ) ^ p + (94039129/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (7940889/8000000 : ℝ)) (y := (94039129/100000000 : ℝ)) (X := (81550439410317/100000000000000 : ℝ)) (Y := (3689915666683/20000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (386600483/200000000 : ℝ)) (τ := (94039129/100000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (821877956/869101763 : ℝ) ^ p + (861478638/869101763 : ℝ) ^ p := by
    exact cert_lt (x := (821877956/869101763 : ℝ)) (y := (861478638/869101763 : ℝ)) (X := (2689486061959/12500000000000 : ℝ)) (Y := (19621028098973/25000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (94039129/100000000 : ℝ)) (n' := (869101763/1000000000 : ℝ)) (Ab := (205469489/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (235097823/250000000 : ℝ) ^ p + (7940889/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (235097823/250000000 : ℝ)) (y := (7940889/8000000 : ℝ)) (X := (9224789706231/50000000000000 : ℝ)) (Y := (81550439410317/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (7940889/8000000 : ℝ) ^ p + (235097823/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (7940889/8000000 : ℝ)) (y := (235097823/250000000 : ℝ)) (X := (81550439410317/100000000000000 : ℝ)) (Y := (9224789706231/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (821877959/869101766 : ℝ) ^ p + (861478641/869101766 : ℝ) ^ p := by
    exact cert_lt (x := (821877959/869101766 : ℝ)) (y := (861478641/869101766 : ℝ)) (X := (860635544521/4000000000000 : ℝ)) (Y := (39242056230909/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (n' := (434550883/500000000 : ℝ)) (Ab := (821877959/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1933002417/1000000000 : ℝ)) (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1700201729/1843717961 : ℝ) ^ p + (1836094836/1843717961 : ℝ) ^ p := by
    exact cert_lt (x := (1700201729/1843717961 : ℝ)) (y := (1836094836/1843717961 : ℝ)) (X := (10768720193281/100000000000000 : ℝ)) (Y := (89231280126691/100000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1083263727/1156282039 : ℝ) ^ p + (1148658914/1156282039 : ℝ) ^ p := by
    exact cert_lt (x := (1083263727/1156282039 : ℝ)) (y := (1148658914/1156282039 : ℝ)) (X := (2078962247517/12500000000000 : ℝ)) (Y := (41684151244079/50000000000000 : ℝ)) 55 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (7940889/8000000 : ℝ)) (U := (1156282039/1000000000 : ℝ)) (Ab := (1700201729/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (235097823/250000000 : ℝ)) (σ := (7940889/8000000 : ℝ)) (Ab := (1083263727/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab023
