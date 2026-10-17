import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 31, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab031 (p : ℝ) (hpa : (447/16 : ℝ) ≤ p) (hpb : p ≤ (28 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (721130814593/49505250000000 : ℝ) (7466343/1000000000 : ℝ) (3200000594063/19802100000000 : ℝ) (591/500 : ℝ) (975548643/500000000 : ℝ) (121936827/125000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156595263/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(678/625 : ℝ) ≤ X j i ∧ X j i ≤ -(346/625 : ℝ)
      else (8191/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5741/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (721130814593/49505250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7466343/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (938069097/1000000000 : ℝ) ^ p + (198699559/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (938069097/1000000000 : ℝ)) (y := (198699559/200000000 : ℝ)) (X := (16694569179661/100000000000000 : ℝ)) (Y := (520659058883/625000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198699559/200000000 : ℝ) ^ p + (938069097/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198699559/200000000 : ℝ)) (y := (938069097/1000000000 : ℝ)) (X := (520659058883/625000000000 : ℝ)) (Y := (16694569179661/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (482891723/250000000 : ℝ)) (τ := (938069097/1000000000 : ℝ)) (σ := (198699559/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (819809917/866031289 : ℝ) ^ p + (858564946/866031289 : ℝ) ^ p := by
    exact cert_lt (x := (819809917/866031289 : ℝ)) (y := (858564946/866031289 : ℝ)) (X := (21529223542263/100000000000000 : ℝ)) (Y := (78470777611821/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (938069097/1000000000 : ℝ)) (n' := (866031289/1000000000 : ℝ)) (Ab := (819809917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (94142733/100000000 : ℝ) ^ p + (992741777/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94142733/100000000 : ℝ)) (y := (992741777/1000000000 : ℝ)) (X := (4612861992697/25000000000000 : ℝ)) (Y := (81548571200999/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992741777/1000000000 : ℝ) ^ p + (94142733/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992741777/1000000000 : ℝ)) (y := (94142733/100000000 : ℝ)) (X := (81548571200999/100000000000000 : ℝ)) (Y := (4612861992697/25000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1934169107/1000000000 : ℝ)) (τ := (94142733/100000000 : ℝ)) (σ := (992741777/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (411672562/434944183 : ℝ) ^ p + (862422023/869888366 : ℝ) ^ p := by
    exact cert_lt (x := (411672562/434944183 : ℝ)) (y := (862422023/869888366 : ℝ)) (X := (5361114430447/25000000000000 : ℝ)) (Y := (3142221744143/4000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (94142733/100000000 : ℝ)) (n' := (434944183/500000000 : ℝ)) (Ab := (205836281/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (470762667/500000000 : ℝ) ^ p + (992718353/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470762667/500000000 : ℝ)) (y := (992718353/1000000000 : ℝ)) (X := (9252653340591/50000000000000 : ℝ)) (Y := (20373677971787/25000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992718353/1000000000 : ℝ) ^ p + (470762667/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992718353/1000000000 : ℝ)) (y := (470762667/500000000 : ℝ)) (X := (20373677971787/25000000000000 : ℝ)) (Y := (9252653340591/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1934243687/1000000000 : ℝ)) (τ := (470762667/500000000 : ℝ)) (σ := (992718353/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823448096/870000723 : ℝ) ^ p + (287511460/290000241 : ℝ) ^ p := by
    exact cert_lt (x := (823448096/870000723 : ℝ)) (y := (287511460/290000241 : ℝ)) (X := (10720999036019/50000000000000 : ℝ)) (Y := (78558002895281/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (470762667/500000000 : ℝ)) (n' := (870000723/1000000000 : ℝ)) (Ab := (25732753/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (470764089/500000000 : ℝ) ^ p + (124089709/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (470764089/500000000 : ℝ)) (y := (124089709/125000000 : ℝ)) (X := (4626717970089/25000000000000 : ℝ)) (Y := (81493146562229/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124089709/125000000 : ℝ) ^ p + (470764089/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124089709/125000000 : ℝ)) (y := (470764089/500000000 : ℝ)) (X := (81493146562229/100000000000000 : ℝ)) (Y := (4626717970089/25000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (38684917/20000000 : ℝ)) (τ := (470764089/500000000 : ℝ)) (σ := (124089709/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (823451084/870003983 : ℝ) ^ p + (862537640/870003983 : ℝ) ^ p := by
    exact cert_lt (x := (823451084/870003983 : ℝ)) (y := (862537640/870003983 : ℝ)) (X := (167515054221/781250000000 : ℝ)) (Y := (4909879640151/6250000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (470764089/500000000 : ℝ)) (n' := (870003983/1000000000 : ℝ)) (Ab := (205862771/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (47076413/50000000 : ℝ) ^ p + (248179413/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (47076413/50000000 : ℝ)) (y := (248179413/250000000 : ℝ)) (X := (9253458505529/50000000000000 : ℝ)) (Y := (10186637573913/12500000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248179413/250000000 : ℝ) ^ p + (47076413/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (248179413/250000000 : ℝ)) (y := (47076413/50000000 : ℝ)) (X := (10186637573913/12500000000000 : ℝ)) (Y := (9253458505529/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (241780739/125000000 : ℝ)) (τ := (47076413/50000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (823451170/870004077 : ℝ) ^ p + (287512578/290001359 : ℝ) ^ p := by
    exact cert_lt (x := (823451170/870004077 : ℝ)) (y := (287512578/290001359 : ℝ)) (X := (21441924774753/100000000000000 : ℝ)) (Y := (39279038149829/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (47076413/50000000 : ℝ)) (n' := (870004077/1000000000 : ℝ)) (Ab := (82345117/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (470764131/500000000 : ℝ) ^ p + (248179413/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (470764131/500000000 : ℝ)) (y := (248179413/250000000 : ℝ)) (X := (18506918111809/100000000000000 : ℝ)) (Y := (10186637573913/12500000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248179413/250000000 : ℝ) ^ p + (470764131/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248179413/250000000 : ℝ)) (y := (470764131/500000000 : ℝ)) (X := (10186637573913/12500000000000 : ℝ)) (Y := (18506918111809/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (823451172/870004079 : ℝ) ^ p + (862537736/870004079 : ℝ) ^ p := by
    exact cert_lt (x := (823451172/870004079 : ℝ)) (y := (862537736/870004079 : ℝ)) (X := (21441924852779/100000000000000 : ℝ)) (Y := (78558076343429/100000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (n' := (870004079/1000000000 : ℝ)) (Ab := (205862793/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (967122957/500000000 : ℝ)) (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1702223345/1843404737 : ℝ) ^ p + (1835938394/1843404737 : ℝ) ^ p := by
    exact cert_lt (x := (1702223345/1843404737 : ℝ)) (y := (1835938394/1843404737 : ℝ)) (X := (10741961915357/100000000000000 : ℝ)) (Y := (44629019204859/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1084710472/1156595263 : ℝ) ^ p + (1149128920/1156595263 : ℝ) ^ p := by
    exact cert_lt (x := (1084710472/1156595263 : ℝ)) (y := (1149128920/1156595263 : ℝ)) (X := (16584709283149/100000000000000 : ℝ)) (Y := (41707645612957/50000000000000 : ℝ)) 28 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248179413/250000000 : ℝ)) (U := (1156595263/1000000000 : ℝ)) (Ab := (340444669/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (470764131/500000000 : ℝ)) (σ := (248179413/250000000 : ℝ)) (Ab := (135588809/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab031
