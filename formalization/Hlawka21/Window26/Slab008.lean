import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 8, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab008 (p : ℝ) (hpa : (53/2 : ℝ) ≤ p) (hpb : p ≤ (425/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (90750813781/5869750000000 : ℝ) (7935249/1000000000 : ℝ) (400000070437/2347900000000 : ℝ) (591/500 : ℝ) (974242579/500000000 : ℝ) (48709131/50000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231135673/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2161/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2741/5000 : ℝ)
      else (1017/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11469/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (90750813781/5869750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7935249/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (934543169/1000000000 : ℝ) ^ p + (24830193/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (934543169/1000000000 : ℝ)) (y := (24830193/25000000 : ℝ)) (X := (2069930238787/12500000000000 : ℝ)) (Y := (41720288605589/50000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (24830193/25000000 : ℝ) ^ p + (934543169/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24830193/25000000 : ℝ)) (y := (934543169/1000000000 : ℝ)) (X := (41720288605589/50000000000000 : ℝ)) (Y := (2069930238787/12500000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1927750889/1000000000 : ℝ)) (τ := (934543169/1000000000 : ℝ)) (σ := (24830193/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (814979713/863148580 : ℝ) ^ p + (122173333/123306940 : ℝ) ^ p := by
    exact cert_lt (x := (814979713/863148580 : ℝ)) (y := (122173333/123306940 : ℝ)) (X := (21755252460797/100000000000000 : ℝ)) (Y := (78244748493669/100000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (934543169/1000000000 : ℝ)) (n' := (43157429/50000000 : ℝ)) (Ab := (814979713/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (37520929/40000000 : ℝ) ^ p + (496214981/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (37520929/40000000 : ℝ)) (y := (496214981/500000000 : ℝ)) (X := (57118072599/312500000000 : ℝ)) (Y := (20430558367721/25000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496214981/500000000 : ℝ) ^ p + (37520929/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (496214981/500000000 : ℝ)) (y := (37520929/40000000 : ℝ)) (X := (20430558367721/25000000000000 : ℝ)) (Y := (57118072599/312500000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1930453187/1000000000 : ℝ)) (τ := (37520929/40000000 : ℝ)) (σ := (496214981/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (818646825/867166871 : ℝ) ^ p + (859231622/867166871 : ℝ) ^ p := by
    exact cert_lt (x := (818646825/867166871 : ℝ)) (y := (859231622/867166871 : ℝ)) (X := (10832921062291/50000000000000 : ℝ)) (Y := (15666831761947/20000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (37520929/40000000 : ℝ)) (n' := (867166871/1000000000 : ℝ)) (Ab := (32745873/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (187626403/200000000 : ℝ) ^ p + (992404173/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187626403/200000000 : ℝ)) (y := (992404173/1000000000 : ℝ)) (X := (4583543621757/25000000000000 : ℝ)) (Y := (40832921899073/50000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992404173/1000000000 : ℝ) ^ p + (187626403/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992404173/1000000000 : ℝ)) (y := (187626403/200000000 : ℝ)) (X := (40832921899073/50000000000000 : ℝ)) (Y := (4583543621757/25000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (482634047/250000000 : ℝ)) (τ := (187626403/200000000 : ℝ)) (σ := (992404173/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (818761235/867292249 : ℝ) ^ p + (859357000/867292249 : ℝ) ^ p := by
    exact cert_lt (x := (818761235/867292249 : ℝ)) (y := (859357000/867292249 : ℝ)) (X := (21663063924381/100000000000000 : ℝ)) (Y := (78336936819207/100000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (187626403/200000000 : ℝ)) (n' := (867292249/1000000000 : ℝ)) (Ab := (163752247/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (187627079/200000000 : ℝ) ^ p + (99240337/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (187627079/200000000 : ℝ)) (y := (99240337/100000000 : ℝ)) (X := (18335929187731/100000000000000 : ℝ)) (Y := (20416022144219/25000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (99240337/100000000 : ℝ) ^ p + (187627079/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (99240337/100000000 : ℝ)) (y := (187627079/200000000 : ℝ)) (X := (20416022144219/25000000000000 : ℝ)) (Y := (18335929187731/100000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (386107753/200000000 : ℝ)) (τ := (187627079/200000000 : ℝ)) (σ := (99240337/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (409382395/433648072 : ℝ) ^ p + (859360895/867296144 : ℝ) ^ p := by
    exact cert_lt (x := (409382395/433648072 : ℝ)) (y := (859360895/867296144 : ℝ)) (X := (5415744537453/25000000000000 : ℝ)) (Y := (3916851155483/5000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (187627079/200000000 : ℝ)) (n' := (54206009/62500000 : ℝ)) (Ab := (81876479/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (1876271/2000000 : ℝ) ^ p + (198480669/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (1876271/2000000 : ℝ)) (y := (198480669/200000000 : ℝ)) (X := (4583995925063/25000000000000 : ℝ)) (Y := (20416008482929/25000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198480669/200000000 : ℝ) ^ p + (1876271/2000000 : ℝ) ^ p := by
    exact cert_lt (x := (198480669/200000000 : ℝ)) (y := (1876271/2000000 : ℝ)) (X := (20416008482929/25000000000000 : ℝ)) (Y := (4583995925063/25000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (386107769/200000000 : ℝ)) (τ := (1876271/2000000 : ℝ)) (σ := (198480669/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (163752980/173459253 : ℝ) ^ p + (286453672/289098755 : ℝ) ^ p := by
    exact cert_lt (x := (163752980/173459253 : ℝ)) (y := (286453672/289098755 : ℝ)) (X := (21662975177561/100000000000000 : ℝ)) (Y := (78337025790303/100000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (1876271/2000000 : ℝ)) (n' := (173459253/200000000 : ℝ)) (Ab := (8187649/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (58633469/62500000 : ℝ) ^ p + (62025209/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (58633469/62500000 : ℝ)) (y := (62025209/62500000 : ℝ)) (X := (9167992888461/50000000000000 : ℝ)) (Y := (8166403174591/10000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (62025209/62500000 : ℝ) ^ p + (58633469/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (62025209/62500000 : ℝ)) (y := (58633469/62500000 : ℝ)) (X := (8166403174591/10000000000000 : ℝ)) (Y := (9167992888461/50000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (60329339/31250000 : ℝ)) (τ := (58633469/62500000 : ℝ)) (σ := (62025209/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (163752981/173459254 : ℝ) ^ p + (859361021/867296270 : ℝ) ^ p := by
    exact cert_lt (x := (163752981/173459254 : ℝ)) (y := (859361021/867296270 : ℝ)) (X := (21662975374193/100000000000000 : ℝ)) (Y := (78337025901073/100000000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (58633469/62500000 : ℝ)) (n' := (86729627/100000000 : ℝ)) (Ab := (163752981/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (60329339/31250000 : ℝ)) (τ := (58633469/62500000 : ℝ)) (σ := (62025209/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (58633469/62500000 : ℝ)) (n' := (86729627/100000000 : ℝ)) (Ab := (163752981/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (60329339/31250000 : ℝ)) (τ := (58633469/62500000 : ℝ)) (σ := (62025209/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (58633469/62500000 : ℝ)) (n' := (86729627/100000000 : ℝ)) (Ab := (163752981/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (60329339/31250000 : ℝ)) (τ := (58633469/62500000 : ℝ)) (σ := (62025209/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (58633469/62500000 : ℝ)) (n' := (86729627/100000000 : ℝ)) (Ab := (163752981/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (60329339/31250000 : ℝ)) (τ := (58633469/62500000 : ℝ)) (σ := (62025209/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (58633469/62500000 : ℝ)) (n' := (86729627/100000000 : ℝ)) (Ab := (163752981/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (60329339/31250000 : ℝ)) (τ := (58633469/62500000 : ℝ)) (σ := (62025209/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1696214361/1844321635 : ℝ) ^ p + (1836386386/1844321635 : ℝ) ^ p := by
    exact cert_lt (x := (1696214361/1844321635 : ℝ)) (y := (1836386386/1844321635 : ℝ)) (X := (10821706293831/100000000000000 : ℝ)) (Y := (222945734823/250000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1080434609/1155678365 : ℝ) ^ p + (1147743116/1155678365 : ℝ) ^ p := by
    exact cert_lt (x := (1080434609/1155678365 : ℝ)) (y := (1147743116/1155678365 : ℝ)) (X := (8362236746477/50000000000000 : ℝ)) (Y := (5204720442461/6250000000000 : ℝ)) 425 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (62025209/62500000 : ℝ)) (U := (231135673/200000000 : ℝ)) (Ab := (1696214361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (58633469/62500000 : ℝ)) (σ := (62025209/62500000 : ℝ)) (Ab := (1080434609/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab008
