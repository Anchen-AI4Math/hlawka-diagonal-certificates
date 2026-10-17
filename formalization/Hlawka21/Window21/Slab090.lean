import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 90, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab090 (p : ℝ) (hpa : (381/16 : ℝ) ≤ p) (hpb : p ≤ (763/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (209584810073/10401300000000 : ℝ) (10372511/1000000000 : ℝ) (2000000312039/10401300000000 : ℝ) (3033/2500 : ℝ) (971348087/500000000 : ℝ) (971311029/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193516797/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11127/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4591/10000 : ℝ)
      else (7741/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (209584810073/10401300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10372511/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (459946949/500000000 : ℝ) ^ p + (198772031/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (459946949/500000000 : ℝ)) (y := (198772031/200000000 : ℝ)) (X := (13657515156547/100000000000000 : ℝ)) (Y := (43171251572263/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198772031/200000000 : ℝ) ^ p + (459946949/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198772031/200000000 : ℝ)) (y := (459946949/500000000 : ℝ)) (X := (43171251572263/50000000000000 : ℝ)) (Y := (13657515156547/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913754053/1000000000 : ℝ)) (τ := (459946949/500000000 : ℝ)) (σ := (198772031/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783633539/829278219 : ℝ) ^ p + (818905708/829278219 : ℝ) ^ p := by
    exact cert_lt (x := (783633539/829278219 : ℝ)) (y := (818905708/829278219 : ℝ)) (X := (25926739954453/100000000000000 : ℝ)) (Y := (7407326138023/10000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459946949/500000000 : ℝ)) (n' := (829278219/1000000000 : ℝ)) (Ab := (783633539/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (57844061/62500000 : ℝ) ^ p + (992819003/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57844061/62500000 : ℝ)) (y := (992819003/1000000000 : ℝ)) (X := (1973574504981/12500000000000 : ℝ)) (Y := (84211421367551/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992819003/1000000000 : ℝ) ^ p + (57844061/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (992819003/1000000000 : ℝ)) (y := (57844061/62500000 : ℝ)) (X := (84211421367551/100000000000000 : ℝ)) (Y := (1973574504981/12500000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918323979/1000000000 : ℝ)) (τ := (57844061/62500000 : ℝ)) (σ := (992819003/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (394837090/417955919 : ℝ) ^ p + (825539327/835911838 : ℝ) ^ p := by
    exact cert_lt (x := (394837090/417955919 : ℝ)) (y := (825539327/835911838 : ℝ)) (X := (25749003883369/100000000000000 : ℝ)) (Y := (74250997121721/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (57844061/62500000 : ℝ)) (n' := (417955919/500000000 : ℝ)) (Ab := (39483709/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925746563/1000000000 : ℝ) ^ p + (992770241/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925746563/1000000000 : ℝ)) (y := (992770241/1000000000 : ℝ)) (X := (3971789438467/25000000000000 : ℝ)) (Y := (42056429245059/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992770241/1000000000 : ℝ) ^ p + (925746563/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992770241/1000000000 : ℝ)) (y := (925746563/1000000000 : ℝ)) (X := (42056429245059/50000000000000 : ℝ)) (Y := (3971789438467/25000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (479629201/250000000 : ℝ)) (τ := (925746563/1000000000 : ℝ)) (σ := (992770241/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (157986682/167239313 : ℝ) ^ p + (825824054/836196565 : ℝ) ^ p := by
    exact cert_lt (x := (157986682/167239313 : ℝ)) (y := (825824054/836196565 : ℝ)) (X := (643535725129/2500000000000 : ℝ)) (Y := (74258571805067/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925746563/1000000000 : ℝ)) (n' := (167239313/200000000 : ℝ)) (Ab := (78993341/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (115719607/125000000 : ℝ) ^ p + (248192039/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115719607/125000000 : ℝ)) (y := (248192039/250000000 : ℝ)) (X := (7945685058419/50000000000000 : ℝ)) (Y := (1682172930679/2000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248192039/250000000 : ℝ) ^ p + (115719607/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248192039/250000000 : ℝ)) (y := (115719607/125000000 : ℝ)) (X := (1682172930679/2000000000000 : ℝ)) (Y := (7945685058419/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (479631253/250000000 : ℝ)) (τ := (115719607/125000000 : ℝ)) (σ := (248192039/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (789944453/836208694 : ℝ) ^ p + (825836183/836208694 : ℝ) ^ p := by
    exact cert_lt (x := (789944453/836208694 : ℝ)) (y := (825836183/836208694 : ℝ)) (X := (1608819162199/6250000000000 : ℝ)) (Y := (37129447189307/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (115719607/125000000 : ℝ)) (n' := (418104347/500000000 : ℝ)) (Ab := (789944453/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (462878647/500000000 : ℝ) ^ p + (992768067/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462878647/500000000 : ℝ)) (y := (992768067/1000000000 : ℝ)) (X := (794577469503/5000000000000 : ℝ)) (Y := (10513558343439/12500000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992768067/1000000000 : ℝ) ^ p + (462878647/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992768067/1000000000 : ℝ)) (y := (462878647/500000000 : ℝ)) (X := (10513558343439/12500000000000 : ℝ)) (Y := (794577469503/5000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1918525361/1000000000 : ℝ)) (τ := (462878647/500000000 : ℝ)) (σ := (992768067/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789944923/836209210 : ℝ) ^ p + (825836699/836209210 : ℝ) ^ p := by
    exact cert_lt (x := (789944923/836209210 : ℝ)) (y := (825836699/836209210 : ℝ)) (X := (25741093035729/100000000000000 : ℝ)) (Y := (2970356324063/4000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (462878647/500000000 : ℝ)) (n' := (83620921/100000000 : ℝ)) (Ab := (789944923/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (7232479/7812500 : ℝ) ^ p + (15512001/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (7232479/7812500 : ℝ)) (y := (15512001/15625000 : ℝ)) (X := (7945778378747/50000000000000 : ℝ)) (Y := (42054230343651/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (15512001/15625000 : ℝ) ^ p + (7232479/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (15512001/15625000 : ℝ)) (y := (7232479/7812500 : ℝ)) (X := (42054230343651/50000000000000 : ℝ)) (Y := (7945778378747/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (29976959/15625000 : ℝ)) (τ := (7232479/7812500 : ℝ)) (σ := (15512001/15625000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789944942/836209231 : ℝ) ^ p + (825836720/836209231 : ℝ) ^ p := by
    exact cert_lt (x := (789944942/836209231 : ℝ)) (y := (825836720/836209231 : ℝ)) (X := (25741092384511/100000000000000 : ℝ)) (Y := (74258908660067/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (7232479/7812500 : ℝ)) (n' := (836209231/1000000000 : ℝ)) (Ab := (394972471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (462878657/500000000 : ℝ) ^ p + (992768063/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462878657/500000000 : ℝ)) (y := (992768063/1000000000 : ℝ)) (X := (7945778788049/50000000000000 : ℝ)) (Y := (2628389333351/3125000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992768063/1000000000 : ℝ) ^ p + (462878657/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992768063/1000000000 : ℝ)) (y := (462878657/500000000 : ℝ)) (X := (2628389333351/3125000000000 : ℝ)) (Y := (7945778788049/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (789944945/836209234 : ℝ) ^ p + (825836723/836209234 : ℝ) ^ p := by
    exact cert_lt (x := (789944945/836209234 : ℝ)) (y := (825836723/836209234 : ℝ)) (X := (25741092513471/100000000000000 : ℝ)) (Y := (74258908739851/100000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (n' := (418104617/500000000 : ℝ)) (Ab := (157988989/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918525377/1000000000 : ℝ)) (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657418297/1806483203 : ℝ) ^ p + (1796110692/1806483203 : ℝ) ^ p := by
    exact cert_lt (x := (1657418297/1806483203 : ℝ)) (y := (1796110692/1806483203 : ℝ)) (X := (12829237891227/100000000000000 : ℝ)) (Y := (43585381167817/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112696415/1193516797 : ℝ) ^ p + (1183144286/1193516797 : ℝ) ^ p := by
    exact cert_lt (x := (1112696415/1193516797 : ℝ)) (y := (1183144286/1193516797 : ℝ)) (X := (3757887523099/20000000000000 : ℝ)) (Y := (40605281480501/50000000000000 : ℝ)) 763 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992768063/1000000000 : ℝ)) (U := (1193516797/1000000000 : ℝ)) (Ab := (1657418297/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (462878657/500000000 : ℝ)) (σ := (992768063/1000000000 : ℝ)) (Ab := (222539283/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab090
