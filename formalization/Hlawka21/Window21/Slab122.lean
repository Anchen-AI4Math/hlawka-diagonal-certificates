import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 122, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab122 (p : ℝ) (hpa : (397/16 : ℝ) ≤ p) (hpb : p ≤ (795/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (260674154971/13547625000000 : ℝ) (1978641/200000000 : ℝ) (2000000325143/10838100000000 : ℝ) (3033/2500 : ℝ) (486242677/250000000 : ℝ) (486225591/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193923711/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(279/250 : ℝ) ≤ X j i ∧ X j i ≤ -(2323/5000 : ℝ)
      else (1559/2000 : ℝ) ≤ X j i ∧ X j i ≤ (741/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (260674154971/13547625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1978641/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (115409839/125000000 : ℝ) ^ p + (497028647/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115409839/125000000 : ℝ)) (y := (497028647/500000000 : ℝ)) (X := (2752753327899/20000000000000 : ℝ)) (Y := (86236252347333/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497028647/500000000 : ℝ) ^ p + (115409839/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (497028647/500000000 : ℝ)) (y := (115409839/125000000 : ℝ)) (X := (86236252347333/100000000000000 : ℝ)) (Y := (2752753327899/20000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958668003/500000000 : ℝ)) (τ := (115409839/125000000 : ℝ)) (σ := (497028647/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (394049089/416200311 : ℝ) ^ p + (91389713/92488958 : ℝ) ^ p := by
    exact cert_lt (x := (394049089/416200311 : ℝ)) (y := (91389713/92488958 : ℝ)) (X := (5139719784701/20000000000000 : ℝ)) (Y := (74301402383137/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115409839/125000000 : ℝ)) (n' := (416200311/500000000 : ℝ)) (Ab := (394049089/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (464376103/500000000 : ℝ) ^ p + (62064669/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (464376103/500000000 : ℝ)) (y := (62064669/62500000 : ℝ)) (X := (15940873121797/100000000000000 : ℝ)) (Y := (4202957210257/5000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (62064669/62500000 : ℝ) ^ p + (464376103/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62064669/62500000 : ℝ)) (y := (464376103/500000000 : ℝ)) (X := (4202957210257/5000000000000 : ℝ)) (Y := (15940873121797/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (192178691/100000000 : ℝ)) (τ := (464376103/500000000 : ℝ)) (σ := (62064669/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (793981919/838840017 : ℝ) ^ p + (276315604/279613339 : ℝ) ^ p := by
    exact cert_lt (x := (793981919/838840017 : ℝ)) (y := (276315604/279613339 : ℝ)) (X := (12763984436359/50000000000000 : ℝ)) (Y := (74472032392951/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (464376103/500000000 : ℝ)) (n' := (838840017/1000000000 : ℝ)) (Ab := (793981919/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (928974977/1000000000 : ℝ) ^ p + (49649469/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (928974977/1000000000 : ℝ)) (y := (49649469/50000000 : ℝ)) (X := (8018068740109/50000000000000 : ℝ)) (Y := (41981940013919/50000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (49649469/50000000 : ℝ) ^ p + (928974977/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49649469/50000000 : ℝ)) (y := (928974977/1000000000 : ℝ)) (X := (41981940013919/50000000000000 : ℝ)) (Y := (8018068740109/50000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1921964357/1000000000 : ℝ)) (τ := (928974977/1000000000 : ℝ)) (σ := (49649469/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (794220627/839101310 : ℝ) ^ p + (165841621/167820262 : ℝ) ^ p := by
    exact cert_lt (x := (794220627/839101310 : ℝ)) (y := (165841621/167820262 : ℝ)) (X := (25521092875459/100000000000000 : ℝ)) (Y := (74478908669227/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (928974977/1000000000 : ℝ)) (n' := (83910131/100000000 : ℝ)) (Ab := (794220627/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (928983953/1000000000 : ℝ) ^ p + (992987547/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (928983953/1000000000 : ℝ)) (y := (992987547/1000000000 : ℝ)) (X := (1603998734767/10000000000000 : ℝ)) (Y := (83960029520517/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992987547/1000000000 : ℝ) ^ p + (928983953/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992987547/1000000000 : ℝ)) (y := (928983953/1000000000 : ℝ)) (X := (83960029520517/100000000000000 : ℝ)) (Y := (1603998734767/10000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (3843943/2000000 : ℝ)) (τ := (928983953/1000000000 : ℝ)) (σ := (992987547/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (794230244/839111837 : ℝ) ^ p + (829218632/839111837 : ℝ) ^ p := by
    exact cert_lt (x := (794230244/839111837 : ℝ)) (y := (829218632/839111837 : ℝ)) (X := (1595050994199/6250000000000 : ℝ)) (Y := (18619796406099/25000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (928983953/1000000000 : ℝ)) (n' := (839111837/1000000000 : ℝ)) (Ab := (198557561/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464492157/500000000 : ℝ) ^ p + (496493737/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (464492157/500000000 : ℝ)) (y := (496493737/500000000 : ℝ)) (X := (16040142201579/100000000000000 : ℝ)) (Y := (10494984521993/12500000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496493737/500000000 : ℝ) ^ p + (464492157/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496493737/500000000 : ℝ)) (y := (464492157/500000000 : ℝ)) (X := (10494984521993/12500000000000 : ℝ)) (Y := (16040142201579/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (480492947/250000000 : ℝ)) (τ := (464492157/500000000 : ℝ)) (σ := (496493737/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (794230631/839112261 : ℝ) ^ p + (276406352/279704087 : ℝ) ^ p := by
    exact cert_lt (x := (794230631/839112261 : ℝ)) (y := (276406352/279704087 : ℝ)) (X := (25520804474359/100000000000000 : ℝ)) (Y := (744791967793/1000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464492157/500000000 : ℝ)) (n' := (839112261/1000000000 : ℝ)) (Ab := (794230631/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (116123041/125000000 : ℝ) ^ p + (992987471/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116123041/125000000 : ℝ)) (y := (992987471/1000000000 : ℝ)) (X := (16040148207023/100000000000000 : ℝ)) (Y := (41979934937059/50000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992987471/1000000000 : ℝ) ^ p + (116123041/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992987471/1000000000 : ℝ)) (y := (116123041/125000000 : ℝ)) (X := (41979934937059/50000000000000 : ℝ)) (Y := (16040148207023/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1921971799/1000000000 : ℝ)) (τ := (116123041/125000000 : ℝ)) (σ := (992987471/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (794230646/839112277 : ℝ) ^ p + (829219072/839112277 : ℝ) ^ p := by
    exact cert_lt (x := (794230646/839112277 : ℝ)) (y := (829219072/839112277 : ℝ)) (X := (12760402179619/50000000000000 : ℝ)) (Y := (930989965003/1250000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (116123041/125000000 : ℝ)) (n' := (839112277/1000000000 : ℝ)) (Ab := (397115323/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (92898433/100000000 : ℝ) ^ p + (99298747/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (92898433/100000000 : ℝ)) (y := (99298747/100000000 : ℝ)) (X := (16040149064943/100000000000000 : ℝ)) (Y := (83959867773509/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (99298747/100000000 : ℝ) ^ p + (92898433/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (99298747/100000000 : ℝ)) (y := (92898433/100000000 : ℝ)) (X := (83959867773509/100000000000000 : ℝ)) (Y := (16040149064943/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (9609859/5000000 : ℝ)) (τ := (92898433/100000000 : ℝ)) (σ := (99298747/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (264743549/279704093 : ℝ) ^ p + (276406358/279704093 : ℝ) ^ p := by
    exact cert_lt (x := (264743549/279704093 : ℝ)) (y := (276406358/279704093 : ℝ)) (X := (12760401823169/50000000000000 : ℝ)) (Y := (74479197252857/100000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (92898433/100000000 : ℝ)) (n' := (839112279/1000000000 : ℝ)) (Ab := (794230647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (9609859/5000000 : ℝ)) (τ := (92898433/100000000 : ℝ)) (σ := (99298747/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (92898433/100000000 : ℝ)) (n' := (839112279/1000000000 : ℝ)) (Ab := (794230647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (9609859/5000000 : ℝ)) (τ := (92898433/100000000 : ℝ)) (σ := (99298747/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (92898433/100000000 : ℝ)) (n' := (839112279/1000000000 : ℝ)) (Ab := (794230647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (9609859/5000000 : ℝ)) (τ := (92898433/100000000 : ℝ)) (σ := (99298747/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (92898433/100000000 : ℝ)) (n' := (839112279/1000000000 : ℝ)) (Ab := (794230647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (9609859/5000000 : ℝ)) (τ := (92898433/100000000 : ℝ)) (σ := (99298747/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1662416006/1806076289 : ℝ) ^ p + (1796183084/1806076289 : ℝ) ^ p := by
    exact cert_lt (x := (1662416006/1806076289 : ℝ)) (y := (1796183084/1806076289 : ℝ)) (X := (1275601291713/10000000000000 : ℝ)) (Y := (43621993708821/50000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1115947969/1193923711 : ℝ) ^ p + (1184030506/1193923711 : ℝ) ^ p := by
    exact cert_lt (x := (1115947969/1193923711 : ℝ)) (y := (1184030506/1193923711 : ℝ)) (X := (3735058781123/20000000000000 : ℝ)) (Y := (16264941322379/20000000000000 : ℝ)) 795 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99298747/100000000 : ℝ)) (U := (1193923711/1000000000 : ℝ)) (Ab := (831208003/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (92898433/100000000 : ℝ)) (σ := (99298747/100000000 : ℝ)) (Ab := (1115947969/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab122
