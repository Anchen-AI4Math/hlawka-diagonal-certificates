import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 153, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab153 (p : ℝ) (hpa : (825/32 : ℝ) ≤ p) (hpb : p ≤ (413/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (33216503/1801800000 : ℝ) (2367193/250000000 : ℝ) (160000027027/900900000000 : ℝ) (3033/2500 : ℝ) (973504181/500000000 : ℝ) (486736247/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194315107/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1119/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(2347/5000 : ℝ)
      else (7843/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5931/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (33216503/1801800000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2367193/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (926296471/1000000000 : ℝ) ^ p + (994237087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926296471/1000000000 : ℝ)) (y := (994237087/1000000000 : ℝ)) (X := (2771817391659/20000000000000 : ℝ)) (Y := (86140932815697/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994237087/1000000000 : ℝ) ^ p + (926296471/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994237087/1000000000 : ℝ)) (y := (926296471/1000000000 : ℝ)) (X := (86140932815697/100000000000000 : ℝ)) (Y := (2771817391659/20000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (960266779/500000000 : ℝ)) (τ := (926296471/1000000000 : ℝ)) (σ := (994237087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (396044169/417577372 : ℝ) ^ p + (206421493/208788686 : ℝ) ^ p := by
    exact cert_lt (x := (396044169/417577372 : ℝ)) (y := (206421493/208788686 : ℝ)) (X := (5099347182237/20000000000000 : ℝ)) (Y := (74503265299607/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (926296471/1000000000 : ℝ)) (n' := (104394343/125000000 : ℝ)) (Ab := (396044169/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (465818969/500000000 : ℝ) ^ p + (993233083/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465818969/500000000 : ℝ)) (y := (993233083/1000000000 : ℝ)) (X := (8038267663057/50000000000000 : ℝ)) (Y := (83923483161007/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993233083/1000000000 : ℝ) ^ p + (465818969/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993233083/1000000000 : ℝ)) (y := (465818969/500000000 : ℝ)) (X := (83923483161007/100000000000000 : ℝ)) (Y := (8038267663057/50000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1924871021/1000000000 : ℝ)) (τ := (465818969/500000000 : ℝ)) (σ := (993233083/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (398911382/420705745 : ℝ) ^ p + (415971359/420705745 : ℝ) ^ p := by
    exact cert_lt (x := (398911382/420705745 : ℝ)) (y := (415971359/420705745 : ℝ)) (X := (12666284935493/50000000000000 : ℝ)) (Y := (74667431497243/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (465818969/500000000 : ℝ)) (n' := (84141149/100000000 : ℝ)) (Ab := (199455691/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (931844381/1000000000 : ℝ) ^ p + (993190783/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931844381/1000000000 : ℝ)) (y := (993190783/1000000000 : ℝ)) (X := (8084371801901/50000000000000 : ℝ)) (Y := (83831274160753/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993190783/1000000000 : ℝ) ^ p + (931844381/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993190783/1000000000 : ℝ)) (y := (931844381/1000000000 : ℝ)) (X := (83831274160753/100000000000000 : ℝ)) (Y := (8084371801901/50000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (481258791/250000000 : ℝ)) (τ := (931844381/1000000000 : ℝ)) (σ := (993190783/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (798043713/841652600 : ℝ) ^ p + (208045957/210413150 : ℝ) ^ p := by
    exact cert_lt (x := (798043713/841652600 : ℝ)) (y := (208045957/210413150 : ℝ)) (X := (12663142846327/50000000000000 : ℝ)) (Y := (74673715862759/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (931844381/1000000000 : ℝ)) (n' := (4208263/5000000 : ℝ)) (Ab := (798043713/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (931852281/1000000000 : ℝ) ^ p + (993189159/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931852281/1000000000 : ℝ)) (y := (993189159/1000000000 : ℝ)) (X := (16172282238427/100000000000000 : ℝ)) (Y := (41913867987333/50000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993189159/1000000000 : ℝ) ^ p + (931852281/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993189159/1000000000 : ℝ)) (y := (931852281/1000000000 : ℝ)) (X := (41913867987333/50000000000000 : ℝ)) (Y := (16172282238427/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (12031509/6250000 : ℝ)) (τ := (931852281/1000000000 : ℝ)) (σ := (993189159/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (266017389/280553942 : ℝ) ^ p + (416096527/420830913 : ℝ) ^ p := by
    exact cert_lt (x := (266017389/280553942 : ℝ)) (y := (416096527/420830913 : ℝ)) (X := (12663022442453/50000000000000 : ℝ)) (Y := (37336978135323/50000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (931852281/1000000000 : ℝ)) (n' := (420830913/500000000 : ℝ)) (Ab := (798052167/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (931852583/1000000000 : ℝ) ^ p + (993189097/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931852583/1000000000 : ℝ)) (y := (993189097/1000000000 : ℝ)) (X := (8086208763793/50000000000000 : ℝ)) (Y := (41913800449489/50000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993189097/1000000000 : ℝ) ^ p + (931852583/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993189097/1000000000 : ℝ)) (y := (931852583/1000000000 : ℝ)) (X := (41913800449489/50000000000000 : ℝ)) (Y := (8086208763793/50000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (24063021/12500000 : ℝ)) (τ := (931852583/1000000000 : ℝ)) (σ := (993189097/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (399026245/420831089 : ℝ) ^ p + (416096703/420831089 : ℝ) ^ p := by
    exact cert_lt (x := (399026245/420831089 : ℝ)) (y := (416096703/420831089 : ℝ)) (X := (1013041442781/4000000000000 : ℝ)) (Y := (1493479308857/2000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (931852583/1000000000 : ℝ)) (n' := (420831089/500000000 : ℝ)) (Ab := (79805249/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (465926297/500000000 : ℝ) ^ p + (198637819/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (465926297/500000000 : ℝ)) (y := (198637819/200000000 : ℝ)) (X := (16172422455357/100000000000000 : ℝ)) (Y := (83827596541701/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198637819/200000000 : ℝ) ^ p + (465926297/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198637819/200000000 : ℝ)) (y := (465926297/500000000 : ℝ)) (X := (83827596541701/100000000000000 : ℝ)) (Y := (16172422455357/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1925041689/1000000000 : ℝ)) (τ := (465926297/500000000 : ℝ)) (σ := (198637819/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (798052502/841662191 : ℝ) ^ p + (832193419/841662191 : ℝ) ^ p := by
    exact cert_lt (x := (798052502/841662191 : ℝ)) (y := (832193419/841662191 : ℝ)) (X := (3165754475267/12500000000000 : ℝ)) (Y := (18668491445399/25000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (465926297/500000000 : ℝ)) (n' := (841662191/1000000000 : ℝ)) (Ab := (399026251/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (232963149/250000000 : ℝ) ^ p + (496594547/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232963149/250000000 : ℝ)) (y := (496594547/500000000 : ℝ)) (X := (4043105837829/25000000000000 : ℝ)) (Y := (83827594363063/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496594547/500000000 : ℝ) ^ p + (232963149/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496594547/500000000 : ℝ)) (y := (232963149/250000000 : ℝ)) (X := (83827594363063/100000000000000 : ℝ)) (Y := (4043105837829/25000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (192504169/100000000 : ℝ)) (τ := (232963149/250000000 : ℝ)) (σ := (496594547/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (798052503/841662193 : ℝ) ^ p + (832193421/841662193 : ℝ) ^ p := by
    exact cert_lt (x := (798052503/841662193 : ℝ)) (y := (832193421/841662193 : ℝ)) (X := (6331508766967/25000000000000 : ℝ)) (Y := (74673965833711/100000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (232963149/250000000 : ℝ)) (n' := (841662193/1000000000 : ℝ)) (Ab := (798052503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (192504169/100000000 : ℝ)) (τ := (232963149/250000000 : ℝ)) (σ := (496594547/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (232963149/250000000 : ℝ)) (n' := (841662193/1000000000 : ℝ)) (Ab := (798052503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (192504169/100000000 : ℝ)) (τ := (232963149/250000000 : ℝ)) (σ := (496594547/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (232963149/250000000 : ℝ)) (n' := (841662193/1000000000 : ℝ)) (Ab := (798052503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (192504169/100000000 : ℝ)) (τ := (232963149/250000000 : ℝ)) (σ := (496594547/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (232963149/250000000 : ℝ)) (n' := (841662193/1000000000 : ℝ)) (Ab := (798052503/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (192504169/100000000 : ℝ)) (τ := (232963149/250000000 : ℝ)) (σ := (496594547/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1666902518/1805684893 : ℝ) ^ p + (1796216121/1805684893 : ℝ) ^ p := by
    exact cert_lt (x := (1666902518/1805684893 : ℝ)) (y := (1796216121/1805684893 : ℝ)) (X := (396585120473/3125000000000 : ℝ)) (Y := (17461855301001/20000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1118908753/1194315107 : ℝ) ^ p + (1184846335/1194315107 : ℝ) ^ p := by
    exact cert_lt (x := (1118908753/1194315107 : ℝ)) (y := (1184846335/1194315107 : ℝ)) (X := (2321614959553/12500000000000 : ℝ)) (Y := (20356770197933/25000000000000 : ℝ)) 413 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496594547/500000000 : ℝ)) (U := (1194315107/1000000000 : ℝ)) (Ab := (833451259/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (232963149/250000000 : ℝ)) (σ := (496594547/500000000 : ℝ)) (Ab := (1118908753/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab153
