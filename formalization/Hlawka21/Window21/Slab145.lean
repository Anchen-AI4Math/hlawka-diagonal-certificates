import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 145, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab145 (p : ℝ) (hpa : (817/32 : ℝ) ≤ p) (hpb : p ≤ (409/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (415676038873/22304100000000 : ℝ) (2393707/250000000 : ℝ) (4000000669123/22304100000000 : ℝ) (3033/2500 : ℝ) (973248551/500000000 : ℝ) (973216249/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194214529/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5591/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(2341/5000 : ℝ)
      else (7831/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11861/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (415676038873/22304100000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2393707/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (925540583/1000000000 : ℝ) ^ p + (994191693/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925540583/1000000000 : ℝ)) (y := (994191693/1000000000 : ℝ)) (X := (13835157575751/100000000000000 : ℝ)) (Y := (215412156383/250000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994191693/1000000000 : ℝ) ^ p + (925540583/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994191693/1000000000 : ℝ)) (y := (925540583/1000000000 : ℝ)) (X := (215412156383/250000000000 : ℝ)) (Y := (13835157575751/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (479933069/250000000 : ℝ)) (τ := (925540583/1000000000 : ℝ)) (σ := (994191693/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (79108801/83446752 : ℝ) ^ p + (206223173/208616880 : ℝ) ^ p := by
    exact cert_lt (x := (79108801/83446752 : ℝ)) (y := (206223173/208616880 : ℝ)) (X := (6386792040989/25000000000000 : ℝ)) (Y := (7445283336619/10000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (925540583/1000000000 : ℝ)) (n' := (2607711/3125000 : ℝ)) (Ab := (79108801/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (186183187/200000000 : ℝ) ^ p + (496591427/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (186183187/200000000 : ℝ)) (y := (496591427/500000000 : ℝ)) (X := (8021281378067/50000000000000 : ℝ)) (Y := (41978727766307/50000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496591427/500000000 : ℝ) ^ p + (186183187/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496591427/500000000 : ℝ)) (y := (186183187/200000000 : ℝ)) (X := (41978727766307/50000000000000 : ℝ)) (Y := (8021281378067/50000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1924098789/1000000000 : ℝ)) (τ := (186183187/200000000 : ℝ)) (σ := (496591427/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (796860655/840770833 : ℝ) ^ p + (831196005/840770833 : ℝ) ^ p := by
    exact cert_lt (x := (796860655/840770833 : ℝ)) (y := (831196005/840770833 : ℝ)) (X := (5076274349013/20000000000000 : ℝ)) (Y := (18654657291889/25000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (186183187/200000000 : ℝ)) (n' := (840770833/1000000000 : ℝ)) (Ab := (159372131/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37245057/40000000 : ℝ) ^ p + (993139801/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (37245057/40000000 : ℝ)) (y := (993139801/1000000000 : ℝ)) (X := (1008471623013/6250000000000 : ℝ)) (Y := (20966118023149/25000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993139801/1000000000 : ℝ) ^ p + (37245057/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (993139801/1000000000 : ℝ)) (y := (37245057/40000000 : ℝ)) (X := (20966118023149/25000000000000 : ℝ)) (Y := (1008471623013/6250000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (962133113/500000000 : ℝ)) (τ := (37245057/40000000 : ℝ)) (σ := (993139801/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797086001/841016932 : ℝ) ^ p + (207860526/210254233 : ℝ) ^ p := by
    exact cert_lt (x := (797086001/841016932 : ℝ)) (y := (207860526/210254233 : ℝ)) (X := (12687470992951/50000000000000 : ℝ)) (Y := (74625059023071/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37245057/40000000 : ℝ)) (n' := (210254233/250000000 : ℝ)) (Ab := (797086001/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (465567293/500000000 : ℝ) ^ p + (496569063/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465567293/500000000 : ℝ)) (y := (496569063/500000000 : ℝ)) (X := (16139161469031/100000000000000 : ℝ)) (Y := (83860856522617/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496569063/500000000 : ℝ) ^ p + (465567293/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496569063/500000000 : ℝ)) (y := (465567293/500000000 : ℝ)) (X := (83860856522617/100000000000000 : ℝ)) (Y := (16139161469031/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (240534089/125000000 : ℝ)) (τ := (465567293/500000000 : ℝ)) (σ := (496569063/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (797094738/841026473 : ℝ) ^ p + (831451645/841026473 : ℝ) ^ p := by
    exact cert_lt (x := (797094738/841026473 : ℝ)) (y := (831451645/841026473 : ℝ)) (X := (25374693283659/100000000000000 : ℝ)) (Y := (74625308236767/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (465567293/500000000 : ℝ)) (n' := (841026473/1000000000 : ℝ)) (Ab := (398547369/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (931134903/1000000000 : ℝ) ^ p + (993138061/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931134903/1000000000 : ℝ)) (y := (993138061/1000000000 : ℝ)) (X := (16139301922643/100000000000000 : ℝ)) (Y := (16772143243987/20000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993138061/1000000000 : ℝ) ^ p + (931134903/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993138061/1000000000 : ℝ)) (y := (931134903/1000000000 : ℝ)) (X := (16772143243987/20000000000000 : ℝ)) (Y := (16139301922643/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481068241/250000000 : ℝ)) (τ := (931134903/1000000000 : ℝ)) (σ := (993138061/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797095076/841026843 : ℝ) ^ p + (831452015/841026843 : ℝ) ^ p := by
    exact cert_lt (x := (797095076/841026843 : ℝ)) (y := (831452015/841026843 : ℝ)) (X := (25374682971153/100000000000000 : ℝ)) (Y := (74625317901177/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (931134903/1000000000 : ℝ)) (n' := (841026843/1000000000 : ℝ)) (Ab := (199273769/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (465567457/500000000 : ℝ) ^ p + (993138059/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465567457/500000000 : ℝ)) (y := (993138059/1000000000 : ℝ)) (X := (16139306796449/100000000000000 : ℝ)) (Y := (83860711902933/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993138059/1000000000 : ℝ) ^ p + (465567457/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993138059/1000000000 : ℝ)) (y := (465567457/500000000 : ℝ)) (X := (83860711902933/100000000000000 : ℝ)) (Y := (16139306796449/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1924272973/1000000000 : ℝ)) (τ := (465567457/500000000 : ℝ)) (σ := (993138059/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (99636886/105128357 : ℝ) ^ p + (207863007/210256714 : ℝ) ^ p := by
    exact cert_lt (x := (99636886/105128357 : ℝ)) (y := (207863007/210256714 : ℝ)) (X := (25374682709991/100000000000000 : ℝ)) (Y := (37312659120369/50000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (465567457/500000000 : ℝ)) (n' := (105128357/125000000 : ℝ)) (Ab := (49818443/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (232783729/250000000 : ℝ) ^ p + (496569029/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232783729/250000000 : ℝ)) (y := (496569029/500000000 : ℝ)) (X := (3227861536519/20000000000000 : ℝ)) (Y := (83860709744433/100000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496569029/500000000 : ℝ) ^ p + (232783729/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496569029/500000000 : ℝ)) (y := (232783729/250000000 : ℝ)) (X := (83860709744433/100000000000000 : ℝ)) (Y := (3227861536519/20000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962136487/500000000 : ℝ)) (τ := (232783729/250000000 : ℝ)) (σ := (496569029/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (797095091/841026859 : ℝ) ^ p + (831452031/841026859 : ℝ) ^ p := by
    exact cert_lt (x := (797095091/841026859 : ℝ)) (y := (831452031/841026859 : ℝ)) (X := (25374682837513/100000000000000 : ℝ)) (Y := (37312659159549/50000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (232783729/250000000 : ℝ)) (n' := (841026859/1000000000 : ℝ)) (Ab := (797095091/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962136487/500000000 : ℝ)) (τ := (232783729/250000000 : ℝ)) (σ := (496569029/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (232783729/250000000 : ℝ)) (n' := (841026859/1000000000 : ℝ)) (Ab := (797095091/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962136487/500000000 : ℝ)) (τ := (232783729/250000000 : ℝ)) (σ := (496569029/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (232783729/250000000 : ℝ)) (n' := (841026859/1000000000 : ℝ)) (Ab := (797095091/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962136487/500000000 : ℝ)) (τ := (232783729/250000000 : ℝ)) (σ := (496569029/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (232783729/250000000 : ℝ)) (n' := (841026859/1000000000 : ℝ)) (Ab := (797095091/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962136487/500000000 : ℝ)) (τ := (232783729/250000000 : ℝ)) (σ := (496569029/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1665775998/1805785471 : ℝ) ^ p + (1796210643/1805785471 : ℝ) ^ p := by
    exact cert_lt (x := (1665775998/1805785471 : ℝ)) (y := (1796210643/1805785471 : ℝ)) (X := (12707080071713/100000000000000 : ℝ)) (Y := (10911615039323/12500000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1118161612/1194214529 : ℝ) ^ p + (1184639701/1194214529 : ℝ) ^ p := by
    exact cert_lt (x := (1118161612/1194214529 : ℝ)) (y := (1184639701/1194214529 : ℝ)) (X := (9299309446301/50000000000000 : ℝ)) (Y := (40700690772677/50000000000000 : ℝ)) 409 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496569029/500000000 : ℝ)) (U := (1194214529/1000000000 : ℝ)) (Ab := (832887999/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (232783729/250000000 : ℝ)) (σ := (496569029/500000000 : ℝ)) (Ab := (279540403/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab145
