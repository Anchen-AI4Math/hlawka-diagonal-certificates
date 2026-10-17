import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 34, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab034 (p : ℝ) (hpa : (353/16 : ℝ) ≤ p) (hpb : p ≤ (707/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1058200634683/48184500000000 : ℝ) (11331179/1000000000 : ℝ) (2000000289107/9636900000000 : ℝ) (3033/2500 : ℝ) (242278507/125000000 : ℝ) (969070963/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192809927/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2213/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2241/5000 : ℝ)
      else (7633/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11837/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1058200634683/48184500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11331179/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (182638957/200000000 : ℝ) ^ p + (99348377/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (182638957/200000000 : ℝ)) (y := (99348377/100000000 : ℝ)) (X := (6724625829629/50000000000000 : ℝ)) (Y := (86550764754611/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99348377/100000000 : ℝ) ^ p + (182638957/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (99348377/100000000 : ℝ)) (y := (182638957/200000000 : ℝ)) (X := (86550764754611/100000000000000 : ℝ)) (Y := (6724625829629/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381335711/200000000 : ℝ)) (τ := (182638957/200000000 : ℝ)) (σ := (99348377/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (154965861/164599028 : ℝ) ^ p + (811663961/822995140 : ℝ) ^ p := by
    exact cert_lt (x := (154965861/164599028 : ℝ)) (y := (811663961/822995140 : ℝ)) (X := (3297975809717/12500000000000 : ℝ)) (Y := (18404048738763/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (182638957/200000000 : ℝ)) (n' := (41149757/50000000 : ℝ)) (Ab := (154965861/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (459522037/500000000 : ℝ) ^ p + (496206543/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (459522037/500000000 : ℝ)) (y := (496206543/500000000 : ℝ)) (X := (3097363932443/20000000000000 : ℝ)) (Y := (84513196865727/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496206543/500000000 : ℝ) ^ p + (459522037/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496206543/500000000 : ℝ)) (y := (459522037/500000000 : ℝ)) (X := (84513196865727/100000000000000 : ℝ)) (Y := (3097363932443/20000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (47786429/25000000 : ℝ)) (τ := (459522037/500000000 : ℝ)) (σ := (496206543/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (390572971/414988856 : ℝ) ^ p + (818646533/829977712 : ℝ) ^ p := by
    exact cert_lt (x := (390572971/414988856 : ℝ)) (y := (818646533/829977712 : ℝ)) (X := (3274068008863/12500000000000 : ℝ)) (Y := (36903728476563/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (459522037/500000000 : ℝ)) (n' := (51873607/62500000 : ℝ)) (Ab := (390572971/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (459662109/500000000 : ℝ) ^ p + (3101117/3125000 : ℝ) ^ p := by
    exact cert_lt (x := (459662109/500000000 : ℝ)) (y := (3101117/3125000 : ℝ)) (X := (3897863455219/25000000000000 : ℝ)) (Y := (4220428073479/5000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (3101117/3125000 : ℝ) ^ p + (459662109/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (3101117/3125000 : ℝ)) (y := (459662109/500000000 : ℝ)) (X := (4220428073479/5000000000000 : ℝ)) (Y := (3897863455219/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (955840829/500000000 : ℝ)) (τ := (459662109/500000000 : ℝ)) (σ := (3101117/3125000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (781447423/830311043 : ℝ) ^ p + (818979864/830311043 : ℝ) ^ p := by
    exact cert_lt (x := (781447423/830311043 : ℝ)) (y := (818979864/830311043 : ℝ)) (X := (26183482666269/100000000000000 : ℝ)) (Y := (1476330372651/2000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (459662109/500000000 : ℝ)) (n' := (830311043/1000000000 : ℝ)) (Ab := (781447423/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (919337487/1000000000 : ℝ) ^ p + (496177397/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (919337487/1000000000 : ℝ)) (y := (496177397/500000000 : ℝ)) (X := (3899106628487/25000000000000 : ℝ)) (Y := (84403589076757/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496177397/500000000 : ℝ) ^ p + (919337487/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496177397/500000000 : ℝ)) (y := (919337487/1000000000 : ℝ)) (X := (84403589076757/100000000000000 : ℝ)) (Y := (3899106628487/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1911692281/1000000000 : ℝ)) (τ := (919337487/1000000000 : ℝ)) (σ := (496177397/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (781461699/830326828 : ℝ) ^ p + (818995649/830326828 : ℝ) ^ p := by
    exact cert_lt (x := (781461699/830326828 : ℝ)) (y := (818995649/830326828 : ℝ)) (X := (26183053272687/100000000000000 : ℝ)) (Y := (36908473798643/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (919337487/1000000000 : ℝ)) (n' := (207581707/250000000 : ℝ)) (Ab := (781461699/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (459669057/500000000 : ℝ) ^ p + (992354669/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459669057/500000000 : ℝ)) (y := (992354669/1000000000 : ℝ)) (X := (7798330763027/50000000000000 : ℝ)) (Y := (3376134167291/4000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992354669/1000000000 : ℝ) ^ p + (459669057/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992354669/1000000000 : ℝ)) (y := (459669057/500000000 : ℝ)) (X := (3376134167291/4000000000000 : ℝ)) (Y := (7798330763027/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1911692783/1000000000 : ℝ)) (τ := (459669057/500000000 : ℝ)) (σ := (992354669/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (130243729/138387929 : ℝ) ^ p + (818996395/830327574 : ℝ) ^ p := by
    exact cert_lt (x := (130243729/138387929 : ℝ)) (y := (818996395/830327574 : ℝ)) (X := (6545758303397/25000000000000 : ℝ)) (Y := (73816967869839/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (459669057/500000000 : ℝ)) (n' := (415163787/500000000 : ℝ)) (Ab := (390731187/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (28729317/31250000 : ℝ) ^ p + (992354663/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28729317/31250000 : ℝ)) (y := (992354663/1000000000 : ℝ)) (X := (15596672770737/100000000000000 : ℝ)) (Y := (21100835726839/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992354663/1000000000 : ℝ) ^ p + (28729317/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (992354663/1000000000 : ℝ)) (y := (28729317/31250000 : ℝ)) (X := (21100835726839/25000000000000 : ℝ)) (Y := (15596672770737/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1911692807/1000000000 : ℝ)) (τ := (28729317/31250000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (260487469/276775870 : ℝ) ^ p + (818996431/830327610 : ℝ) ^ p := by
    exact cert_lt (x := (260487469/276775870 : ℝ)) (y := (818996431/830327610 : ℝ)) (X := (26183032561141/100000000000000 : ℝ)) (Y := (73816968848139/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (28729317/31250000 : ℝ)) (n' := (83032761/100000000 : ℝ)) (Ab := (781462407/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (183867629/200000000 : ℝ) ^ p + (992354663/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183867629/200000000 : ℝ)) (y := (992354663/1000000000 : ℝ)) (X := (389916828639/2500000000000 : ℝ)) (Y := (21100835726839/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992354663/1000000000 : ℝ) ^ p + (183867629/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992354663/1000000000 : ℝ)) (y := (183867629/200000000 : ℝ)) (X := (21100835726839/25000000000000 : ℝ)) (Y := (389916828639/2500000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (781462408/830327611 : ℝ) ^ p + (818996432/830327611 : ℝ) ^ p := by
    exact cert_lt (x := (781462408/830327611 : ℝ)) (y := (818996432/830327611 : ℝ)) (X := (5236606520941/20000000000000 : ℝ)) (Y := (36908484437657/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1647632392/1807190073 : ℝ) ^ p + (1795858894/1807190073 : ℝ) ^ p := by
    exact cert_lt (x := (1647632392/1807190073 : ℝ)) (y := (1795858894/1807190073 : ℝ)) (X := (2594832346781/20000000000000 : ℝ)) (Y := (17405167695807/20000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (368823728/397603309 : ℝ) ^ p + (1181478748/1192809927 : ℝ) ^ p := by
    exact cert_lt (x := (368823728/397603309 : ℝ)) (y := (1181478748/1192809927 : ℝ)) (X := (19013226470993/100000000000000 : ℝ)) (Y := (80986773988897/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992354663/1000000000 : ℝ)) (U := (1192809927/1000000000 : ℝ)) (Ab := (205954049/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ)) (Ab := (69154449/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab034
