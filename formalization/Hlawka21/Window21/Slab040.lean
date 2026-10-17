import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 40, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab040 (p : ℝ) (hpa : (89/4 : ℝ) ≤ p) (hpb : p ≤ (713/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (16515984943/759281250000 : ℝ) (11220217/1000000000 : ℝ) (500000072891/2429700000000 : ℝ) (3033/2500 : ℝ) (242342479/125000000 : ℝ) (484663781/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (74555291/62500000 : ℝ)) ∧
    (∀ j i, if j = i then -(692/625 : ℝ) ≤ X j i ∧ X j i ≤ -(2247/5000 : ℝ)
      else (1529/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11839/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (16515984943/759281250000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11220217/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (913965461/1000000000 : ℝ) ^ p + (124190769/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (913965461/1000000000 : ℝ)) (y := (124190769/125000000 : ℝ)) (X := (1684134456557/12500000000000 : ℝ)) (Y := (86526941145973/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124190769/125000000 : ℝ) ^ p + (913965461/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124190769/125000000 : ℝ)) (y := (913965461/1000000000 : ℝ)) (X := (86526941145973/100000000000000 : ℝ)) (Y := (1684134456557/12500000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1907491613/1000000000 : ℝ)) (τ := (913965461/1000000000 : ℝ)) (σ := (124190769/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (129306679/137287487 : ℝ) ^ p + (812504705/823724922 : ℝ) ^ p := by
    exact cert_lt (x := (129306679/137287487 : ℝ)) (y := (812504705/823724922 : ℝ)) (X := (3291355191291/12500000000000 : ℝ)) (Y := (73669159582747/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (913965461/1000000000 : ℝ)) (n' := (411862461/500000000 : ℝ)) (Ab := (387920037/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (919789717/1000000000 : ℝ) ^ p + (496229187/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (919789717/1000000000 : ℝ)) (y := (496229187/500000000 : ℝ)) (X := (15521564860211/100000000000000 : ℝ)) (Y := (42239225843887/50000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496229187/500000000 : ℝ) ^ p + (919789717/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496229187/500000000 : ℝ)) (y := (919789717/1000000000 : ℝ)) (X := (42239225843887/50000000000000 : ℝ)) (Y := (15521564860211/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1912248091/1000000000 : ℝ)) (τ := (919789717/1000000000 : ℝ)) (σ := (496229187/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (391063687/415334930 : ℝ) ^ p + (819449643/830669860 : ℝ) ^ p := by
    exact cert_lt (x := (391063687/415334930 : ℝ)) (y := (819449643/830669860 : ℝ)) (X := (13070547490559/50000000000000 : ℝ)) (Y := (73858906263413/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (919789717/1000000000 : ℝ)) (n' := (41533493/50000000 : ℝ)) (Ab := (391063687/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (230016337/250000000 : ℝ) ^ p + (992403523/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230016337/250000000 : ℝ)) (y := (992403523/1000000000 : ℝ)) (X := (15625532928807/100000000000000 : ℝ)) (Y := (84374483047319/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992403523/1000000000 : ℝ) ^ p + (230016337/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992403523/1000000000 : ℝ)) (y := (230016337/250000000 : ℝ)) (X := (84374483047319/100000000000000 : ℝ)) (Y := (15625532928807/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1912468871/1000000000 : ℝ)) (τ := (230016337/250000000 : ℝ)) (σ := (992403523/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (391211947/415498730 : ℝ) ^ p + (819777243/830997460 : ℝ) ^ p := by
    exact cert_lt (x := (391211947/415498730 : ℝ)) (y := (819777243/830997460 : ℝ)) (X := (26132211252857/100000000000000 : ℝ)) (Y := (73867789895233/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (230016337/250000000 : ℝ)) (n' := (41549873/50000000 : ℝ)) (Ab := (391211947/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (115009781/125000000 : ℝ) ^ p + (496200473/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115009781/125000000 : ℝ)) (y := (496200473/500000000 : ℝ)) (X := (7815207534349/50000000000000 : ℝ)) (Y := (84369601418009/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496200473/500000000 : ℝ) ^ p + (115009781/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496200473/500000000 : ℝ)) (y := (115009781/125000000 : ℝ)) (X := (84369601418009/100000000000000 : ℝ)) (Y := (7815207534349/50000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (956239597/500000000 : ℝ)) (τ := (115009781/125000000 : ℝ)) (σ := (496200473/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (782437769/831012790 : ℝ) ^ p + (819792573/831012790 : ℝ) ^ p := by
    exact cert_lt (x := (782437769/831012790 : ℝ)) (y := (819792573/831012790 : ℝ)) (X := (26131795324147/100000000000000 : ℝ)) (Y := (1846705136427/2500000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (115009781/125000000 : ℝ)) (n' := (83101279/100000000 : ℝ)) (Ab := (782437769/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (230019713/250000000 : ℝ) ^ p + (39696033/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (230019713/250000000 : ℝ)) (y := (39696033/40000000 : ℝ)) (X := (3126128738903/20000000000000 : ℝ)) (Y := (21092343053371/25000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39696033/40000000 : ℝ) ^ p + (230019713/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (39696033/40000000 : ℝ)) (y := (230019713/250000000 : ℝ)) (X := (21092343053371/25000000000000 : ℝ)) (Y := (3126128738903/20000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1912479677/1000000000 : ℝ)) (τ := (230019713/250000000 : ℝ)) (σ := (39696033/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (782438419/831013508 : ℝ) ^ p + (819793291/831013508 : ℝ) ^ p := by
    exact cert_lt (x := (782438419/831013508 : ℝ)) (y := (819793291/831013508 : ℝ)) (X := (26131775953349/100000000000000 : ℝ)) (Y := (36934112460063/50000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (230019713/250000000 : ℝ)) (n' := (207753377/250000000 : ℝ)) (Ab := (782438419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (920078881/1000000000 : ℝ) ^ p + (992400819/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920078881/1000000000 : ℝ)) (y := (992400819/1000000000 : ℝ)) (X := (15630654671663/100000000000000 : ℝ)) (Y := (42184680423993/50000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992400819/1000000000 : ℝ) ^ p + (920078881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992400819/1000000000 : ℝ)) (y := (920078881/1000000000 : ℝ)) (X := (42184680423993/50000000000000 : ℝ)) (Y := (15630654671663/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (19124797/10000000 : ℝ)) (τ := (920078881/1000000000 : ℝ)) (σ := (992400819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (782438451/831013543 : ℝ) ^ p + (819793326/831013543 : ℝ) ^ p := by
    exact cert_lt (x := (782438451/831013543 : ℝ)) (y := (819793326/831013543 : ℝ)) (X := (26131775243321/100000000000000 : ℝ)) (Y := (73868225868881/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (920078881/1000000000 : ℝ)) (n' := (831013543/1000000000 : ℝ)) (Ab := (782438451/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (460039441/500000000 : ℝ) ^ p + (992400819/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460039441/500000000 : ℝ)) (y := (992400819/1000000000 : ℝ)) (X := (3126131010037/20000000000000 : ℝ)) (Y := (42184680423993/50000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992400819/1000000000 : ℝ) ^ p + (460039441/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992400819/1000000000 : ℝ)) (y := (460039441/500000000 : ℝ)) (X := (42184680423993/50000000000000 : ℝ)) (Y := (3126131010037/20000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1912479701/1000000000 : ℝ)) (τ := (460039441/500000000 : ℝ)) (σ := (992400819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (195609613/207753386 : ℝ) ^ p + (819793327/831013544 : ℝ) ^ p := by
    exact cert_lt (x := (195609613/207753386 : ℝ)) (y := (819793327/831013544 : ℝ)) (X := (13065887643409/50000000000000 : ℝ)) (Y := (18467056473997/25000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (460039441/500000000 : ℝ)) (n' := (103876693/125000000 : ℝ)) (Ab := (195609613/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1912479701/1000000000 : ℝ)) (τ := (460039441/500000000 : ℝ)) (σ := (992400819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (460039441/500000000 : ℝ)) (n' := (103876693/125000000 : ℝ)) (Ab := (195609613/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1912479701/1000000000 : ℝ)) (τ := (460039441/500000000 : ℝ)) (σ := (992400819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (460039441/500000000 : ℝ)) (n' := (103876693/125000000 : ℝ)) (Ab := (195609613/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1912479701/1000000000 : ℝ)) (τ := (460039441/500000000 : ℝ)) (σ := (992400819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (460039441/500000000 : ℝ)) (n' := (103876693/125000000 : ℝ)) (Ab := (195609613/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1912479701/1000000000 : ℝ)) (τ := (460039441/500000000 : ℝ)) (σ := (992400819/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1648751149/1807115344 : ℝ) ^ p + (1795895127/1807115344 : ℝ) ^ p := by
    exact cert_lt (x := (1648751149/1807115344 : ℝ)) (y := (1795895127/1807115344 : ℝ)) (X := (6478744198797/50000000000000 : ℝ)) (Y := (21760627952701/25000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (553586705/596442328 : ℝ) ^ p + (1181664439/1192884656 : ℝ) ^ p := by
    exact cert_lt (x := (553586705/596442328 : ℝ)) (y := (1181664439/1192884656 : ℝ)) (X := (18987623992103/100000000000000 : ℝ)) (Y := (81012376440191/100000000000000 : ℝ)) 713 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992400819/1000000000 : ℝ)) (U := (74555291/62500000 : ℝ)) (Ab := (1648751149/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (460039441/500000000 : ℝ)) (σ := (992400819/1000000000 : ℝ)) (Ab := (110717341/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab040
