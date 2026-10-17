import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 46, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab046 (p : ℝ) (hpa : (359/16 : ℝ) ≤ p) (hpb : p ≤ (719/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (211173001769/9800700000000 : ℝ) (2777843/250000000 : ℝ) (2000000294021/9800700000000 : ℝ) (3033/2500 : ℝ) (969621599/500000000 : ℝ) (969579939/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149119967/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11079/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4507/10000 : ℝ)
      else (3829/5000 : ℝ) ≤ X j i ∧ X j i ≤ (148/125 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (211173001769/9800700000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2777843/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (45736131/50000000 : ℝ) ^ p + (496784011/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (45736131/50000000 : ℝ)) (y := (496784011/500000000 : ℝ)) (X := (1349651459653/10000000000000 : ℝ)) (Y := (86503502788769/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496784011/500000000 : ℝ) ^ p + (45736131/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (496784011/500000000 : ℝ)) (y := (45736131/50000000 : ℝ)) (X := (86503502788769/100000000000000 : ℝ)) (Y := (1349651459653/10000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (954145321/500000000 : ℝ)) (τ := (45736131/50000000 : ℝ)) (σ := (496784011/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (776833633/824440141 : ℝ) ^ p + (813328769/824440141 : ℝ) ^ p := by
    exact cert_lt (x := (776833633/824440141 : ℝ)) (y := (813328769/824440141 : ℝ)) (X := (131394527669/500000000000 : ℝ)) (Y := (1474421908831/2000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (45736131/50000000 : ℝ)) (n' := (824440141/1000000000 : ℝ)) (Ab := (776833633/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (36820867/40000000 : ℝ) ^ p + (992503223/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (36820867/40000000 : ℝ)) (y := (992503223/1000000000 : ℝ)) (X := (7777846534083/50000000000000 : ℝ)) (Y := (84444322658301/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992503223/1000000000 : ℝ) ^ p + (36820867/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (992503223/1000000000 : ℝ)) (y := (36820867/40000000 : ℝ)) (X := (84444322658301/100000000000000 : ℝ)) (Y := (7777846534083/50000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956512449/500000000 : ℝ)) (τ := (36820867/40000000 : ℝ)) (σ := (992503223/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (391545745/415673728 : ℝ) ^ p + (205059021/207836864 : ℝ) ^ p := by
    exact cert_lt (x := (391545745/415673728 : ℝ)) (y := (205059021/207836864 : ℝ)) (X := (13045329275007/50000000000000 : ℝ)) (Y := (73909342494209/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (36820867/40000000 : ℝ)) (n' := (3247451/3906250 : ℝ)) (Ab := (78309149/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (920792889/1000000000 : ℝ) ^ p + (992449153/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920792889/1000000000 : ℝ)) (y := (992449153/1000000000 : ℝ)) (X := (7829498932093/50000000000000 : ℝ)) (Y := (84341018010659/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992449153/1000000000 : ℝ) ^ p + (920792889/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992449153/1000000000 : ℝ)) (y := (920792889/1000000000 : ℝ)) (X := (84341018010659/100000000000000 : ℝ)) (Y := (7829498932093/50000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (956621021/500000000 : ℝ)) (τ := (920792889/1000000000 : ℝ)) (σ := (992449153/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (261127720/277223153 : ℝ) ^ p + (820558087/831669459 : ℝ) ^ p := by
    exact cert_lt (x := (261127720/277223153 : ℝ)) (y := (820558087/831669459 : ℝ)) (X := (26081947945613/100000000000000 : ℝ)) (Y := (73918052946039/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (920792889/1000000000 : ℝ)) (n' := (831669459/1000000000 : ℝ)) (Ab := (19584579/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (184161087/200000000 : ℝ) ^ p + (496223321/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184161087/200000000 : ℝ)) (y := (496223321/500000000 : ℝ)) (X := (313275848697/2000000000000 : ℝ)) (Y := (42168111749367/50000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496223321/500000000 : ℝ) ^ p + (184161087/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496223321/500000000 : ℝ)) (y := (184161087/200000000 : ℝ)) (X := (42168111749367/50000000000000 : ℝ)) (Y := (313275848697/2000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1913252077/1000000000 : ℝ)) (τ := (184161087/200000000 : ℝ)) (σ := (496223321/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (783396651/831684353 : ℝ) ^ p + (820572981/831684353 : ℝ) ^ p := by
    exact cert_lt (x := (783396651/831684353 : ℝ)) (y := (820572981/831684353 : ℝ)) (X := (26081545295811/100000000000000 : ℝ)) (Y := (36959227850889/50000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (184161087/200000000 : ℝ)) (n' := (831684353/1000000000 : ℝ)) (Ab := (783396651/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (184161203/200000000 : ℝ) ^ p + (496223263/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184161203/200000000 : ℝ)) (y := (496223263/500000000 : ℝ)) (X := (7832007060583/50000000000000 : ℝ)) (Y := (42168001007117/50000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496223263/500000000 : ℝ) ^ p + (184161203/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496223263/500000000 : ℝ)) (y := (184161203/200000000 : ℝ)) (X := (42168001007117/50000000000000 : ℝ)) (Y := (7832007060583/50000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1913252541/1000000000 : ℝ)) (τ := (184161203/200000000 : ℝ)) (σ := (496223263/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (71217934/75607731 : ℝ) ^ p + (820573669/831685041 : ℝ) ^ p := by
    exact cert_lt (x := (71217934/75607731 : ℝ)) (y := (820573669/831685041 : ℝ)) (X := (26081526553721/100000000000000 : ℝ)) (Y := (2309952322063/3125000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (184161203/200000000 : ℝ)) (n' := (831685041/1000000000 : ℝ)) (Ab := (391698637/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (920806041/1000000000 : ℝ) ^ p + (992446521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920806041/1000000000 : ℝ)) (y := (992446521/1000000000 : ℝ)) (X := (15664024058899/100000000000000 : ℝ)) (Y := (84335992467501/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992446521/1000000000 : ℝ) ^ p + (920806041/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992446521/1000000000 : ℝ)) (y := (920806041/1000000000 : ℝ)) (X := (84335992467501/100000000000000 : ℝ)) (Y := (15664024058899/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (956626281/500000000 : ℝ)) (τ := (920806041/1000000000 : ℝ)) (σ := (992446521/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (391698651/415842536 : ℝ) ^ p + (205143425/207921268 : ℝ) ^ p := by
    exact cert_lt (x := (391698651/415842536 : ℝ)) (y := (205143425/207921268 : ℝ)) (X := (13040762827981/50000000000000 : ℝ)) (Y := (73918475144287/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (920806041/1000000000 : ℝ)) (n' := (51980317/62500000 : ℝ)) (Ab := (391698651/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (920806043/1000000000 : ℝ) ^ p + (24811163/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (920806043/1000000000 : ℝ)) (y := (24811163/25000000 : ℝ)) (X := (783201241167/5000000000000 : ℝ)) (Y := (42167995279077/50000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (24811163/25000000 : ℝ) ^ p + (920806043/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24811163/25000000 : ℝ)) (y := (920806043/1000000000 : ℝ)) (X := (42167995279077/50000000000000 : ℝ)) (Y := (783201241167/5000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1913252563/1000000000 : ℝ)) (τ := (920806043/1000000000 : ℝ)) (σ := (24811163/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (391698652/415842537 : ℝ) ^ p + (410286851/415842537 : ℝ) ^ p := by
    exact cert_lt (x := (391698652/415842537 : ℝ)) (y := (410286851/415842537 : ℝ)) (X := (13040762871413/50000000000000 : ℝ)) (Y := (73918475198369/100000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (920806043/1000000000 : ℝ)) (n' := (415842537/500000000 : ℝ)) (Ab := (97924663/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1913252563/1000000000 : ℝ)) (τ := (920806043/1000000000 : ℝ)) (σ := (24811163/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (920806043/1000000000 : ℝ)) (n' := (415842537/500000000 : ℝ)) (Ab := (97924663/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1913252563/1000000000 : ℝ)) (τ := (920806043/1000000000 : ℝ)) (σ := (24811163/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (920806043/1000000000 : ℝ)) (n' := (415842537/500000000 : ℝ)) (Ab := (97924663/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1913252563/1000000000 : ℝ)) (τ := (920806043/1000000000 : ℝ)) (σ := (24811163/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (920806043/1000000000 : ℝ)) (n' := (415842537/500000000 : ℝ)) (Ab := (97924663/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1913252563/1000000000 : ℝ)) (τ := (920806043/1000000000 : ℝ)) (σ := (24811163/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (824926029/903520132 : ℝ) ^ p + (448982223/451760066 : ℝ) ^ p := by
    exact cert_lt (x := (824926029/903520132 : ℝ)) (y := (448982223/451760066 : ℝ)) (X := (3235277198417/25000000000000 : ℝ)) (Y := (10882361427103/12500000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (553933409/596479868 : ℝ) ^ p + (295462091/298239934 : ℝ) ^ p := by
    exact cert_lt (x := (553933409/596479868 : ℝ)) (y := (295462091/298239934 : ℝ)) (X := (18962435754933/100000000000000 : ℝ)) (Y := (20259391168847/25000000000000 : ℝ)) 719 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (24811163/25000000 : ℝ)) (U := (149119967/125000000 : ℝ)) (Ab := (824926029/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (920806043/1000000000 : ℝ)) (σ := (24811163/25000000 : ℝ)) (Ab := (553933409/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab046
