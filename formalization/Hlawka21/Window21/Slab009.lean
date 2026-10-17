import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 9, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab009 (p : ℝ) (hpa : (681/32 : ℝ) ≤ p) (hpb : p ≤ (341/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2126656406531/92956500000000 : ℝ) (5908849/500000000 : ℝ) (4000000557739/18591300000000 : ℝ) (3033/2500 : ℝ) (121000019/62500000 : ℝ) (967953923/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596251741/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2207/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2213/5000 : ℝ)
      else (3789/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1479/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2126656406531/92956500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5908849/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (454914953/500000000 : ℝ) ^ p + (31040671/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (454914953/500000000 : ℝ)) (y := (31040671/31250000 : ℝ)) (X := (6672820401083/50000000000000 : ℝ)) (Y := (43327187832809/50000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31040671/31250000 : ℝ) ^ p + (454914953/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (31040671/31250000 : ℝ)) (y := (454914953/500000000 : ℝ)) (X := (43327187832809/50000000000000 : ℝ)) (Y := (6672820401083/50000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (951565689/500000000 : ℝ)) (τ := (454914953/500000000 : ℝ)) (σ := (31040671/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (770422207/819787661 : ℝ) ^ p + (807969963/819787661 : ℝ) ^ p := by
    exact cert_lt (x := (770422207/819787661 : ℝ)) (y := (807969963/819787661 : ℝ)) (X := (831757663513/3125000000000 : ℝ)) (Y := (36691877758877/50000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (454914953/500000000 : ℝ)) (n' := (819787661/1000000000 : ℝ)) (Ab := (770422207/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (915781041/1000000000 : ℝ) ^ p + (992219609/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915781041/1000000000 : ℝ)) (y := (992219609/1000000000 : ℝ)) (X := (15335025554309/100000000000000 : ℝ)) (Y := (84664989290371/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992219609/1000000000 : ℝ) ^ p + (915781041/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992219609/1000000000 : ℝ)) (y := (915781041/1000000000 : ℝ)) (X := (84664989290371/100000000000000 : ℝ)) (Y := (15335025554309/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (38160013/20000000 : ℝ)) (τ := (915781041/1000000000 : ℝ)) (σ := (992219609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (776859318/826926515 : ℝ) ^ p + (815108817/826926515 : ℝ) ^ p := by
    exact cert_lt (x := (776859318/826926515 : ℝ)) (y := (815108817/826926515 : ℝ)) (X := (13209253668021/50000000000000 : ℝ)) (Y := (18395373435603/25000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (915781041/1000000000 : ℝ)) (n' := (165385303/200000000 : ℝ)) (Ab := (388429659/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (229020269/250000000 : ℝ) ^ p + (992160497/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229020269/250000000 : ℝ)) (y := (992160497/1000000000 : ℝ)) (X := (3088492067667/20000000000000 : ℝ)) (Y := (42278777447081/50000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992160497/1000000000 : ℝ) ^ p + (229020269/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992160497/1000000000 : ℝ)) (y := (229020269/250000000 : ℝ)) (X := (42278777447081/50000000000000 : ℝ)) (Y := (3088492067667/20000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1908241573/1000000000 : ℝ)) (τ := (229020269/250000000 : ℝ)) (σ := (992160497/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (777182703/827285230 : ℝ) ^ p + (407733766/413642615 : ℝ) ^ p := by
    exact cert_lt (x := (777182703/827285230 : ℝ)) (y := (407733766/413642615 : ℝ)) (X := (26408648378527/100000000000000 : ℝ)) (Y := (4599459559769/6250000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (229020269/250000000 : ℝ)) (n' := (82728523/100000000 : ℝ)) (Ab := (777182703/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (91609603/100000000 : ℝ) ^ p + (992157539/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (91609603/100000000 : ℝ)) (y := (992157539/1000000000 : ℝ)) (X := (15447833703537/100000000000000 : ℝ)) (Y := (84552182227449/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992157539/1000000000 : ℝ) ^ p + (91609603/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992157539/1000000000 : ℝ)) (y := (91609603/100000000 : ℝ)) (X := (84552182227449/100000000000000 : ℝ)) (Y := (15447833703537/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1908253569/1000000000 : ℝ)) (τ := (91609603/100000000 : ℝ)) (σ := (992157539/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (388599409/413651553 : ℝ) ^ p + (407742704/413651553 : ℝ) ^ p := by
    exact cert_lt (x := (388599409/413651553 : ℝ)) (y := (407742704/413651553 : ℝ)) (X := (52816314219/200000000000 : ℝ)) (Y := (73591844084049/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (91609603/100000000 : ℝ)) (n' := (413651553/500000000 : ℝ)) (Ab := (388599409/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (114512097/125000000 : ℝ) ^ p + (992157391/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (114512097/125000000 : ℝ)) (y := (992157391/1000000000 : ℝ)) (X := (15448101807603/100000000000000 : ℝ)) (Y := (84551913421029/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992157391/1000000000 : ℝ) ^ p + (114512097/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992157391/1000000000 : ℝ)) (y := (114512097/125000000 : ℝ)) (X := (84551913421029/100000000000000 : ℝ)) (Y := (15448101807603/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1908254167/1000000000 : ℝ)) (τ := (114512097/125000000 : ℝ)) (σ := (992157391/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (388599811/413651999 : ℝ) ^ p + (407743150/413651999 : ℝ) ^ p := by
    exact cert_lt (x := (388599811/413651999 : ℝ)) (y := (407743150/413651999 : ℝ)) (X := (13204066252049/50000000000000 : ℝ)) (Y := (73591868590509/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (114512097/125000000 : ℝ)) (n' := (413651999/500000000 : ℝ)) (Ab := (388599811/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (916096813/1000000000 : ℝ) ^ p + (124019673/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (916096813/1000000000 : ℝ)) (y := (124019673/125000000 : ℝ)) (X := (3089623021021/20000000000000 : ℝ)) (Y := (2642246897101/3125000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124019673/125000000 : ℝ) ^ p + (916096813/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124019673/125000000 : ℝ)) (y := (916096813/1000000000 : ℝ)) (X := (2642246897101/3125000000000 : ℝ)) (Y := (3089623021021/20000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1908254197/1000000000 : ℝ)) (τ := (916096813/1000000000 : ℝ)) (σ := (124019673/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (129533277/137884007 : ℝ) ^ p + (407743172/413652021 : ℝ) ^ p := by
    exact cert_lt (x := (129533277/137884007 : ℝ)) (y := (407743172/413652021 : ℝ)) (X := (26408131537183/100000000000000 : ℝ)) (Y := (73591869799347/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (916096813/1000000000 : ℝ)) (n' := (413652021/500000000 : ℝ)) (Ab := (388599831/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (183219363/200000000 : ℝ) ^ p + (992157383/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183219363/200000000 : ℝ)) (y := (992157383/1000000000 : ℝ)) (X := (15448115823889/100000000000000 : ℝ)) (Y := (3382075955639/4000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992157383/1000000000 : ℝ) ^ p + (183219363/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992157383/1000000000 : ℝ)) (y := (183219363/200000000 : ℝ)) (X := (3382075955639/4000000000000 : ℝ)) (Y := (15448115823889/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (954127099/500000000 : ℝ)) (τ := (183219363/200000000 : ℝ)) (σ := (992157383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (777199663/827304044 : ℝ) ^ p + (407743173/413652022 : ℝ) ^ p := by
    exact cert_lt (x := (777199663/827304044 : ℝ)) (y := (407743173/413652022 : ℝ)) (X := (26408130900731/100000000000000 : ℝ)) (Y := (36795934927147/50000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (183219363/200000000 : ℝ)) (n' := (206826011/250000000 : ℝ)) (Ab := (777199663/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (954127099/500000000 : ℝ)) (τ := (183219363/200000000 : ℝ)) (σ := (992157383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (183219363/200000000 : ℝ)) (n' := (206826011/250000000 : ℝ)) (Ab := (777199663/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (954127099/500000000 : ℝ)) (τ := (183219363/200000000 : ℝ)) (σ := (992157383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (183219363/200000000 : ℝ)) (n' := (206826011/250000000 : ℝ)) (Ab := (777199663/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (954127099/500000000 : ℝ)) (τ := (183219363/200000000 : ℝ)) (σ := (992157383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (183219363/200000000 : ℝ)) (n' := (206826011/250000000 : ℝ)) (Ab := (777199663/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (954127099/500000000 : ℝ)) (τ := (183219363/200000000 : ℝ)) (σ := (992157383/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (821384400/903748259 : ℝ) ^ p + (897839410/903748259 : ℝ) ^ p := by
    exact cert_lt (x := (821384400/903748259 : ℝ)) (y := (897839410/903748259 : ℝ)) (X := (1630870410283/12500000000000 : ℝ)) (Y := (43476518485731/50000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (551723340/596251741 : ℝ) ^ p + (590342892/596251741 : ℝ) ^ p := by
    exact cert_lt (x := (551723340/596251741 : ℝ)) (y := (590342892/596251741 : ℝ)) (X := (956228726009/5000000000000 : ℝ)) (Y := (80875426206861/100000000000000 : ℝ)) 341 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992157383/1000000000 : ℝ)) (U := (596251741/500000000 : ℝ)) (Ab := (2053461/1250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (183219363/200000000 : ℝ)) (σ := (992157383/1000000000 : ℝ)) (Ab := (27586167/25000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab009
