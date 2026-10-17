import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar144 (p : ℝ) (hpa : (51/2 : ℝ) ≤ p) (hpb : p ≤ (817/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(51/2 : ℝ) ≤ (158555973/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (158555973/10000000000 : ℝ)) (by norm_num) (by norm_num) 51 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20158555973/10000000000 : ℝ) ≤ (5139366501/5000000000 : ℝ)^(51/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5139366501/5000000000 : ℝ)) (X := (20158555973/10000000000 : ℝ)) (by norm_num) 51 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10440243729/10000000000 : ℝ)^(51/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10440243729/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 51 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (51/2 : ℝ)) (beta := (817/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5139366501/5000000000 : ℝ)) (aup := (10440243729/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar145 (p : ℝ) (hpa : (817/32 : ℝ) ≤ p) (hpb : p ≤ (409/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(817/32 : ℝ) ≤ (78876377/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (78876377/5000000000 : ℝ)) (by norm_num) (by norm_num) 817 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10078876377/5000000000 : ℝ) ≤ (10278371089/10000000000 : ℝ)^(817/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10278371089/10000000000 : ℝ)) (X := (10078876377/5000000000 : ℝ)) (by norm_num) 817 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10439693199/10000000000 : ℝ)^(817/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10439693199/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 817 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (817/32 : ℝ)) (beta := (409/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10278371089/10000000000 : ℝ)) (aup := (10439693199/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar146 (p : ℝ) (hpa : (409/16 : ℝ) ≤ p) (hpb : p ≤ (819/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(409/16 : ℝ) ≤ (156953603/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (156953603/10000000000 : ℝ)) (by norm_num) (by norm_num) 409 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20156953603/10000000000 : ℝ) ≤ (5139005077/5000000000 : ℝ)^(409/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5139005077/5000000000 : ℝ)) (X := (20156953603/10000000000 : ℝ)) (by norm_num) 409 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10439144043/10000000000 : ℝ)^(409/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10439144043/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 409 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (409/16 : ℝ)) (beta := (819/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5139005077/5000000000 : ℝ)) (aup := (10439144043/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar147 (p : ℝ) (hpa : (819/32 : ℝ) ≤ p) (hpb : p ≤ (205/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(819/32 : ℝ) ≤ (156158501/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (156158501/10000000000 : ℝ)) (by norm_num) (by norm_num) 819 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20156158501/10000000000 : ℝ) ≤ (10277650193/10000000000 : ℝ)^(819/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10277650193/10000000000 : ℝ)) (X := (20156158501/10000000000 : ℝ)) (by norm_num) 819 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10438596257/10000000000 : ℝ)^(819/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10438596257/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 819 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (819/32 : ℝ)) (beta := (205/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10277650193/10000000000 : ℝ)) (aup := (10438596257/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar148 (p : ℝ) (hpa : (205/8 : ℝ) ≤ p) (hpb : p ≤ (821/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(205/8 : ℝ) ≤ (155367427/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (155367427/10000000000 : ℝ)) (by norm_num) (by norm_num) 205 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20155367427/10000000000 : ℝ) ≤ (10277291203/10000000000 : ℝ)^(205/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10277291203/10000000000 : ℝ)) (X := (20155367427/10000000000 : ℝ)) (by norm_num) 205 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2609512459/2500000000 : ℝ)^(205/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2609512459/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 205 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (205/8 : ℝ)) (beta := (821/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10277291203/10000000000 : ℝ)) (aup := (2609512459/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar149 (p : ℝ) (hpa : (821/32 : ℝ) ≤ p) (hpb : p ≤ (411/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(821/32 : ℝ) ≤ (3864509/250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (3864509/250000000 : ℝ)) (by norm_num) (by norm_num) 821 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (503864509/250000000 : ℝ) ≤ (5138466589/5000000000 : ℝ)^(821/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5138466589/5000000000 : ℝ)) (X := (503864509/250000000 : ℝ)) (by norm_num) 821 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (417500191/400000000 : ℝ)^(821/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (417500191/400000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 821 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (821/32 : ℝ)) (beta := (411/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5138466589/5000000000 : ℝ)) (aup := (417500191/400000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar150 (p : ℝ) (hpa : (411/16 : ℝ) ≤ p) (hpb : p ≤ (823/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(411/16 : ℝ) ≤ (961233/62500000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (961233/62500000 : ℝ)) (by norm_num) (by norm_num) 411 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (125961233/62500000 : ℝ) ≤ (2055315223/2000000000 : ℝ)^(411/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2055315223/2000000000 : ℝ)) (X := (125961233/62500000 : ℝ)) (by norm_num) 411 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2609240267/2500000000 : ℝ)^(411/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2609240267/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 411 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (411/16 : ℝ)) (beta := (823/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2055315223/2000000000 : ℝ)) (aup := (2609240267/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar151 (p : ℝ) (hpa : (823/32 : ℝ) ≤ p) (hpb : p ≤ (103/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(823/32 : ℝ) ≤ (19127271/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (19127271/1250000000 : ℝ)) (by norm_num) (by norm_num) 823 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2519127271/1250000000 : ℝ) ≤ (10276220011/10000000000 : ℝ)^(823/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10276220011/10000000000 : ℝ)) (X := (2519127271/1250000000 : ℝ)) (by norm_num) 823 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10436418711/10000000000 : ℝ)^(823/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10436418711/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 823 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (823/32 : ℝ)) (beta := (103/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10276220011/10000000000 : ℝ)) (aup := (10436418711/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar152 (p : ℝ) (hpa : (103/4 : ℝ) ≤ p) (hpb : p ≤ (825/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(103/4 : ℝ) ≤ (76121501/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (76121501/5000000000 : ℝ)) (by norm_num) (by norm_num) 103 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10076121501/5000000000 : ℝ) ≤ (513793243/500000000 : ℝ)^(103/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (513793243/500000000 : ℝ)) (X := (10076121501/5000000000 : ℝ)) (by norm_num) 103 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5217938849/5000000000 : ℝ)^(103/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5217938849/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 103 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (103/4 : ℝ)) (beta := (825/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (513793243/500000000 : ℝ)) (aup := (5217938849/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar153 (p : ℝ) (hpa : (825/32 : ℝ) ≤ p) (hpb : p ≤ (413/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(825/32 : ℝ) ≤ (151471763/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (151471763/10000000000 : ℝ)) (by norm_num) (by norm_num) 825 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20151471763/10000000000 : ℝ) ≤ (513775533/500000000 : ℝ)^(825/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (513775533/500000000 : ℝ)) (X := (20151471763/10000000000 : ℝ)) (by norm_num) 825 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1304417253/1250000000 : ℝ)^(825/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1304417253/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 825 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (825/32 : ℝ)) (beta := (413/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (513775533/500000000 : ℝ)) (aup := (1304417253/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar154 (p : ℝ) (hpa : (413/16 : ℝ) ≤ p) (hpb : p ≤ (827/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(413/16 : ℝ) ≤ (150704431/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (150704431/10000000000 : ℝ)) (by norm_num) (by norm_num) 413 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20150704431/10000000000 : ℝ) ≤ (10275157407/10000000000 : ℝ)^(413/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10275157407/10000000000 : ℝ)) (X := (20150704431/10000000000 : ℝ)) (by norm_num) 413 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2086959937/2000000000 : ℝ)^(413/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2086959937/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 413 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (413/16 : ℝ)) (beta := (827/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10275157407/10000000000 : ℝ)) (aup := (2086959937/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar155 (p : ℝ) (hpa : (827/32 : ℝ) ≤ p) (hpb : p ≤ (207/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(827/32 : ℝ) ≤ (74970493/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (74970493/5000000000 : ℝ)) (by norm_num) (by norm_num) 827 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10074970493/5000000000 : ℝ) ≤ (2054961019/2000000000 : ℝ)^(827/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2054961019/2000000000 : ℝ)) (X := (10074970493/5000000000 : ℝ)) (by norm_num) 827 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2608565669/2500000000 : ℝ)^(827/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2608565669/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 827 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (827/32 : ℝ)) (beta := (207/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2054961019/2000000000 : ℝ)) (aup := (2608565669/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar156 (p : ℝ) (hpa : (207/8 : ℝ) ≤ p) (hpb : p ≤ (829/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(207/8 : ℝ) ≤ (149181409/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (149181409/10000000000 : ℝ)) (by norm_num) (by norm_num) 207 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20149181409/10000000000 : ℝ) ≤ (10274453723/10000000000 : ℝ)^(207/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10274453723/10000000000 : ℝ)) (X := (20149181409/10000000000 : ℝ)) (by norm_num) 207 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10433726991/10000000000 : ℝ)^(207/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10433726991/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 207 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (207/8 : ℝ)) (beta := (829/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10274453723/10000000000 : ℝ)) (aup := (10433726991/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar157 (p : ℝ) (hpa : (829/32 : ℝ) ≤ p) (hpb : p ≤ (415/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(829/32 : ℝ) ≤ (148425679/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (148425679/10000000000 : ℝ)) (by norm_num) (by norm_num) 829 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20148425679/10000000000 : ℝ) ≤ (2054820657/2000000000 : ℝ)^(829/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2054820657/2000000000 : ℝ)) (X := (20148425679/10000000000 : ℝ)) (by norm_num) 829 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10433192627/10000000000 : ℝ)^(829/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10433192627/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 829 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (829/32 : ℝ)) (beta := (415/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2054820657/2000000000 : ℝ)) (aup := (10433192627/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar158 (p : ℝ) (hpa : (415/16 : ℝ) ≤ p) (hpb : p ≤ (831/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(415/16 : ℝ) ≤ (73836889/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (73836889/5000000000 : ℝ)) (by norm_num) (by norm_num) 415 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10073836889/5000000000 : ℝ) ≤ (10273753779/10000000000 : ℝ)^(415/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10273753779/10000000000 : ℝ)) (X := (10073836889/5000000000 : ℝ)) (by norm_num) 415 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10432659577/10000000000 : ℝ)^(415/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10432659577/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 415 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (415/16 : ℝ)) (beta := (831/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10273753779/10000000000 : ℝ)) (aup := (10432659577/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar159 (p : ℝ) (hpa : (831/32 : ℝ) ≤ p) (hpb : p ≤ (26 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(831/32 : ℝ) ≤ (146925687/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (146925687/10000000000 : ℝ)) (by norm_num) (by norm_num) 831 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20146925687/10000000000 : ℝ) ≤ (10273405199/10000000000 : ℝ)^(831/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10273405199/10000000000 : ℝ)) (X := (20146925687/10000000000 : ℝ)) (by norm_num) 831 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10432127837/10000000000 : ℝ)^(831/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10432127837/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 831 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (831/32 : ℝ)) (beta := (26 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10273405199/10000000000 : ℝ)) (aup := (10432127837/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk09 (p : ℝ) (hpa : (51/2 : ℝ) ≤ p) (hpb : p ≤ (26 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (103/4 : ℝ) with hl | hr
  ·
    rcases le_total p (205/8 : ℝ) with hal | har
    ·
      rcases le_total p (409/16 : ℝ) with haal | haar
      ·
        rcases le_total p (817/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar144 p hpa haaal
        ·
          exact lower21_scalar145 p haaar haal
      ·
        rcases le_total p (819/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar146 p haar haabl
        ·
          exact lower21_scalar147 p haabr hal
    ·
      rcases le_total p (411/16 : ℝ) with habl | habr
      ·
        rcases le_total p (821/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar148 p har habal
        ·
          exact lower21_scalar149 p habar habl
      ·
        rcases le_total p (823/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar150 p habr habbl
        ·
          exact lower21_scalar151 p habbr hl
  ·
    rcases le_total p (207/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (413/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (825/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar152 p hr hbaal
        ·
          exact lower21_scalar153 p hbaar hbal
      ·
        rcases le_total p (827/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar154 p hbar hbabl
        ·
          exact lower21_scalar155 p hbabr hbl
    ·
      rcases le_total p (415/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (829/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar156 p hbr hbbal
        ·
          exact lower21_scalar157 p hbbar hbbl
      ·
        rcases le_total p (831/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar158 p hbbr hbbbl
        ·
          exact lower21_scalar159 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk09
