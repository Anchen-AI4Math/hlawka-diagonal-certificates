import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar032 (p : ℝ) (hpa : (22 : ℝ) ≤ p) (hpb : p ≤ (705/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(22 : ℝ) ≤ (280037613/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (280037613/10000000000 : ℝ)) (by norm_num) (by norm_num) 22 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20280037613/10000000000 : ℝ) ≤ (2581651877/2500000000 : ℝ)^(22 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2581651877/2500000000 : ℝ)) (X := (20280037613/10000000000 : ℝ)) (by norm_num) 22 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10512047867/10000000000 : ℝ)^(22 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10512047867/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 22 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (22 : ℝ)) (beta := (705/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2581651877/2500000000 : ℝ)) (aup := (10512047867/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar033 (p : ℝ) (hpa : (705/32 : ℝ) ≤ p) (hpb : p ≤ (353/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(705/32 : ℝ) ≤ (139309493/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (139309493/5000000000 : ℝ)) (by norm_num) (by norm_num) 705 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10139309493/5000000000 : ℝ) ≤ (5163051987/5000000000 : ℝ)^(705/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5163051987/5000000000 : ℝ)) (X := (10139309493/5000000000 : ℝ)) (by norm_num) 705 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5255651649/5000000000 : ℝ)^(705/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5255651649/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 705 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (705/32 : ℝ)) (beta := (353/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5163051987/5000000000 : ℝ)) (aup := (5255651649/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar034 (p : ℝ) (hpa : (353/16 : ℝ) ≤ p) (hpb : p ≤ (707/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(353/16 : ℝ) ≤ (277207547/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (277207547/10000000000 : ℝ)) (by norm_num) (by norm_num) 353 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20277207547/10000000000 : ℝ) ≤ (5162801027/5000000000 : ℝ)^(353/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5162801027/5000000000 : ℝ)) (X := (20277207547/10000000000 : ℝ)) (by norm_num) 353 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2627640223/2500000000 : ℝ)^(353/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2627640223/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 353 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (353/16 : ℝ)) (beta := (707/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5162801027/5000000000 : ℝ)) (aup := (2627640223/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar035 (p : ℝ) (hpa : (707/32 : ℝ) ≤ p) (hpb : p ≤ (177/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(707/32 : ℝ) ≤ (275803257/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (275803257/10000000000 : ℝ)) (by norm_num) (by norm_num) 707 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20275803257/10000000000 : ℝ) ≤ (516255087/500000000 : ℝ)^(707/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (516255087/500000000 : ℝ)) (X := (20275803257/10000000000 : ℝ)) (by norm_num) 707 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10509820637/10000000000 : ℝ)^(707/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10509820637/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 707 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (707/32 : ℝ)) (beta := (177/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (516255087/500000000 : ℝ)) (aup := (10509820637/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar036 (p : ℝ) (hpa : (177/8 : ℝ) ≤ p) (hpb : p ≤ (709/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(177/8 : ℝ) ≤ (137203041/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (137203041/5000000000 : ℝ)) (by norm_num) (by norm_num) 177 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10137203041/5000000000 : ℝ) ≤ (5162301513/5000000000 : ℝ)^(177/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5162301513/5000000000 : ℝ)) (X := (10137203041/5000000000 : ℝ)) (by norm_num) 177 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5254541263/5000000000 : ℝ)^(177/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5254541263/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 177 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (177/8 : ℝ)) (beta := (709/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5162301513/5000000000 : ℝ)) (aup := (5254541263/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar037 (p : ℝ) (hpa : (709/32 : ℝ) ≤ p) (hpb : p ≤ (355/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(709/32 : ℝ) ≤ (17063499/625000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (17063499/625000000 : ℝ)) (by norm_num) (by norm_num) 709 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1267063499/625000000 : ℝ) ≤ (10324105903/10000000000 : ℝ)^(709/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10324105903/10000000000 : ℝ)) (X := (1267063499/625000000 : ℝ)) (by norm_num) 709 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10508346549/10000000000 : ℝ)^(709/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10508346549/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 709 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (709/32 : ℝ)) (beta := (355/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10324105903/10000000000 : ℝ)) (aup := (10508346549/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar038 (p : ℝ) (hpa : (355/16 : ℝ) ≤ p) (hpb : p ≤ (711/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(355/16 : ℝ) ≤ (8488529/312500000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (8488529/312500000 : ℝ)) (by norm_num) (by norm_num) 355 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (633488529/312500000 : ℝ) ≤ (10323610363/10000000000 : ℝ)^(355/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10323610363/10000000000 : ℝ)) (X := (633488529/312500000 : ℝ)) (by norm_num) 355 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1313451587/1250000000 : ℝ)^(355/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1313451587/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 355 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (355/16 : ℝ)) (beta := (711/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10323610363/10000000000 : ℝ)) (aup := (1313451587/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar039 (p : ℝ) (hpa : (711/32 : ℝ) ≤ p) (hpb : p ≤ (89/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(711/32 : ℝ) ≤ (270256879/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (270256879/10000000000 : ℝ)) (by norm_num) (by norm_num) 711 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20270256879/10000000000 : ℝ) ≤ (25807791/25000000 : ℝ)^(711/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (25807791/25000000 : ℝ)) (X := (20270256879/10000000000 : ℝ)) (by norm_num) 711 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5253440479/5000000000 : ℝ)^(711/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5253440479/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 711 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (711/32 : ℝ)) (beta := (89/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (25807791/25000000 : ℝ)) (aup := (5253440479/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar040 (p : ℝ) (hpa : (89/4 : ℝ) ≤ p) (hpb : p ≤ (713/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(89/4 : ℝ) ≤ (1344439/50000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (1344439/50000000 : ℝ)) (by norm_num) (by norm_num) 89 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (101344439/50000000 : ℝ) ≤ (2064524801/2000000000 : ℝ)^(89/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2064524801/2000000000 : ℝ)) (X := (101344439/50000000 : ℝ)) (by norm_num) 89 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5253075663/5000000000 : ℝ)^(89/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5253075663/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (89/4 : ℝ)) (beta := (713/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2064524801/2000000000 : ℝ)) (aup := (5253075663/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar041 (p : ℝ) (hpa : (713/32 : ℝ) ≤ p) (hpb : p ≤ (357/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(713/32 : ℝ) ≤ (267525657/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (267525657/10000000000 : ℝ)) (by norm_num) (by norm_num) 713 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20267525657/10000000000 : ℝ) ≤ (10322133171/10000000000 : ℝ)^(713/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10322133171/10000000000 : ℝ)) (X := (20267525657/10000000000 : ℝ)) (by norm_num) 713 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (656588987/625000000 : ℝ)^(713/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (656588987/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 713 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (713/32 : ℝ)) (beta := (357/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10322133171/10000000000 : ℝ)) (aup := (656588987/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar042 (p : ℝ) (hpa : (357/16 : ℝ) ≤ p) (hpb : p ≤ (715/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(357/16 : ℝ) ≤ (133085207/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (133085207/5000000000 : ℝ)) (by norm_num) (by norm_num) 357 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10133085207/5000000000 : ℝ) ≤ (1032164389/1000000000 : ℝ)^(357/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1032164389/1000000000 : ℝ)) (X := (10133085207/5000000000 : ℝ)) (by norm_num) 357 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5252349173/5000000000 : ℝ)^(357/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5252349173/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 357 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (357/16 : ℝ)) (beta := (715/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1032164389/1000000000 : ℝ)) (aup := (5252349173/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar043 (p : ℝ) (hpa : (715/32 : ℝ) ≤ p) (hpb : p ≤ (179/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(715/32 : ℝ) ≤ (264822037/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (264822037/10000000000 : ℝ)) (by norm_num) (by norm_num) 715 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20264822037/10000000000 : ℝ) ≤ (2580289039/2500000000 : ℝ)^(715/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2580289039/2500000000 : ℝ)) (X := (20264822037/10000000000 : ℝ)) (by norm_num) 715 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10503974979/10000000000 : ℝ)^(715/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10503974979/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 715 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (715/32 : ℝ)) (beta := (179/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2580289039/2500000000 : ℝ)) (aup := (10503974979/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar044 (p : ℝ) (hpa : (179/8 : ℝ) ≤ p) (hpb : p ≤ (717/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(179/8 : ℝ) ≤ (263480491/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (263480491/10000000000 : ℝ)) (by norm_num) (by norm_num) 179 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20263480491/10000000000 : ℝ) ≤ (10320669961/10000000000 : ℝ)^(179/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10320669961/10000000000 : ℝ)) (X := (20263480491/10000000000 : ℝ)) (by norm_num) 179 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5251626841/5000000000 : ℝ)^(179/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5251626841/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 179 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (179/8 : ℝ)) (beta := (717/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10320669961/10000000000 : ℝ)) (aup := (5251626841/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar045 (p : ℝ) (hpa : (717/32 : ℝ) ≤ p) (hpb : p ≤ (359/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(717/32 : ℝ) ≤ (13107287/500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (13107287/500000000 : ℝ)) (by norm_num) (by norm_num) 717 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1013107287/500000000 : ℝ) ≤ (10320185297/10000000000 : ℝ)^(717/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10320185297/10000000000 : ℝ)) (X := (1013107287/500000000 : ℝ)) (by norm_num) 717 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5251267223/5000000000 : ℝ)^(717/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5251267223/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 717 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (717/32 : ℝ)) (beta := (359/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10320185297/10000000000 : ℝ)) (aup := (5251267223/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar046 (p : ℝ) (hpa : (359/16 : ℝ) ≤ p) (hpb : p ≤ (719/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(359/16 : ℝ) ≤ (260817751/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (260817751/10000000000 : ℝ)) (by norm_num) (by norm_num) 359 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20260817751/10000000000 : ℝ) ≤ (10319702157/10000000000 : ℝ)^(359/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10319702157/10000000000 : ℝ)) (X := (20260817751/10000000000 : ℝ)) (by norm_num) 359 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10501817263/10000000000 : ℝ)^(359/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10501817263/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 359 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (359/16 : ℝ)) (beta := (719/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10319702157/10000000000 : ℝ)) (aup := (10501817263/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar047 (p : ℝ) (hpa : (719/32 : ℝ) ≤ p) (hpb : p ≤ (45/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(719/32 : ℝ) ≤ (25949649/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (25949649/1000000000 : ℝ)) (by norm_num) (by norm_num) 719 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2025949649/1000000000 : ℝ) ≤ (5159610267/5000000000 : ℝ)^(719/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5159610267/5000000000 : ℝ)) (X := (2025949649/1000000000 : ℝ)) (by norm_num) 719 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10501102123/10000000000 : ℝ)^(719/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10501102123/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 719 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (719/32 : ℝ)) (beta := (45/2 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5159610267/5000000000 : ℝ)) (aup := (10501102123/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk02 (p : ℝ) (hpa : (22 : ℝ) ≤ p) (hpb : p ≤ (45/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (89/4 : ℝ) with hl | hr
  ·
    rcases le_total p (177/8 : ℝ) with hal | har
    ·
      rcases le_total p (353/16 : ℝ) with haal | haar
      ·
        rcases le_total p (705/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar032 p hpa haaal
        ·
          exact lower21_scalar033 p haaar haal
      ·
        rcases le_total p (707/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar034 p haar haabl
        ·
          exact lower21_scalar035 p haabr hal
    ·
      rcases le_total p (355/16 : ℝ) with habl | habr
      ·
        rcases le_total p (709/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar036 p har habal
        ·
          exact lower21_scalar037 p habar habl
      ·
        rcases le_total p (711/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar038 p habr habbl
        ·
          exact lower21_scalar039 p habbr hl
  ·
    rcases le_total p (179/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (357/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (713/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar040 p hr hbaal
        ·
          exact lower21_scalar041 p hbaar hbal
      ·
        rcases le_total p (715/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar042 p hbar hbabl
        ·
          exact lower21_scalar043 p hbabr hbl
    ·
      rcases le_total p (359/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (717/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar044 p hbr hbbal
        ·
          exact lower21_scalar045 p hbbar hbbl
      ·
        rcases le_total p (719/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar046 p hbbr hbbbl
        ·
          exact lower21_scalar047 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk02
