import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower26_scalar032 (p : ℝ) (hpa : (28 : ℝ) ≤ p) (hpb : p ≤ (449/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(28 : ℝ) ≤ (6329787/312500000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (6329787/312500000 : ℝ)) (by norm_num) (by norm_num) 28 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (631329787/312500000 : ℝ) ≤ (5127165907/5000000000 : ℝ)^(28 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5127165907/5000000000 : ℝ)) (X := (631329787/312500000 : ℝ)) (by norm_num) 28 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5200080289/5000000000 : ℝ)^(28 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5200080289/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 28 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (28 : ℝ)) (beta := (449/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5127165907/5000000000 : ℝ)) (aup := (5200080289/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar033 (p : ℝ) (hpa : (449/16 : ℝ) ≤ p) (hpb : p ≤ (225/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(449/16 : ℝ) ≤ (50199459/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (50199459/2500000000 : ℝ)) (by norm_num) (by norm_num) 449 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5050199459/2500000000 : ℝ) ≤ (10253726497/10000000000 : ℝ)^(449/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10253726497/10000000000 : ℝ)) (X := (5050199459/2500000000 : ℝ)) (by norm_num) 449 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10399251793/10000000000 : ℝ)^(449/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10399251793/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 449 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (449/16 : ℝ)) (beta := (225/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10253726497/10000000000 : ℝ)) (aup := (10399251793/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar034 (p : ℝ) (hpa : (225/8 : ℝ) ≤ p) (hpb : p ≤ (451/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(225/8 : ℝ) ≤ (1990577/100000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (1990577/100000000 : ℝ)) (by norm_num) (by norm_num) 225 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (201990577/100000000 : ℝ) ≤ (5126562089/5000000000 : ℝ)^(225/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5126562089/5000000000 : ℝ)) (X := (201990577/100000000 : ℝ)) (by norm_num) 225 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5199173563/5000000000 : ℝ)^(225/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5199173563/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 225 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (225/8 : ℝ)) (beta := (451/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5126562089/5000000000 : ℝ)) (aup := (5199173563/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar035 (p : ℝ) (hpa : (451/16 : ℝ) ≤ p) (hpb : p ≤ (113/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(451/16 : ℝ) ≤ (49333161/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (49333161/2500000000 : ℝ)) (by norm_num) (by norm_num) 451 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5049333161/2500000000 : ℝ) ≤ (5126262417/5000000000 : ℝ)^(451/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5126262417/5000000000 : ℝ)) (X := (5049333161/2500000000 : ℝ)) (by norm_num) 451 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10397446549/10000000000 : ℝ)^(451/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10397446549/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 451 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (451/16 : ℝ)) (beta := (113/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5126262417/5000000000 : ℝ)) (aup := (10397446549/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar036 (p : ℝ) (hpa : (113/4 : ℝ) ≤ p) (hpb : p ≤ (453/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(113/4 : ℝ) ≤ (195622537/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (195622537/10000000000 : ℝ)) (by norm_num) (by norm_num) 113 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20195622537/10000000000 : ℝ) ≤ (10251928443/10000000000 : ℝ)^(113/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10251928443/10000000000 : ℝ)) (X := (20195622537/10000000000 : ℝ)) (by norm_num) 113 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5198275017/5000000000 : ℝ)^(113/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5198275017/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 113 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (113/4 : ℝ)) (beta := (453/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10251928443/10000000000 : ℝ)) (aup := (5198275017/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar037 (p : ℝ) (hpa : (453/16 : ℝ) ≤ p) (hpb : p ≤ (227/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(453/16 : ℝ) ≤ (193927251/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (193927251/10000000000 : ℝ)) (by norm_num) (by norm_num) 453 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20193927251/10000000000 : ℝ) ≤ (10251334983/10000000000 : ℝ)^(453/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10251334983/10000000000 : ℝ)) (X := (20193927251/10000000000 : ℝ)) (by norm_num) 453 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5197828777/5000000000 : ℝ)^(453/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5197828777/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 453 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (453/16 : ℝ)) (beta := (227/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10251334983/10000000000 : ℝ)) (aup := (5197828777/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar038 (p : ℝ) (hpa : (227/8 : ℝ) ≤ p) (hpb : p ≤ (455/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(227/8 : ℝ) ≤ (1501927/78125000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (1501927/78125000 : ℝ)) (by norm_num) (by norm_num) 227 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (157751927/78125000 : ℝ) ≤ (10250744431/10000000000 : ℝ)^(227/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10250744431/10000000000 : ℝ)) (X := (157751927/78125000 : ℝ)) (by norm_num) 227 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5197384541/5000000000 : ℝ)^(227/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5197384541/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 227 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (227/8 : ℝ)) (beta := (455/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10250744431/10000000000 : ℝ)) (aup := (5197384541/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar039 (p : ℝ) (hpa : (455/16 : ℝ) ≤ p) (hpb : p ≤ (57/2 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(455/16 : ℝ) ≤ (304929/16000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (304929/16000000 : ℝ)) (by norm_num) (by norm_num) 455 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (32304929/16000000 : ℝ) ≤ (5125078383/5000000000 : ℝ)^(455/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5125078383/5000000000 : ℝ)) (X := (32304929/16000000 : ℝ)) (by norm_num) 455 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10393884591/10000000000 : ℝ)^(455/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10393884591/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 455 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (455/16 : ℝ)) (beta := (57/2 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5125078383/5000000000 : ℝ)) (aup := (10393884591/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar040 (p : ℝ) (hpa : (57/2 : ℝ) ≤ p) (hpb : p ≤ (457/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(57/2 : ℝ) ≤ (188929033/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (188929033/10000000000 : ℝ)) (by norm_num) (by norm_num) 57 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20188929033/10000000000 : ℝ) ≤ (80074781/78125000 : ℝ)^(57/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (80074781/78125000 : ℝ)) (X := (20188929033/10000000000 : ℝ)) (by norm_num) 57 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5196502027/5000000000 : ℝ)^(57/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5196502027/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 57 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (57/2 : ℝ)) (beta := (457/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (80074781/78125000 : ℝ)) (aup := (5196502027/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar041 (p : ℝ) (hpa : (457/16 : ℝ) ≤ p) (hpb : p ≤ (229/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(457/16 : ℝ) ≤ (187291753/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (187291753/10000000000 : ℝ)) (by norm_num) (by norm_num) 457 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20187291753/10000000000 : ℝ) ≤ (10248990013/10000000000 : ℝ)^(457/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10248990013/10000000000 : ℝ)) (X := (20187291753/10000000000 : ℝ)) (by norm_num) 457 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2598031861/2500000000 : ℝ)^(457/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2598031861/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 457 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (457/16 : ℝ)) (beta := (229/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10248990013/10000000000 : ℝ)) (aup := (2598031861/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar042 (p : ℝ) (hpa : (229/8 : ℝ) ≤ p) (hpb : p ≤ (459/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(229/8 : ℝ) ≤ (92834331/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (92834331/5000000000 : ℝ)) (by norm_num) (by norm_num) 229 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10092834331/5000000000 : ℝ) ≤ (5124205441/5000000000 : ℝ)^(229/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5124205441/5000000000 : ℝ)) (X := (10092834331/5000000000 : ℝ)) (by norm_num) 229 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (649453421/625000000 : ℝ)^(229/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (649453421/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 229 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (229/8 : ℝ)) (beta := (459/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5124205441/5000000000 : ℝ)) (aup := (649453421/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar043 (p : ℝ) (hpa : (459/16 : ℝ) ≤ p) (hpb : p ≤ (115/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(459/16 : ℝ) ≤ (184059637/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (184059637/10000000000 : ℝ)) (by norm_num) (by norm_num) 459 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20184059637/10000000000 : ℝ) ≤ (5123917277/5000000000 : ℝ)^(459/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5123917277/5000000000 : ℝ)) (X := (20184059637/10000000000 : ℝ)) (by norm_num) 459 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (649399119/625000000 : ℝ)^(459/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (649399119/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 459 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (459/16 : ℝ)) (beta := (115/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5123917277/5000000000 : ℝ)) (aup := (649399119/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar044 (p : ℝ) (hpa : (115/4 : ℝ) ≤ p) (hpb : p ≤ (461/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(115/4 : ℝ) ≤ (45616139/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (45616139/2500000000 : ℝ)) (by norm_num) (by norm_num) 115 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5045616139/2500000000 : ℝ) ≤ (10247261007/10000000000 : ℝ)^(115/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10247261007/10000000000 : ℝ)) (X := (5045616139/2500000000 : ℝ)) (by norm_num) 115 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10389520921/10000000000 : ℝ)^(115/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10389520921/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 115 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (115/4 : ℝ)) (beta := (461/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10247261007/10000000000 : ℝ)) (aup := (10389520921/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar045 (p : ℝ) (hpa : (461/16 : ℝ) ≤ p) (hpb : p ≤ (231/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(461/16 : ℝ) ≤ (90441649/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (90441649/5000000000 : ℝ)) (by norm_num) (by norm_num) 461 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10090441649/5000000000 : ℝ) ≤ (5123345111/5000000000 : ℝ)^(461/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5123345111/5000000000 : ℝ)) (X := (10090441649/5000000000 : ℝ)) (by norm_num) 461 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5194329881/5000000000 : ℝ)^(461/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5194329881/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 461 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (461/16 : ℝ)) (beta := (231/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5123345111/5000000000 : ℝ)) (aup := (5194329881/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar046 (p : ℝ) (hpa : (231/8 : ℝ) ≤ p) (hpb : p ≤ (463/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(231/8 : ℝ) ≤ (179315743/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (179315743/10000000000 : ℝ)) (by norm_num) (by norm_num) 231 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20179315743/10000000000 : ℝ) ≤ (10246122179/10000000000 : ℝ)^(231/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10246122179/10000000000 : ℝ)) (X := (20179315743/10000000000 : ℝ)) (by norm_num) 231 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5193901201/5000000000 : ℝ)^(231/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5193901201/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 231 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (231/8 : ℝ)) (beta := (463/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10246122179/10000000000 : ℝ)) (aup := (5193901201/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar047 (p : ℝ) (hpa : (463/16 : ℝ) ≤ p) (hpb : p ≤ (29 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(463/16 : ℝ) ≤ (177761773/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (177761773/10000000000 : ℝ)) (by norm_num) (by norm_num) 463 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20177761773/10000000000 : ℝ) ≤ (1280694607/1250000000 : ℝ)^(463/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1280694607/1250000000 : ℝ)) (X := (20177761773/10000000000 : ℝ)) (by norm_num) 463 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (649184301/625000000 : ℝ)^(463/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (649184301/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 463 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (463/16 : ℝ)) (beta := (29 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1280694607/1250000000 : ℝ)) (aup := (649184301/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_chunk02 (p : ℝ) (hpa : (28 : ℝ) ≤ p) (hpb : p ≤ (29 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (57/2 : ℝ) with hl | hr
  ·
    rcases le_total p (113/4 : ℝ) with hal | har
    ·
      rcases le_total p (225/8 : ℝ) with haal | haar
      ·
        rcases le_total p (449/16 : ℝ) with haaal | haaar
        ·
          exact lower26_scalar032 p hpa haaal
        ·
          exact lower26_scalar033 p haaar haal
      ·
        rcases le_total p (451/16 : ℝ) with haabl | haabr
        ·
          exact lower26_scalar034 p haar haabl
        ·
          exact lower26_scalar035 p haabr hal
    ·
      rcases le_total p (227/8 : ℝ) with habl | habr
      ·
        rcases le_total p (453/16 : ℝ) with habal | habar
        ·
          exact lower26_scalar036 p har habal
        ·
          exact lower26_scalar037 p habar habl
      ·
        rcases le_total p (455/16 : ℝ) with habbl | habbr
        ·
          exact lower26_scalar038 p habr habbl
        ·
          exact lower26_scalar039 p habbr hl
  ·
    rcases le_total p (115/4 : ℝ) with hbl | hbr
    ·
      rcases le_total p (229/8 : ℝ) with hbal | hbar
      ·
        rcases le_total p (457/16 : ℝ) with hbaal | hbaar
        ·
          exact lower26_scalar040 p hr hbaal
        ·
          exact lower26_scalar041 p hbaar hbal
      ·
        rcases le_total p (459/16 : ℝ) with hbabl | hbabr
        ·
          exact lower26_scalar042 p hbar hbabl
        ·
          exact lower26_scalar043 p hbabr hbl
    ·
      rcases le_total p (231/8 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (461/16 : ℝ) with hbbal | hbbar
        ·
          exact lower26_scalar044 p hbr hbbal
        ·
          exact lower26_scalar045 p hbbar hbbl
      ·
        rcases le_total p (463/16 : ℝ) with hbbbl | hbbbr
        ·
          exact lower26_scalar046 p hbbr hbbbl
        ·
          exact lower26_scalar047 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower26_chunk02
