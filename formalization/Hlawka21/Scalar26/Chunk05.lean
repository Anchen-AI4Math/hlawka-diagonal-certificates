import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower26_scalar080 (p : ℝ) (hpa : (31 : ℝ) ≤ p) (hpb : p ≤ (497/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(31 : ℝ) ≤ (133381879/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (133381879/10000000000 : ℝ)) (by norm_num) (by norm_num) 31 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20133381879/10000000000 : ℝ) ≤ (10228307253/10000000000 : ℝ)^(31 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10228307253/10000000000 : ℝ)) (X := (20133381879/10000000000 : ℝ)) (by norm_num) 31 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2590186389/2500000000 : ℝ)^(31 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2590186389/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 31 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (31 : ℝ)) (beta := (497/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10228307253/10000000000 : ℝ)) (aup := (2590186389/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar081 (p : ℝ) (hpa : (497/16 : ℝ) ≤ p) (hpb : p ≤ (249/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(497/16 : ℝ) ≤ (132225977/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (132225977/10000000000 : ℝ)) (by norm_num) (by norm_num) 497 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20132225977/10000000000 : ℝ) ≤ (1278477973/1250000000 : ℝ)^(497/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1278477973/1250000000 : ℝ)) (X := (20132225977/10000000000 : ℝ)) (by norm_num) 497 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10360006799/10000000000 : ℝ)^(497/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10360006799/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 497 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (497/16 : ℝ)) (beta := (249/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1278477973/1250000000 : ℝ)) (aup := (10360006799/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar082 (p : ℝ) (hpa : (249/8 : ℝ) ≤ p) (hpb : p ≤ (499/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(249/8 : ℝ) ≤ (131080093/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (131080093/10000000000 : ℝ)) (by norm_num) (by norm_num) 249 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20131080093/10000000000 : ℝ) ≤ (5113671221/5000000000 : ℝ)^(249/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5113671221/5000000000 : ℝ)) (X := (20131080093/10000000000 : ℝ)) (by norm_num) 249 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10359271061/10000000000 : ℝ)^(249/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10359271061/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 249 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (249/8 : ℝ)) (beta := (499/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5113671221/5000000000 : ℝ)) (aup := (10359271061/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar083 (p : ℝ) (hpa : (499/16 : ℝ) ≤ p) (hpb : p ≤ (125/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(499/16 : ℝ) ≤ (64972069/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (64972069/5000000000 : ℝ)) (by norm_num) (by norm_num) 499 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10064972069/5000000000 : ℝ) ≤ (2556715803/2500000000 : ℝ)^(499/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2556715803/2500000000 : ℝ)) (X := (10064972069/5000000000 : ℝ)) (by norm_num) 499 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10358538323/10000000000 : ℝ)^(499/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10358538323/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 499 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (499/16 : ℝ)) (beta := (125/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2556715803/2500000000 : ℝ)) (aup := (10358538323/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar084 (p : ℝ) (hpa : (125/4 : ℝ) ≤ p) (hpb : p ≤ (501/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(125/4 : ℝ) ≤ (32204507/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (32204507/2500000000 : ℝ)) (by norm_num) (by norm_num) 125 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5032204507/2500000000 : ℝ) ≤ (10226386081/10000000000 : ℝ)^(125/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10226386081/10000000000 : ℝ)) (X := (5032204507/2500000000 : ℝ)) (by norm_num) 125 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1294726071/1250000000 : ℝ)^(125/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1294726071/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 125 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (125/4 : ℝ)) (beta := (501/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10226386081/10000000000 : ℝ)) (aup := (1294726071/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar085 (p : ℝ) (hpa : (501/16 : ℝ) ≤ p) (hpb : p ≤ (251/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(501/16 : ℝ) ≤ (127701677/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (127701677/10000000000 : ℝ)) (by norm_num) (by norm_num) 501 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20127701677/10000000000 : ℝ) ≤ (10225911033/10000000000 : ℝ)^(501/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10225911033/10000000000 : ℝ)) (X := (20127701677/10000000000 : ℝ)) (by norm_num) 501 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10357081777/10000000000 : ℝ)^(501/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10357081777/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 501 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (501/16 : ℝ)) (beta := (251/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10225911033/10000000000 : ℝ)) (aup := (10357081777/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar086 (p : ℝ) (hpa : (251/8 : ℝ) ≤ p) (hpb : p ≤ (503/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(251/8 : ℝ) ≤ (25319/2000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (25319/2000000 : ℝ)) (by norm_num) (by norm_num) 251 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4025319/2000000 : ℝ) ≤ (1278179757/1250000000 : ℝ)^(251/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1278179757/1250000000 : ℝ)) (X := (4025319/2000000 : ℝ)) (by norm_num) 251 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10356357933/10000000000 : ℝ)^(251/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10356357933/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 251 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (251/8 : ℝ)) (beta := (503/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1278179757/1250000000 : ℝ)) (aup := (10356357933/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar087 (p : ℝ) (hpa : (503/16 : ℝ) ≤ p) (hpb : p ≤ (63/2 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(503/16 : ℝ) ≤ (62748957/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (62748957/5000000000 : ℝ)) (by norm_num) (by norm_num) 503 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10062748957/5000000000 : ℝ) ≤ (2044993427/2000000000 : ℝ)^(503/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2044993427/2000000000 : ℝ)) (X := (10062748957/5000000000 : ℝ)) (by norm_num) 503 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10355637017/10000000000 : ℝ)^(503/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10355637017/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 503 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (503/16 : ℝ)) (beta := (63/2 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2044993427/2000000000 : ℝ)) (aup := (10355637017/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar088 (p : ℝ) (hpa : (63/2 : ℝ) ≤ p) (hpb : p ≤ (505/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(63/2 : ℝ) ≤ (24882067/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (24882067/2000000000 : ℝ)) (by norm_num) (by norm_num) 63 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4024882067/2000000000 : ℝ) ≤ (10224498257/10000000000 : ℝ)^(63/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10224498257/10000000000 : ℝ)) (X := (4024882067/2000000000 : ℝ)) (by norm_num) 63 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2588729753/2500000000 : ℝ)^(63/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2588729753/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 63 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (63/2 : ℝ)) (beta := (505/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10224498257/10000000000 : ℝ)) (aup := (2588729753/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar089 (p : ℝ) (hpa : (505/16 : ℝ) ≤ p) (hpb : p ≤ (253/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(505/16 : ℝ) ≤ (123332181/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (123332181/10000000000 : ℝ)) (by norm_num) (by norm_num) 505 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20123332181/10000000000 : ℝ) ≤ (639001963/625000000 : ℝ)^(505/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (639001963/625000000 : ℝ)) (X := (20123332181/10000000000 : ℝ)) (by norm_num) 505 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10354203899/10000000000 : ℝ)^(505/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10354203899/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 505 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (505/16 : ℝ)) (beta := (253/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (639001963/625000000 : ℝ)) (aup := (10354203899/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar090 (p : ℝ) (hpa : (253/8 : ℝ) ≤ p) (hpb : p ≤ (507/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(253/8 : ℝ) ≤ (122263371/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (122263371/10000000000 : ℝ)) (by norm_num) (by norm_num) 253 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20122263371/10000000000 : ℝ) ≤ (5111783287/5000000000 : ℝ)^(253/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5111783287/5000000000 : ℝ)) (X := (20122263371/10000000000 : ℝ)) (by norm_num) 253 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10353491663/10000000000 : ℝ)^(253/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10353491663/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 253 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (253/8 : ℝ)) (beta := (507/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5111783287/5000000000 : ℝ)) (aup := (10353491663/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar091 (p : ℝ) (hpa : (507/16 : ℝ) ≤ p) (hpb : p ≤ (127/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(507/16 : ℝ) ≤ (121203823/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (121203823/10000000000 : ℝ)) (by norm_num) (by norm_num) 507 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20121203823/10000000000 : ℝ) ≤ (10223103743/10000000000 : ℝ)^(507/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10223103743/10000000000 : ℝ)) (X := (20121203823/10000000000 : ℝ)) (by norm_num) 507 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2588195571/2500000000 : ℝ)^(507/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2588195571/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 507 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (507/16 : ℝ)) (beta := (127/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10223103743/10000000000 : ℝ)) (aup := (2588195571/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar092 (p : ℝ) (hpa : (127/4 : ℝ) ≤ p) (hpb : p ≤ (509/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(127/4 : ℝ) ≤ (60076729/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (60076729/5000000000 : ℝ)) (by norm_num) (by norm_num) 127 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10060076729/5000000000 : ℝ) ≤ (10222642901/10000000000 : ℝ)^(127/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10222642901/10000000000 : ℝ)) (X := (10060076729/5000000000 : ℝ)) (by norm_num) 127 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10352075747/10000000000 : ℝ)^(127/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10352075747/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 127 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (127/4 : ℝ)) (beta := (509/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10222642901/10000000000 : ℝ)) (aup := (10352075747/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar093 (p : ℝ) (hpa : (509/16 : ℝ) ≤ p) (hpb : p ≤ (255/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(509/16 : ℝ) ≤ (59556097/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (59556097/5000000000 : ℝ)) (by norm_num) (by norm_num) 509 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10059556097/5000000000 : ℝ) ≤ (2044436807/2000000000 : ℝ)^(509/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2044436807/2000000000 : ℝ)) (X := (10059556097/5000000000 : ℝ)) (by norm_num) 509 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5175686017/5000000000 : ℝ)^(509/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5175686017/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 509 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (509/16 : ℝ)) (beta := (255/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2044436807/2000000000 : ℝ)) (aup := (5175686017/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar094 (p : ℝ) (hpa : (255/8 : ℝ) ≤ p) (hpb : p ≤ (511/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(255/8 : ℝ) ≤ (23615991/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (23615991/2000000000 : ℝ)) (by norm_num) (by norm_num) 255 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4023615991/2000000000 : ℝ) ≤ (2555431783/2500000000 : ℝ)^(255/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2555431783/2500000000 : ℝ)) (X := (4023615991/2000000000 : ℝ)) (by norm_num) 255 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1293833891/1250000000 : ℝ)^(255/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1293833891/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 255 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (255/8 : ℝ)) (beta := (511/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2555431783/2500000000 : ℝ)) (aup := (1293833891/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar095 (p : ℝ) (hpa : (511/16 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(511/16 : ℝ) ≤ (117056661/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (117056661/10000000000 : ℝ)) (by norm_num) (by norm_num) 511 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20117056661/10000000000 : ℝ) ≤ (5110636089/5000000000 : ℝ)^(511/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5110636089/5000000000 : ℝ)) (X := (20117056661/10000000000 : ℝ)) (by norm_num) 511 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10349973013/10000000000 : ℝ)^(511/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10349973013/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 511 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (511/16 : ℝ)) (beta := (32 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5110636089/5000000000 : ℝ)) (aup := (10349973013/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_chunk05 (p : ℝ) (hpa : (31 : ℝ) ≤ p) (hpb : p ≤ (32 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (63/2 : ℝ) with hl | hr
  ·
    rcases le_total p (125/4 : ℝ) with hal | har
    ·
      rcases le_total p (249/8 : ℝ) with haal | haar
      ·
        rcases le_total p (497/16 : ℝ) with haaal | haaar
        ·
          exact lower26_scalar080 p hpa haaal
        ·
          exact lower26_scalar081 p haaar haal
      ·
        rcases le_total p (499/16 : ℝ) with haabl | haabr
        ·
          exact lower26_scalar082 p haar haabl
        ·
          exact lower26_scalar083 p haabr hal
    ·
      rcases le_total p (251/8 : ℝ) with habl | habr
      ·
        rcases le_total p (501/16 : ℝ) with habal | habar
        ·
          exact lower26_scalar084 p har habal
        ·
          exact lower26_scalar085 p habar habl
      ·
        rcases le_total p (503/16 : ℝ) with habbl | habbr
        ·
          exact lower26_scalar086 p habr habbl
        ·
          exact lower26_scalar087 p habbr hl
  ·
    rcases le_total p (127/4 : ℝ) with hbl | hbr
    ·
      rcases le_total p (253/8 : ℝ) with hbal | hbar
      ·
        rcases le_total p (505/16 : ℝ) with hbaal | hbaar
        ·
          exact lower26_scalar088 p hr hbaal
        ·
          exact lower26_scalar089 p hbaar hbal
      ·
        rcases le_total p (507/16 : ℝ) with hbabl | hbabr
        ·
          exact lower26_scalar090 p hbar hbabl
        ·
          exact lower26_scalar091 p hbabr hbl
    ·
      rcases le_total p (255/8 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (509/16 : ℝ) with hbbal | hbbar
        ·
          exact lower26_scalar092 p hbr hbbal
        ·
          exact lower26_scalar093 p hbbar hbbl
      ·
        rcases le_total p (511/16 : ℝ) with hbbbl | hbbbr
        ·
          exact lower26_scalar094 p hbbr hbbbl
        ·
          exact lower26_scalar095 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower26_chunk05
