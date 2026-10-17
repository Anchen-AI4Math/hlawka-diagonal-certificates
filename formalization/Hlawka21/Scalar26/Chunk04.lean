import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower26_scalar064 (p : ℝ) (hpa : (30 : ℝ) ≤ p) (hpb : p ≤ (481/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(30 : ℝ) ≤ (30662501/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (30662501/2000000000 : ℝ)) (by norm_num) (by norm_num) 30 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4030662501/2000000000 : ℝ) ≤ (5118172107/5000000000 : ℝ)^(30 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5118172107/5000000000 : ℝ)) (X := (4030662501/2000000000 : ℝ)) (by norm_num) 30 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5186495987/5000000000 : ℝ)^(30 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5186495987/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 30 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (30 : ℝ)) (beta := (481/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5118172107/5000000000 : ℝ)) (aup := (5186495987/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar065 (p : ℝ) (hpa : (481/16 : ℝ) ≤ p) (hpb : p ≤ (241/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(481/16 : ℝ) ≤ (75991941/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (75991941/5000000000 : ℝ)) (by norm_num) (by norm_num) 481 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10075991941/5000000000 : ℝ) ≤ (10235824657/10000000000 : ℝ)^(481/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10235824657/10000000000 : ℝ)) (X := (10075991941/5000000000 : ℝ)) (by norm_num) 481 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10372202267/10000000000 : ℝ)^(481/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10372202267/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 481 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (481/16 : ℝ)) (beta := (241/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10235824657/10000000000 : ℝ)) (aup := (10372202267/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar066 (p : ℝ) (hpa : (241/8 : ℝ) ≤ p) (hpb : p ≤ (483/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(241/8 : ℝ) ≤ (150666773/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (150666773/10000000000 : ℝ)) (by norm_num) (by norm_num) 241 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20150666773/10000000000 : ℝ) ≤ (409412299/400000000 : ℝ)^(241/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (409412299/400000000 : ℝ)) (X := (20150666773/10000000000 : ℝ)) (by norm_num) 241 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10371415897/10000000000 : ℝ)^(241/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10371415897/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 241 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (241/8 : ℝ)) (beta := (483/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (409412299/400000000 : ℝ)) (aup := (10371415897/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar067 (p : ℝ) (hpa : (483/16 : ℝ) ≤ p) (hpb : p ≤ (121/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(483/16 : ℝ) ≤ (74680539/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (74680539/5000000000 : ℝ)) (by norm_num) (by norm_num) 483 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10074680539/5000000000 : ℝ) ≤ (10234792651/10000000000 : ℝ)^(483/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10234792651/10000000000 : ℝ)) (X := (10074680539/5000000000 : ℝ)) (by norm_num) 483 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10370632843/10000000000 : ℝ)^(483/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10370632843/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 483 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (483/16 : ℝ)) (beta := (121/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10234792651/10000000000 : ℝ)) (aup := (10370632843/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar068 (p : ℝ) (hpa : (121/4 : ℝ) ≤ p) (hpb : p ≤ (485/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(121/4 : ℝ) ≤ (148066699/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (148066699/10000000000 : ℝ)) (by norm_num) (by norm_num) 121 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20148066699/10000000000 : ℝ) ≤ (10234280169/10000000000 : ℝ)^(121/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10234280169/10000000000 : ℝ)) (X := (20148066699/10000000000 : ℝ)) (by norm_num) 121 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10369853083/10000000000 : ℝ)^(121/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10369853083/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 121 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (121/4 : ℝ)) (beta := (485/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10234280169/10000000000 : ℝ)) (aup := (10369853083/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar069 (p : ℝ) (hpa : (485/16 : ℝ) ≤ p) (hpb : p ≤ (243/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(485/16 : ℝ) ≤ (9173971/625000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (9173971/625000000 : ℝ)) (by norm_num) (by norm_num) 485 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1259173971/625000000 : ℝ) ≤ (2558442503/2500000000 : ℝ)^(485/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2558442503/2500000000 : ℝ)) (X := (1259173971/625000000 : ℝ)) (by norm_num) 485 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10369076597/10000000000 : ℝ)^(485/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10369076597/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 485 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (485/16 : ℝ)) (beta := (243/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2558442503/2500000000 : ℝ)) (aup := (10369076597/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar070 (p : ℝ) (hpa : (243/8 : ℝ) ≤ p) (hpb : p ≤ (487/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(243/8 : ℝ) ≤ (72755747/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (72755747/5000000000 : ℝ)) (by norm_num) (by norm_num) 243 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10072755747/5000000000 : ℝ) ≤ (2558315541/2500000000 : ℝ)^(243/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2558315541/2500000000 : ℝ)) (X := (10072755747/5000000000 : ℝ)) (by norm_num) 243 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2592075841/2500000000 : ℝ)^(243/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2592075841/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 243 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (243/8 : ℝ)) (beta := (487/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2558315541/2500000000 : ℝ)) (aup := (2592075841/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar071 (p : ℝ) (hpa : (487/16 : ℝ) ≤ p) (hpb : p ≤ (61/2 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(487/16 : ℝ) ≤ (5770019/400000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (5770019/400000000 : ℝ)) (by norm_num) (by norm_num) 487 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (805770019/400000000 : ℝ) ≤ (1023275661/1000000000 : ℝ)^(487/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1023275661/1000000000 : ℝ)) (X := (805770019/400000000 : ℝ)) (by norm_num) 487 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2591883341/2500000000 : ℝ)^(487/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2591883341/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 487 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (487/16 : ℝ)) (beta := (61/2 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1023275661/1000000000 : ℝ)) (aup := (2591883341/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar072 (p : ℝ) (hpa : (61/2 : ℝ) ≤ p) (hpb : p ≤ (489/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(61/2 : ℝ) ≤ (28600077/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (28600077/2000000000 : ℝ)) (by norm_num) (by norm_num) 61 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4028600077/2000000000 : ℝ) ≤ (10232253333/10000000000 : ℝ)^(61/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10232253333/10000000000 : ℝ)) (X := (4028600077/2000000000 : ℝ)) (by norm_num) 61 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10366766577/10000000000 : ℝ)^(61/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10366766577/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 61 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (61/2 : ℝ)) (beta := (489/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10232253333/10000000000 : ℝ)) (aup := (10366766577/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar073 (p : ℝ) (hpa : (489/16 : ℝ) ≤ p) (hpb : p ≤ (245/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(489/16 : ℝ) ≤ (17720141/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (17720141/1250000000 : ℝ)) (by norm_num) (by norm_num) 489 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2517720141/1250000000 : ℝ) ≤ (5115876159/5000000000 : ℝ)^(489/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5115876159/5000000000 : ℝ)) (X := (2517720141/1250000000 : ℝ)) (by norm_num) 489 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5183001491/5000000000 : ℝ)^(489/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5183001491/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 489 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (489/16 : ℝ)) (beta := (245/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5115876159/5000000000 : ℝ)) (aup := (5183001491/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar074 (p : ℝ) (hpa : (245/8 : ℝ) ≤ p) (hpb : p ≤ (491/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(245/8 : ℝ) ≤ (14053261/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (14053261/1000000000 : ℝ)) (by norm_num) (by norm_num) 245 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2014053261/1000000000 : ℝ) ≤ (10231253549/10000000000 : ℝ)^(245/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10231253549/10000000000 : ℝ)) (X := (2014053261/1000000000 : ℝ)) (by norm_num) 245 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10365242559/10000000000 : ℝ)^(245/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10365242559/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 245 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (245/8 : ℝ)) (beta := (491/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10231253549/10000000000 : ℝ)) (aup := (10365242559/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar075 (p : ℝ) (hpa : (491/16 : ℝ) ≤ p) (hpb : p ≤ (123/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(491/16 : ℝ) ≤ (139314739/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (139314739/10000000000 : ℝ)) (by norm_num) (by norm_num) 491 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20139314739/10000000000 : ℝ) ≤ (10230757011/10000000000 : ℝ)^(491/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10230757011/10000000000 : ℝ)) (X := (20139314739/10000000000 : ℝ)) (by norm_num) 491 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1036448529/1000000000 : ℝ)^(491/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1036448529/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 491 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (491/16 : ℝ)) (beta := (123/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10230757011/10000000000 : ℝ)) (aup := (1036448529/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar076 (p : ℝ) (hpa : (123/4 : ℝ) ≤ p) (hpb : p ≤ (493/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(123/4 : ℝ) ≤ (69053711/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (69053711/5000000000 : ℝ)) (by norm_num) (by norm_num) 123 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10069053711/5000000000 : ℝ) ≤ (319695709/312500000 : ℝ)^(123/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (319695709/312500000 : ℝ)) (X := (10069053711/5000000000 : ℝ)) (by norm_num) 123 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10363731153/10000000000 : ℝ)^(123/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10363731153/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 123 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (123/4 : ℝ)) (beta := (493/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (319695709/312500000 : ℝ)) (aup := (10363731153/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar077 (p : ℝ) (hpa : (493/16 : ℝ) ≤ p) (hpb : p ≤ (247/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(493/16 : ℝ) ≤ (17113821/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (17113821/1250000000 : ℝ)) (by norm_num) (by norm_num) 493 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2517113821/1250000000 : ℝ) ≤ (5114885283/5000000000 : ℝ)^(493/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5114885283/5000000000 : ℝ)) (X := (2517113821/1250000000 : ℝ)) (by norm_num) 493 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10362980131/10000000000 : ℝ)^(493/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10362980131/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 493 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (493/16 : ℝ)) (beta := (247/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5114885283/5000000000 : ℝ)) (aup := (10362980131/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar078 (p : ℝ) (hpa : (247/8 : ℝ) ≤ p) (hpb : p ≤ (495/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(247/8 : ℝ) ≤ (67862043/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (67862043/5000000000 : ℝ)) (by norm_num) (by norm_num) 247 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10067862043/5000000000 : ℝ) ≤ (1022928063/1000000000 : ℝ)^(247/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1022928063/1000000000 : ℝ)) (X := (10067862043/5000000000 : ℝ)) (by norm_num) 247 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2590558051/2500000000 : ℝ)^(247/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2590558051/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 247 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (247/8 : ℝ)) (beta := (495/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1022928063/1000000000 : ℝ)) (aup := (2590558051/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar079 (p : ℝ) (hpa : (495/16 : ℝ) ≤ p) (hpb : p ≤ (31 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(495/16 : ℝ) ≤ (67273943/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (67273943/5000000000 : ℝ)) (by norm_num) (by norm_num) 495 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10067273943/5000000000 : ℝ) ≤ (319649777/312500000 : ℝ)^(495/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (319649777/312500000 : ℝ)) (X := (10067273943/5000000000 : ℝ)) (by norm_num) 495 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1295185919/1250000000 : ℝ)^(495/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1295185919/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 495 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (495/16 : ℝ)) (beta := (31 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (319649777/312500000 : ℝ)) (aup := (1295185919/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_chunk04 (p : ℝ) (hpa : (30 : ℝ) ≤ p) (hpb : p ≤ (31 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (61/2 : ℝ) with hl | hr
  ·
    rcases le_total p (121/4 : ℝ) with hal | har
    ·
      rcases le_total p (241/8 : ℝ) with haal | haar
      ·
        rcases le_total p (481/16 : ℝ) with haaal | haaar
        ·
          exact lower26_scalar064 p hpa haaal
        ·
          exact lower26_scalar065 p haaar haal
      ·
        rcases le_total p (483/16 : ℝ) with haabl | haabr
        ·
          exact lower26_scalar066 p haar haabl
        ·
          exact lower26_scalar067 p haabr hal
    ·
      rcases le_total p (243/8 : ℝ) with habl | habr
      ·
        rcases le_total p (485/16 : ℝ) with habal | habar
        ·
          exact lower26_scalar068 p har habal
        ·
          exact lower26_scalar069 p habar habl
      ·
        rcases le_total p (487/16 : ℝ) with habbl | habbr
        ·
          exact lower26_scalar070 p habr habbl
        ·
          exact lower26_scalar071 p habbr hl
  ·
    rcases le_total p (123/4 : ℝ) with hbl | hbr
    ·
      rcases le_total p (245/8 : ℝ) with hbal | hbar
      ·
        rcases le_total p (489/16 : ℝ) with hbaal | hbaar
        ·
          exact lower26_scalar072 p hr hbaal
        ·
          exact lower26_scalar073 p hbaar hbal
      ·
        rcases le_total p (491/16 : ℝ) with hbabl | hbabr
        ·
          exact lower26_scalar074 p hbar hbabl
        ·
          exact lower26_scalar075 p hbabr hbl
    ·
      rcases le_total p (247/8 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (493/16 : ℝ) with hbbal | hbbar
        ·
          exact lower26_scalar076 p hbr hbbal
        ·
          exact lower26_scalar077 p hbbar hbbl
      ·
        rcases le_total p (495/16 : ℝ) with hbbbl | hbbbr
        ·
          exact lower26_scalar078 p hbbr hbbbl
        ·
          exact lower26_scalar079 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower26_chunk04
