import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar048 (p : ℝ) (hpa : (45/2 : ℝ) ≤ p) (hpb : p ≤ (721/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(45/2 : ℝ) ≤ (129090961/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (129090961/5000000000 : ℝ)) (by norm_num) (by norm_num) 45 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10129090961/5000000000 : ℝ) ≤ (10318740421/10000000000 : ℝ)^(45/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10318740421/10000000000 : ℝ)) (X := (10129090961/5000000000 : ℝ)) (by norm_num) 45 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10500389019/10000000000 : ℝ)^(45/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10500389019/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 45 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (45/2 : ℝ)) (beta := (721/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10318740421/10000000000 : ℝ)) (aup := (10500389019/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar049 (p : ℝ) (hpa : (721/32 : ℝ) ≤ p) (hpb : p ≤ (361/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(721/32 : ℝ) ≤ (256874013/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (256874013/10000000000 : ℝ)) (by norm_num) (by norm_num) 721 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20256874013/10000000000 : ℝ) ≤ (1031826181/1000000000 : ℝ)^(721/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1031826181/1000000000 : ℝ)) (X := (20256874013/10000000000 : ℝ)) (by norm_num) 721 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (524983897/500000000 : ℝ)^(721/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (524983897/500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 721 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (721/32 : ℝ)) (beta := (361/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1031826181/1000000000 : ℝ)) (aup := (524983897/500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar050 (p : ℝ) (hpa : (361/16 : ℝ) ≤ p) (hpb : p ≤ (723/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(361/16 : ℝ) ≤ (25557273/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (25557273/1000000000 : ℝ)) (by norm_num) (by norm_num) 361 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2025557273/1000000000 : ℝ) ≤ (1289723087/1250000000 : ℝ)^(361/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1289723087/1250000000 : ℝ)) (X := (2025557273/1000000000 : ℝ)) (by norm_num) 361 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (131237111/125000000 : ℝ)^(361/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (131237111/125000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 361 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (361/16 : ℝ)) (beta := (723/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1289723087/1250000000 : ℝ)) (aup := (131237111/125000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar051 (p : ℝ) (hpa : (723/32 : ℝ) ≤ p) (hpb : p ≤ (181/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(723/32 : ℝ) ≤ (254278039/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (254278039/10000000000 : ℝ)) (by norm_num) (by norm_num) 723 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20254278039/10000000000 : ℝ) ≤ (10317309069/10000000000 : ℝ)^(723/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10317309069/10000000000 : ℝ)) (X := (20254278039/10000000000 : ℝ)) (by norm_num) 723 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10498261829/10000000000 : ℝ)^(723/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10498261829/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 723 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (723/32 : ℝ)) (beta := (181/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10317309069/10000000000 : ℝ)) (aup := (10498261829/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar052 (p : ℝ) (hpa : (181/8 : ℝ) ≤ p) (hpb : p ≤ (725/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(181/8 : ℝ) ≤ (252989907/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (252989907/10000000000 : ℝ)) (by norm_num) (by norm_num) 181 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20252989907/10000000000 : ℝ) ≤ (2579208731/2500000000 : ℝ)^(181/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2579208731/2500000000 : ℝ)) (X := (20252989907/10000000000 : ℝ)) (by norm_num) 181 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5248778389/5000000000 : ℝ)^(181/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5248778389/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 181 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (181/8 : ℝ)) (beta := (725/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2579208731/2500000000 : ℝ)) (aup := (5248778389/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar053 (p : ℝ) (hpa : (725/32 : ℝ) ≤ p) (hpb : p ≤ (363/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(725/32 : ℝ) ≤ (2517083/100000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (2517083/100000000 : ℝ)) (by norm_num) (by norm_num) 725 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (202517083/100000000 : ℝ) ≤ (5158181127/5000000000 : ℝ)^(725/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5158181127/5000000000 : ℝ)) (X := (202517083/100000000 : ℝ)) (by norm_num) 725 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10496853719/10000000000 : ℝ)^(725/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10496853719/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 725 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (725/32 : ℝ)) (beta := (363/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5158181127/5000000000 : ℝ)) (aup := (10496853719/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar054 (p : ℝ) (hpa : (363/16 : ℝ) ≤ p) (hpb : p ≤ (727/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(363/16 : ℝ) ≤ (125216593/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (125216593/5000000000 : ℝ)) (by norm_num) (by norm_num) 363 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10125216593/5000000000 : ℝ) ≤ (2578972763/2500000000 : ℝ)^(363/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2578972763/2500000000 : ℝ)) (X := (10125216593/5000000000 : ℝ)) (by norm_num) 363 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2624038161/2500000000 : ℝ)^(363/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2624038161/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 363 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (363/16 : ℝ)) (beta := (727/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2578972763/2500000000 : ℝ)) (aup := (2624038161/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar055 (p : ℝ) (hpa : (727/32 : ℝ) ≤ p) (hpb : p ≤ (91/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(727/32 : ℝ) ≤ (249164531/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (249164531/10000000000 : ℝ)) (by norm_num) (by norm_num) 727 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20249164531/10000000000 : ℝ) ≤ (1031542131/1000000000 : ℝ)^(727/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1031542131/1000000000 : ℝ)) (X := (20249164531/10000000000 : ℝ)) (by norm_num) 727 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2099090709/2000000000 : ℝ)^(727/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2099090709/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 727 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (727/32 : ℝ)) (beta := (91/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1031542131/1000000000 : ℝ)) (aup := (2099090709/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar056 (p : ℝ) (hpa : (91/4 : ℝ) ≤ p) (hpb : p ≤ (729/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(91/4 : ℝ) ≤ (247902303/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (247902303/10000000000 : ℝ)) (by norm_num) (by norm_num) 91 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20247902303/10000000000 : ℝ) ≤ (5157476511/5000000000 : ℝ)^(91/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5157476511/5000000000 : ℝ)) (X := (20247902303/10000000000 : ℝ)) (by norm_num) 91 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2623689103/2500000000 : ℝ)^(91/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2623689103/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (91/4 : ℝ)) (beta := (729/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5157476511/5000000000 : ℝ)) (aup := (2623689103/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar057 (p : ℝ) (hpa : (729/32 : ℝ) ≤ p) (hpb : p ≤ (365/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(729/32 : ℝ) ≤ (246646469/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (246646469/10000000000 : ℝ)) (by norm_num) (by norm_num) 729 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20246646469/10000000000 : ℝ) ≤ (10314486181/10000000000 : ℝ)^(729/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10314486181/10000000000 : ℝ)) (X := (20246646469/10000000000 : ℝ)) (by norm_num) 729 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5247030619/5000000000 : ℝ)^(729/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5247030619/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 729 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (729/32 : ℝ)) (beta := (365/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10314486181/10000000000 : ℝ)) (aup := (5247030619/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar058 (p : ℝ) (hpa : (365/16 : ℝ) ≤ p) (hpb : p ≤ (731/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(365/16 : ℝ) ≤ (245396997/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (245396997/10000000000 : ℝ)) (by norm_num) (by norm_num) 365 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20245396997/10000000000 : ℝ) ≤ (10314020781/10000000000 : ℝ)^(365/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10314020781/10000000000 : ℝ)) (X := (20245396997/10000000000 : ℝ)) (by norm_num) 365 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5246684007/5000000000 : ℝ)^(365/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5246684007/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 365 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (365/16 : ℝ)) (beta := (731/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10314020781/10000000000 : ℝ)) (aup := (5246684007/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar059 (p : ℝ) (hpa : (731/32 : ℝ) ≤ p) (hpb : p ≤ (183/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(731/32 : ℝ) ≤ (48830771/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (48830771/2000000000 : ℝ)) (by norm_num) (by norm_num) 731 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4048830771/2000000000 : ℝ) ≤ (5156778407/5000000000 : ℝ)^(731/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5156778407/5000000000 : ℝ)) (X := (4048830771/2000000000 : ℝ)) (by norm_num) 731 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10492676733/10000000000 : ℝ)^(731/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10492676733/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 731 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (731/32 : ℝ)) (beta := (183/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5156778407/5000000000 : ℝ)) (aup := (10492676733/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar060 (p : ℝ) (hpa : (183/8 : ℝ) ≤ p) (hpb : p ≤ (733/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(183/8 : ℝ) ≤ (24291701/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (24291701/1000000000 : ℝ)) (by norm_num) (by norm_num) 183 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2024291701/1000000000 : ℝ) ≤ (412523771/400000000 : ℝ)^(183/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (412523771/400000000 : ℝ)) (X := (2024291701/1000000000 : ℝ)) (by norm_num) 183 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5245993693/5000000000 : ℝ)^(183/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5245993693/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 183 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (183/8 : ℝ)) (beta := (733/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (412523771/400000000 : ℝ)) (aup := (5245993693/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar061 (p : ℝ) (hpa : (733/32 : ℝ) ≤ p) (hpb : p ≤ (367/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(733/32 : ℝ) ≤ (241686431/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (241686431/10000000000 : ℝ)) (by norm_num) (by norm_num) 733 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20241686431/10000000000 : ℝ) ≤ (2062526631/2000000000 : ℝ)^(733/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2062526631/2000000000 : ℝ)) (X := (20241686431/10000000000 : ℝ)) (by norm_num) 733 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2098259993/2000000000 : ℝ)^(733/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2098259993/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 733 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (733/32 : ℝ)) (beta := (367/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2062526631/2000000000 : ℝ)) (aup := (2098259993/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar062 (p : ℝ) (hpa : (367/16 : ℝ) ≤ p) (hpb : p ≤ (735/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(367/16 : ℝ) ≤ (120231043/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (120231043/5000000000 : ℝ)) (by norm_num) (by norm_num) 367 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10120231043/5000000000 : ℝ) ≤ (206243469/200000000 : ℝ)^(367/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (206243469/200000000 : ℝ)) (X := (10120231043/5000000000 : ℝ)) (by norm_num) 367 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5245307231/5000000000 : ℝ)^(367/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5245307231/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 367 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (367/16 : ℝ)) (beta := (735/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (206243469/200000000 : ℝ)) (aup := (5245307231/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar063 (p : ℝ) (hpa : (735/32 : ℝ) ≤ p) (hpb : p ≤ (23 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(735/32 : ℝ) ≤ (239243943/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (239243943/10000000000 : ℝ)) (by norm_num) (by norm_num) 735 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20239243943/10000000000 : ℝ) ≤ (644482197/625000000 : ℝ)^(735/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (644482197/625000000 : ℝ)) (X := (20239243943/10000000000 : ℝ)) (by norm_num) 735 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2622482717/2500000000 : ℝ)^(735/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2622482717/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 735 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (735/32 : ℝ)) (beta := (23 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (644482197/625000000 : ℝ)) (aup := (2622482717/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk03 (p : ℝ) (hpa : (45/2 : ℝ) ≤ p) (hpb : p ≤ (23 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (91/4 : ℝ) with hl | hr
  ·
    rcases le_total p (181/8 : ℝ) with hal | har
    ·
      rcases le_total p (361/16 : ℝ) with haal | haar
      ·
        rcases le_total p (721/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar048 p hpa haaal
        ·
          exact lower21_scalar049 p haaar haal
      ·
        rcases le_total p (723/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar050 p haar haabl
        ·
          exact lower21_scalar051 p haabr hal
    ·
      rcases le_total p (363/16 : ℝ) with habl | habr
      ·
        rcases le_total p (725/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar052 p har habal
        ·
          exact lower21_scalar053 p habar habl
      ·
        rcases le_total p (727/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar054 p habr habbl
        ·
          exact lower21_scalar055 p habbr hl
  ·
    rcases le_total p (183/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (365/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (729/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar056 p hr hbaal
        ·
          exact lower21_scalar057 p hbaar hbal
      ·
        rcases le_total p (731/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar058 p hbar hbabl
        ·
          exact lower21_scalar059 p hbabr hbl
    ·
      rcases le_total p (367/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (733/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar060 p hbr hbbal
        ·
          exact lower21_scalar061 p hbbar hbbl
      ·
        rcases le_total p (735/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar062 p hbbr hbbbl
        ·
          exact lower21_scalar063 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk03
