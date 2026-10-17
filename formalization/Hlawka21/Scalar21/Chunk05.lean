import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar080 (p : ℝ) (hpa : (47/2 : ℝ) ≤ p) (hpb : p ≤ (753/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(47/2 : ℝ) ≤ (109727317/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (109727317/5000000000 : ℝ)) (by norm_num) (by norm_num) 47 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10109727317/5000000000 : ℝ) ≤ (644008327/625000000 : ℝ)^(47/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (644008327/625000000 : ℝ)) (X := (10109727317/5000000000 : ℝ)) (by norm_num) 47 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5239297223/5000000000 : ℝ)^(47/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5239297223/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 47 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (47/2 : ℝ)) (beta := (753/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (644008327/625000000 : ℝ)) (aup := (5239297223/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar081 (p : ℝ) (hpa : (753/32 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(753/32 : ℝ) ≤ (218342911/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (218342911/10000000000 : ℝ)) (by norm_num) (by norm_num) 753 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20218342911/10000000000 : ℝ) ≤ (2575924797/2500000000 : ℝ)^(753/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2575924797/2500000000 : ℝ)) (X := (20218342911/10000000000 : ℝ)) (by norm_num) 753 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1047794391/1000000000 : ℝ)^(753/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1047794391/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 753 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (753/32 : ℝ)) (beta := (377/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2575924797/2500000000 : ℝ)) (aup := (1047794391/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar082 (p : ℝ) (hpa : (377/16 : ℝ) ≤ p) (hpb : p ≤ (755/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(377/16 : ℝ) ≤ (217236821/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (217236821/10000000000 : ℝ)) (by norm_num) (by norm_num) 377 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20217236821/10000000000 : ℝ) ≤ (5151633217/5000000000 : ℝ)^(377/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5151633217/5000000000 : ℝ)) (X := (20217236821/10000000000 : ℝ)) (by norm_num) 377 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (523864757/500000000 : ℝ)^(377/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (523864757/500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 377 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (377/16 : ℝ)) (beta := (755/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5151633217/5000000000 : ℝ)) (aup := (523864757/500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar083 (p : ℝ) (hpa : (755/32 : ℝ) ≤ p) (hpb : p ≤ (189/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(755/32 : ℝ) ≤ (216136333/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (216136333/10000000000 : ℝ)) (by norm_num) (by norm_num) 755 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20216136333/10000000000 : ℝ) ≤ (2575708741/2500000000 : ℝ)^(755/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2575708741/2500000000 : ℝ)) (X := (20216136333/10000000000 : ℝ)) (by norm_num) 755 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10476648129/10000000000 : ℝ)^(755/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10476648129/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 755 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (755/32 : ℝ)) (beta := (189/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2575708741/2500000000 : ℝ)) (aup := (10476648129/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar084 (p : ℝ) (hpa : (189/8 : ℝ) ≤ p) (hpb : p ≤ (757/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(189/8 : ℝ) ≤ (215041421/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (215041421/10000000000 : ℝ)) (by norm_num) (by norm_num) 189 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20215041421/10000000000 : ℝ) ≤ (10302404773/10000000000 : ℝ)^(189/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10302404773/10000000000 : ℝ)) (X := (20215041421/10000000000 : ℝ)) (by norm_num) 189 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10476002869/10000000000 : ℝ)^(189/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10476002869/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 189 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (189/8 : ℝ)) (beta := (757/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10302404773/10000000000 : ℝ)) (aup := (10476002869/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar085 (p : ℝ) (hpa : (757/32 : ℝ) ≤ p) (hpb : p ≤ (379/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(757/32 : ℝ) ≤ (42790411/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (42790411/2000000000 : ℝ)) (by norm_num) (by norm_num) 757 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4042790411/2000000000 : ℝ) ≤ (5150987927/5000000000 : ℝ)^(757/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5150987927/5000000000 : ℝ)) (X := (4042790411/2000000000 : ℝ)) (by norm_num) 757 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10475359353/10000000000 : ℝ)^(757/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10475359353/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 757 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (757/32 : ℝ)) (beta := (379/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5150987927/5000000000 : ℝ)) (aup := (10475359353/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar086 (p : ℝ) (hpa : (379/16 : ℝ) ≤ p) (hpb : p ≤ (759/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(379/16 : ℝ) ≤ (13304263/625000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (13304263/625000000 : ℝ)) (by norm_num) (by norm_num) 379 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1263304263/625000000 : ℝ) ≤ (5150774101/5000000000 : ℝ)^(379/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5150774101/5000000000 : ℝ)) (X := (1263304263/625000000 : ℝ)) (by norm_num) 379 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (418988703/400000000 : ℝ)^(379/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (418988703/400000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 379 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (379/16 : ℝ)) (beta := (759/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5150774101/5000000000 : ℝ)) (aup := (418988703/400000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar087 (p : ℝ) (hpa : (759/32 : ℝ) ≤ p) (hpb : p ≤ (95/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(759/32 : ℝ) ≤ (211789851/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (211789851/10000000000 : ℝ)) (by norm_num) (by norm_num) 759 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20211789851/10000000000 : ℝ) ≤ (2575280453/2500000000 : ℝ)^(759/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2575280453/2500000000 : ℝ)) (X := (20211789851/10000000000 : ℝ)) (by norm_num) 759 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10474077527/10000000000 : ℝ)^(759/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10474077527/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 759 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (759/32 : ℝ)) (beta := (95/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2575280453/2500000000 : ℝ)) (aup := (10474077527/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar088 (p : ℝ) (hpa : (95/4 : ℝ) ≤ p) (hpb : p ≤ (761/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(95/4 : ℝ) ≤ (210716957/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (210716957/10000000000 : ℝ)) (by norm_num) (by norm_num) 95 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20210716957/10000000000 : ℝ) ≤ (10300696677/10000000000 : ℝ)^(95/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10300696677/10000000000 : ℝ)) (X := (20210716957/10000000000 : ℝ)) (by norm_num) 95 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10473439203/10000000000 : ℝ)^(95/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10473439203/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (95/4 : ℝ)) (beta := (761/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10300696677/10000000000 : ℝ)) (aup := (10473439203/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar089 (p : ℝ) (hpa : (761/32 : ℝ) ≤ p) (hpb : p ≤ (381/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(761/32 : ℝ) ≤ (209649499/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (209649499/10000000000 : ℝ)) (by norm_num) (by norm_num) 761 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20209649499/10000000000 : ℝ) ≤ (1287534099/1250000000 : ℝ)^(761/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1287534099/1250000000 : ℝ)) (X := (20209649499/10000000000 : ℝ)) (by norm_num) 761 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5236401297/5000000000 : ℝ)^(761/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5236401297/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 761 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (761/32 : ℝ)) (beta := (381/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1287534099/1250000000 : ℝ)) (aup := (5236401297/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar090 (p : ℝ) (hpa : (381/16 : ℝ) ≤ p) (hpb : p ≤ (763/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(381/16 : ℝ) ≤ (208587447/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (208587447/10000000000 : ℝ)) (by norm_num) (by norm_num) 381 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20208587447/10000000000 : ℝ) ≤ (1287481269/1250000000 : ℝ)^(381/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1287481269/1250000000 : ℝ)) (X := (20208587447/10000000000 : ℝ)) (by norm_num) 381 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2094433539/2000000000 : ℝ)^(381/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2094433539/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 381 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (381/16 : ℝ)) (beta := (763/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1287481269/1250000000 : ℝ)) (aup := (2094433539/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar091 (p : ℝ) (hpa : (763/32 : ℝ) ≤ p) (hpb : p ≤ (191/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(763/32 : ℝ) ≤ (207530777/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (207530777/10000000000 : ℝ)) (by norm_num) (by norm_num) 763 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20207530777/10000000000 : ℝ) ≤ (10299428751/10000000000 : ℝ)^(763/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10299428751/10000000000 : ℝ)) (X := (20207530777/10000000000 : ℝ)) (by norm_num) 763 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10471534499/10000000000 : ℝ)^(763/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10471534499/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 763 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (763/32 : ℝ)) (beta := (191/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10299428751/10000000000 : ℝ)) (aup := (10471534499/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar092 (p : ℝ) (hpa : (191/8 : ℝ) ≤ p) (hpb : p ≤ (765/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(191/8 : ℝ) ≤ (103239729/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (103239729/5000000000 : ℝ)) (by norm_num) (by norm_num) 191 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10103239729/5000000000 : ℝ) ≤ (10299008583/10000000000 : ℝ)^(191/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10299008583/10000000000 : ℝ)) (X := (10103239729/5000000000 : ℝ)) (by norm_num) 191 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5235451499/5000000000 : ℝ)^(191/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5235451499/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 191 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (191/8 : ℝ)) (beta := (765/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10299008583/10000000000 : ℝ)) (aup := (5235451499/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar093 (p : ℝ) (hpa : (765/32 : ℝ) ≤ p) (hpb : p ≤ (383/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(765/32 : ℝ) ≤ (102716733/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (102716733/5000000000 : ℝ)) (by norm_num) (by norm_num) 765 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10102716733/5000000000 : ℝ) ≤ (10298589643/10000000000 : ℝ)^(765/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10298589643/10000000000 : ℝ)) (X := (10102716733/5000000000 : ℝ)) (by norm_num) 765 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10470273187/10000000000 : ℝ)^(765/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10470273187/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 765 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (765/32 : ℝ)) (beta := (383/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10298589643/10000000000 : ℝ)) (aup := (10470273187/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar094 (p : ℝ) (hpa : (383/16 : ℝ) ≤ p) (hpb : p ≤ (767/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(383/16 : ℝ) ≤ (204392773/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (204392773/10000000000 : ℝ)) (by norm_num) (by norm_num) 383 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20204392773/10000000000 : ℝ) ≤ (411926877/400000000 : ℝ)^(383/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (411926877/400000000 : ℝ)) (X := (20204392773/10000000000 : ℝ)) (by norm_num) 383 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10469645057/10000000000 : ℝ)^(383/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10469645057/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 383 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (383/16 : ℝ)) (beta := (767/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (411926877/400000000 : ℝ)) (aup := (10469645057/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar095 (p : ℝ) (hpa : (767/32 : ℝ) ≤ p) (hpb : p ≤ (24 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(767/32 : ℝ) ≤ (203357351/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (203357351/10000000000 : ℝ)) (by norm_num) (by norm_num) 767 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20203357351/10000000000 : ℝ) ≤ (411910217/400000000 : ℝ)^(767/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (411910217/400000000 : ℝ)) (X := (20203357351/10000000000 : ℝ)) (by norm_num) 767 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10469018603/10000000000 : ℝ)^(767/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10469018603/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 767 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (767/32 : ℝ)) (beta := (24 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (411910217/400000000 : ℝ)) (aup := (10469018603/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk05 (p : ℝ) (hpa : (47/2 : ℝ) ≤ p) (hpb : p ≤ (24 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (95/4 : ℝ) with hl | hr
  ·
    rcases le_total p (189/8 : ℝ) with hal | har
    ·
      rcases le_total p (377/16 : ℝ) with haal | haar
      ·
        rcases le_total p (753/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar080 p hpa haaal
        ·
          exact lower21_scalar081 p haaar haal
      ·
        rcases le_total p (755/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar082 p haar haabl
        ·
          exact lower21_scalar083 p haabr hal
    ·
      rcases le_total p (379/16 : ℝ) with habl | habr
      ·
        rcases le_total p (757/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar084 p har habal
        ·
          exact lower21_scalar085 p habar habl
      ·
        rcases le_total p (759/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar086 p habr habbl
        ·
          exact lower21_scalar087 p habbr hl
  ·
    rcases le_total p (191/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (381/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (761/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar088 p hr hbaal
        ·
          exact lower21_scalar089 p hbaar hbal
      ·
        rcases le_total p (763/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar090 p hbar hbabl
        ·
          exact lower21_scalar091 p hbabr hbl
    ·
      rcases le_total p (383/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (765/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar092 p hbr hbbal
        ·
          exact lower21_scalar093 p hbbar hbbl
      ·
        rcases le_total p (767/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar094 p hbbr hbbbl
        ·
          exact lower21_scalar095 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk05
