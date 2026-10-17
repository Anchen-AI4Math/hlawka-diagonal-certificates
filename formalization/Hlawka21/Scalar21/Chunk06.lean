import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar096 (p : ℝ) (hpa : (24 : ℝ) ≤ p) (hpb : p ≤ (769/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(24 : ℝ) ≤ (8093087/400000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (8093087/400000000 : ℝ)) (by norm_num) (by norm_num) 24 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (808093087/400000000 : ℝ) ≤ (1287167517/1250000000 : ℝ)^(24 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1287167517/1250000000 : ℝ)) (X := (808093087/400000000 : ℝ)) (by norm_num) 24 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5234196909/5000000000 : ℝ)^(24 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5234196909/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 24 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (24 : ℝ)) (beta := (769/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1287167517/1250000000 : ℝ)) (aup := (5234196909/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar097 (p : ℝ) (hpa : (769/32 : ℝ) ≤ p) (hpb : p ≤ (385/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(769/32 : ℝ) ≤ (100651109/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (100651109/5000000000 : ℝ)) (by norm_num) (by norm_num) 769 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10100651109/5000000000 : ℝ) ≤ (5148463027/5000000000 : ℝ)^(769/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5148463027/5000000000 : ℝ)) (X := (10100651109/5000000000 : ℝ)) (by norm_num) 769 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5233885347/5000000000 : ℝ)^(769/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5233885347/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 769 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (769/32 : ℝ)) (beta := (385/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5148463027/5000000000 : ℝ)) (aup := (5233885347/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar098 (p : ℝ) (hpa : (385/16 : ℝ) ≤ p) (hpb : p ≤ (771/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(385/16 : ℝ) ≤ (200282453/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (200282453/10000000000 : ℝ)) (by norm_num) (by norm_num) 385 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20200282453/10000000000 : ℝ) ≤ (10296513173/10000000000 : ℝ)^(385/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10296513173/10000000000 : ℝ)) (X := (20200282453/10000000000 : ℝ)) (by norm_num) 385 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10467149227/10000000000 : ℝ)^(385/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10467149227/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 385 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (385/16 : ℝ)) (beta := (771/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10296513173/10000000000 : ℝ)) (aup := (10467149227/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar099 (p : ℝ) (hpa : (771/32 : ℝ) ≤ p) (hpb : p ≤ (193/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(771/32 : ℝ) ≤ (199267853/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (199267853/10000000000 : ℝ)) (by norm_num) (by norm_num) 771 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20199267853/10000000000 : ℝ) ≤ (10296101487/10000000000 : ℝ)^(771/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10296101487/10000000000 : ℝ)) (X := (20199267853/10000000000 : ℝ)) (by norm_num) 771 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (81769761/78125000 : ℝ)^(771/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (81769761/78125000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 771 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (771/32 : ℝ)) (beta := (193/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10296101487/10000000000 : ℝ)) (aup := (81769761/78125000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar100 (p : ℝ) (hpa : (193/8 : ℝ) ≤ p) (hpb : p ≤ (773/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(193/8 : ℝ) ≤ (99129197/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (99129197/5000000000 : ℝ)) (by norm_num) (by norm_num) 193 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10099129197/5000000000 : ℝ) ≤ (643480687/625000000 : ℝ)^(193/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (643480687/625000000 : ℝ)) (X := (10099129197/5000000000 : ℝ)) (by norm_num) 193 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10465911231/10000000000 : ℝ)^(193/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10465911231/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 193 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (193/8 : ℝ)) (beta := (773/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (643480687/625000000 : ℝ)) (aup := (10465911231/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar101 (p : ℝ) (hpa : (773/32 : ℝ) ≤ p) (hpb : p ≤ (387/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(773/32 : ℝ) ≤ (6164189/312500000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (6164189/312500000 : ℝ)) (by norm_num) (by norm_num) 773 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (631164189/312500000 : ℝ) ≤ (5147640841/5000000000 : ℝ)^(773/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5147640841/5000000000 : ℝ)) (X := (631164189/312500000 : ℝ)) (by norm_num) 773 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1046529469/1000000000 : ℝ)^(773/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1046529469/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 773 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (773/32 : ℝ)) (beta := (387/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5147640841/5000000000 : ℝ)) (aup := (1046529469/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar102 (p : ℝ) (hpa : (387/16 : ℝ) ≤ p) (hpb : p ≤ (775/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(387/16 : ℝ) ≤ (196254791/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (196254791/10000000000 : ℝ)) (by norm_num) (by norm_num) 387 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20196254791/10000000000 : ℝ) ≤ (643429597/625000000 : ℝ)^(387/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (643429597/625000000 : ℝ)) (X := (20196254791/10000000000 : ℝ)) (by norm_num) 387 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5232339889/5000000000 : ℝ)^(387/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5232339889/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 387 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (387/16 : ℝ)) (beta := (775/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (643429597/625000000 : ℝ)) (aup := (5232339889/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar103 (p : ℝ) (hpa : (775/32 : ℝ) ≤ p) (hpb : p ≤ (97/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(775/32 : ℝ) ≤ (39052119/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (39052119/2000000000 : ℝ)) (by norm_num) (by norm_num) 775 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4039052119/2000000000 : ℝ) ≤ (10294466597/10000000000 : ℝ)^(775/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10294466597/10000000000 : ℝ)) (X := (4039052119/2000000000 : ℝ)) (by norm_num) 775 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1046406649/1000000000 : ℝ)^(775/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1046406649/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 775 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (775/32 : ℝ)) (beta := (97/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10294466597/10000000000 : ℝ)) (aup := (1046406649/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar104 (p : ℝ) (hpa : (97/4 : ℝ) ≤ p) (hpb : p ≤ (777/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(97/4 : ℝ) ≤ (48567859/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (48567859/2500000000 : ℝ)) (by norm_num) (by norm_num) 97 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5048567859/2500000000 : ℝ) ≤ (10294060811/10000000000 : ℝ)^(97/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10294060811/10000000000 : ℝ)) (X := (5048567859/2500000000 : ℝ)) (by norm_num) 97 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10463454817/10000000000 : ℝ)^(97/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10463454817/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 97 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (97/4 : ℝ)) (beta := (777/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10294060811/10000000000 : ℝ)) (aup := (10463454817/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar105 (p : ℝ) (hpa : (777/32 : ℝ) ≤ p) (hpb : p ≤ (389/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(777/32 : ℝ) ≤ (193287287/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (193287287/10000000000 : ℝ)) (by norm_num) (by norm_num) 777 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20193287287/10000000000 : ℝ) ≤ (10293656191/10000000000 : ℝ)^(777/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10293656191/10000000000 : ℝ)) (X := (20193287287/10000000000 : ℝ)) (by norm_num) 777 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2092568951/2000000000 : ℝ)^(777/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2092568951/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 777 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (777/32 : ℝ)) (beta := (389/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10293656191/10000000000 : ℝ)) (aup := (2092568951/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar106 (p : ℝ) (hpa : (389/16 : ℝ) ≤ p) (hpb : p ≤ (779/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(389/16 : ℝ) ≤ (307693/16000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (307693/16000000 : ℝ)) (by norm_num) (by norm_num) 389 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (32307693/16000000 : ℝ) ≤ (10293252729/10000000000 : ℝ)^(389/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10293252729/10000000000 : ℝ)) (X := (32307693/16000000 : ℝ)) (by norm_num) 389 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10462236297/10000000000 : ℝ)^(389/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10462236297/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 389 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (389/16 : ℝ)) (beta := (779/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10293252729/10000000000 : ℝ)) (aup := (10462236297/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar107 (p : ℝ) (hpa : (779/32 : ℝ) ≤ p) (hpb : p ≤ (195/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(779/32 : ℝ) ≤ (95666961/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (95666961/5000000000 : ℝ)) (by norm_num) (by norm_num) 779 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10095666961/5000000000 : ℝ) ≤ (10292850423/10000000000 : ℝ)^(779/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10292850423/10000000000 : ℝ)) (X := (10095666961/5000000000 : ℝ)) (by norm_num) 779 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2615407359/2500000000 : ℝ)^(779/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2615407359/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 779 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (779/32 : ℝ)) (beta := (195/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10292850423/10000000000 : ℝ)) (aup := (2615407359/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar108 (p : ℝ) (hpa : (195/8 : ℝ) ≤ p) (hpb : p ≤ (781/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(195/8 : ℝ) ≤ (38072931/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (38072931/2000000000 : ℝ)) (by norm_num) (by norm_num) 195 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4038072931/2000000000 : ℝ) ≤ (2058489853/2000000000 : ℝ)^(195/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2058489853/2000000000 : ℝ)) (X := (4038072931/2000000000 : ℝ)) (by norm_num) 195 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5230512083/5000000000 : ℝ)^(195/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5230512083/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 195 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (195/8 : ℝ)) (beta := (781/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2058489853/2000000000 : ℝ)) (aup := (5230512083/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar109 (p : ℝ) (hpa : (781/32 : ℝ) ≤ p) (hpb : p ≤ (391/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(781/32 : ℝ) ≤ (94700149/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (94700149/5000000000 : ℝ)) (by norm_num) (by norm_num) 781 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10094700149/5000000000 : ℝ) ≤ (2573012313/2500000000 : ℝ)^(781/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2573012313/2500000000 : ℝ)) (X := (10094700149/5000000000 : ℝ)) (by norm_num) 781 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (16344407/15625000 : ℝ)^(781/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (16344407/15625000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 781 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (781/32 : ℝ)) (beta := (391/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2573012313/2500000000 : ℝ)) (aup := (16344407/15625000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar110 (p : ℝ) (hpa : (391/16 : ℝ) ≤ p) (hpb : p ≤ (783/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(391/16 : ℝ) ≤ (94220413/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (94220413/5000000000 : ℝ)) (by norm_num) (by norm_num) 391 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10094220413/5000000000 : ℝ) ≤ (10291650379/10000000000 : ℝ)^(391/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10291650379/10000000000 : ℝ)) (X := (10094220413/5000000000 : ℝ)) (by norm_num) 391 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5229909187/5000000000 : ℝ)^(391/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5229909187/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 391 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (391/16 : ℝ)) (beta := (783/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10291650379/10000000000 : ℝ)) (aup := (5229909187/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar111 (p : ℝ) (hpa : (783/32 : ℝ) ≤ p) (hpb : p ≤ (49/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(783/32 : ℝ) ≤ (93743107/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (93743107/5000000000 : ℝ)) (by norm_num) (by norm_num) 783 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10093743107/5000000000 : ℝ) ≤ (64320329/62500000 : ℝ)^(783/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (64320329/62500000 : ℝ)) (X := (10093743107/5000000000 : ℝ)) (by norm_num) 783 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (130740223/125000000 : ℝ)^(783/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (130740223/125000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 783 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (783/32 : ℝ)) (beta := (49/2 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (64320329/62500000 : ℝ)) (aup := (130740223/125000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk06 (p : ℝ) (hpa : (24 : ℝ) ≤ p) (hpb : p ≤ (49/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (97/4 : ℝ) with hl | hr
  ·
    rcases le_total p (193/8 : ℝ) with hal | har
    ·
      rcases le_total p (385/16 : ℝ) with haal | haar
      ·
        rcases le_total p (769/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar096 p hpa haaal
        ·
          exact lower21_scalar097 p haaar haal
      ·
        rcases le_total p (771/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar098 p haar haabl
        ·
          exact lower21_scalar099 p haabr hal
    ·
      rcases le_total p (387/16 : ℝ) with habl | habr
      ·
        rcases le_total p (773/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar100 p har habal
        ·
          exact lower21_scalar101 p habar habl
      ·
        rcases le_total p (775/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar102 p habr habbl
        ·
          exact lower21_scalar103 p habbr hl
  ·
    rcases le_total p (195/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (389/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (777/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar104 p hr hbaal
        ·
          exact lower21_scalar105 p hbaar hbal
      ·
        rcases le_total p (779/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar106 p hbar hbabl
        ·
          exact lower21_scalar107 p hbabr hbl
    ·
      rcases le_total p (391/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (781/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar108 p hbr hbbal
        ·
          exact lower21_scalar109 p hbbar hbbl
      ·
        rcases le_total p (783/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar110 p hbbr hbbbl
        ·
          exact lower21_scalar111 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk06
