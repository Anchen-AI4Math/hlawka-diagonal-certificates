import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar016 (p : ℝ) (hpa : (43/2 : ℝ) ≤ p) (hpb : p ≤ (689/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(43/2 : ℝ) ≤ (303743437/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (303743437/10000000000 : ℝ)) (by norm_num) (by norm_num) 43 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20303743437/10000000000 : ℝ) ≤ (161482659/156250000 : ℝ)^(43/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (161482659/156250000 : ℝ)) (X := (20303743437/10000000000 : ℝ)) (by norm_num) 43 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10524262849/10000000000 : ℝ)^(43/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10524262849/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 43 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (43/2 : ℝ)) (beta := (689/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (161482659/156250000 : ℝ)) (aup := (10524262849/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar017 (p : ℝ) (hpa : (689/32 : ℝ) ≤ p) (hpb : p ≤ (345/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(689/32 : ℝ) ≤ (302204721/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (302204721/10000000000 : ℝ)) (by norm_num) (by norm_num) 689 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20302204721/10000000000 : ℝ) ≤ (1033435971/1000000000 : ℝ)^(689/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1033435971/1000000000 : ℝ)) (X := (20302204721/10000000000 : ℝ)) (by norm_num) 689 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (41107353/39062500 : ℝ)^(689/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (41107353/39062500 : ℝ)) (X := (3 : ℝ)) (by norm_num) 689 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (689/32 : ℝ)) (beta := (345/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1033435971/1000000000 : ℝ)) (aup := (41107353/39062500 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar018 (p : ℝ) (hpa : (345/16 : ℝ) ≤ p) (hpb : p ≤ (691/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(345/16 : ℝ) ≤ (1503369/50000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (1503369/50000000 : ℝ)) (by norm_num) (by norm_num) 345 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (101503369/50000000 : ℝ) ≤ (1033383099/1000000000 : ℝ)^(345/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1033383099/1000000000 : ℝ)) (X := (101503369/50000000 : ℝ)) (by norm_num) 345 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10522704207/10000000000 : ℝ)^(345/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10522704207/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 345 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (345/16 : ℝ)) (beta := (691/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1033383099/1000000000 : ℝ)) (aup := (10522704207/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar019 (p : ℝ) (hpa : (691/32 : ℝ) ≤ p) (hpb : p ≤ (173/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(691/32 : ℝ) ≤ (149575317/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (149575317/5000000000 : ℝ)) (by norm_num) (by norm_num) 691 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10149575317/5000000000 : ℝ) ≤ (10333304007/10000000000 : ℝ)^(691/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10333304007/10000000000 : ℝ)) (X := (10149575317/5000000000 : ℝ)) (by norm_num) 691 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2104385671/2000000000 : ℝ)^(691/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2104385671/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 691 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (691/32 : ℝ)) (beta := (173/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10333304007/10000000000 : ℝ)) (aup := (2104385671/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar020 (p : ℝ) (hpa : (173/8 : ℝ) ≤ p) (hpb : p ≤ (693/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(173/8 : ℝ) ≤ (18602199/625000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (18602199/625000000 : ℝ)) (by norm_num) (by norm_num) 173 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1268602199/625000000 : ℝ) ≤ (10332778753/10000000000 : ℝ)^(173/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10332778753/10000000000 : ℝ)) (X := (1268602199/625000000 : ℝ)) (by norm_num) 173 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10521154803/10000000000 : ℝ)^(173/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10521154803/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 173 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (173/8 : ℝ)) (beta := (693/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10332778753/10000000000 : ℝ)) (aup := (10521154803/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar021 (p : ℝ) (hpa : (693/32 : ℝ) ≤ p) (hpb : p ≤ (347/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(693/32 : ℝ) ≤ (74031853/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (74031853/2500000000 : ℝ)) (by norm_num) (by norm_num) 693 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5074031853/2500000000 : ℝ) ≤ (10332255219/10000000000 : ℝ)^(693/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10332255219/10000000000 : ℝ)) (X := (5074031853/2500000000 : ℝ)) (by norm_num) 693 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (526019177/500000000 : ℝ)^(693/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (526019177/500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 693 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (693/32 : ℝ)) (beta := (347/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10332255219/10000000000 : ℝ)) (aup := (526019177/500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar022 (p : ℝ) (hpa : (347/16 : ℝ) ≤ p) (hpb : p ≤ (695/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(347/16 : ℝ) ≤ (294627277/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (294627277/10000000000 : ℝ)) (by norm_num) (by norm_num) 347 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20294627277/10000000000 : ℝ) ≤ (5165866699/5000000000 : ℝ)^(347/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5165866699/5000000000 : ℝ)) (X := (20294627277/10000000000 : ℝ)) (by norm_num) 347 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2629903639/2500000000 : ℝ)^(347/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2629903639/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 347 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (347/16 : ℝ)) (beta := (695/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5165866699/5000000000 : ℝ)) (aup := (2629903639/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar023 (p : ℝ) (hpa : (695/32 : ℝ) ≤ p) (hpb : p ≤ (87/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(695/32 : ℝ) ≤ (146567371/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (146567371/5000000000 : ℝ)) (by norm_num) (by norm_num) 695 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10146567371/5000000000 : ℝ) ≤ (10331213279/10000000000 : ℝ)^(695/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10331213279/10000000000 : ℝ)) (X := (10146567371/5000000000 : ℝ)) (by norm_num) 695 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (65742799/62500000 : ℝ)^(695/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (65742799/62500000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 695 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (695/32 : ℝ)) (beta := (87/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10331213279/10000000000 : ℝ)) (aup := (65742799/62500000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar024 (p : ℝ) (hpa : (87/4 : ℝ) ≤ p) (hpb : p ≤ (697/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(87/4 : ℝ) ≤ (36456221/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (36456221/1250000000 : ℝ)) (by norm_num) (by norm_num) 87 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2536456221/1250000000 : ℝ) ≤ (1291336857/1250000000 : ℝ)^(87/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1291336857/1250000000 : ℝ)) (X := (2536456221/1250000000 : ℝ)) (by norm_num) 87 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1314760423/1250000000 : ℝ)^(87/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1314760423/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (87/4 : ℝ)) (beta := (697/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1291336857/1250000000 : ℝ)) (aup := (1314760423/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar025 (p : ℝ) (hpa : (697/32 : ℝ) ≤ p) (hpb : p ≤ (349/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(697/32 : ℝ) ≤ (72543079/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (72543079/2500000000 : ℝ)) (by norm_num) (by norm_num) 697 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5072543079/2500000000 : ℝ) ≤ (10330178119/10000000000 : ℝ)^(697/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10330178119/10000000000 : ℝ)) (X := (5072543079/2500000000 : ℝ)) (by norm_num) 697 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1314665147/1250000000 : ℝ)^(697/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1314665147/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 697 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (697/32 : ℝ)) (beta := (349/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10330178119/10000000000 : ℝ)) (aup := (1314665147/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar026 (p : ℝ) (hpa : (349/16 : ℝ) ≤ p) (hpb : p ≤ (699/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(349/16 : ℝ) ≤ (288702349/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (288702349/10000000000 : ℝ)) (by norm_num) (by norm_num) 349 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20288702349/10000000000 : ℝ) ≤ (5164831531/5000000000 : ℝ)^(349/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5164831531/5000000000 : ℝ)) (X := (20288702349/10000000000 : ℝ)) (by norm_num) 349 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1314570151/1250000000 : ℝ)^(349/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1314570151/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 349 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (349/16 : ℝ)) (beta := (699/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5164831531/5000000000 : ℝ)) (aup := (1314570151/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar027 (p : ℝ) (hpa : (699/32 : ℝ) ≤ p) (hpb : p ≤ (175/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(699/32 : ℝ) ≤ (287239829/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (287239829/10000000000 : ℝ)) (by norm_num) (by norm_num) 699 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20287239829/10000000000 : ℝ) ≤ (5164574837/5000000000 : ℝ)^(699/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5164574837/5000000000 : ℝ)) (X := (20287239829/10000000000 : ℝ)) (by norm_num) 699 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2628950867/2500000000 : ℝ)^(699/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2628950867/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 699 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (699/32 : ℝ)) (beta := (175/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5164574837/5000000000 : ℝ)) (aup := (2628950867/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar028 (p : ℝ) (hpa : (175/8 : ℝ) ≤ p) (hpb : p ≤ (701/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(175/8 : ℝ) ≤ (285784717/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (285784717/10000000000 : ℝ)) (by norm_num) (by norm_num) 175 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20285784717/10000000000 : ℝ) ≤ (10328637949/10000000000 : ℝ)^(175/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10328637949/10000000000 : ℝ)) (X := (20285784717/10000000000 : ℝ)) (by norm_num) 175 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2628761987/2500000000 : ℝ)^(175/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2628761987/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 175 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (175/8 : ℝ)) (beta := (701/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10328637949/10000000000 : ℝ)) (aup := (2628761987/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar029 (p : ℝ) (hpa : (701/32 : ℝ) ≤ p) (hpb : p ≤ (351/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(701/32 : ℝ) ≤ (284336977/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (284336977/10000000000 : ℝ)) (by norm_num) (by norm_num) 701 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20284336977/10000000000 : ℝ) ≤ (10328127877/10000000000 : ℝ)^(701/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10328127877/10000000000 : ℝ)) (X := (20284336977/10000000000 : ℝ)) (by norm_num) 701 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10514294637/10000000000 : ℝ)^(701/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10514294637/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 701 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (701/32 : ℝ)) (beta := (351/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10328127877/10000000000 : ℝ)) (aup := (10514294637/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar030 (p : ℝ) (hpa : (351/16 : ℝ) ≤ p) (hpb : p ≤ (703/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(351/16 : ℝ) ≤ (282896571/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (282896571/10000000000 : ℝ)) (by norm_num) (by norm_num) 351 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20282896571/10000000000 : ℝ) ≤ (2581904863/2500000000 : ℝ)^(351/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2581904863/2500000000 : ℝ)) (X := (20282896571/10000000000 : ℝ)) (by norm_num) 351 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10513543527/10000000000 : ℝ)^(351/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10513543527/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 351 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (351/16 : ℝ)) (beta := (703/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2581904863/2500000000 : ℝ)) (aup := (10513543527/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar031 (p : ℝ) (hpa : (703/32 : ℝ) ≤ p) (hpb : p ≤ (22 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(703/32 : ℝ) ≤ (140731731/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (140731731/5000000000 : ℝ)) (by norm_num) (by norm_num) 703 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10140731731/5000000000 : ℝ) ≤ (2065422533/2000000000 : ℝ)^(703/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2065422533/2000000000 : ℝ)) (X := (10140731731/5000000000 : ℝ)) (by norm_num) 703 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5256397303/5000000000 : ℝ)^(703/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5256397303/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 703 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (703/32 : ℝ)) (beta := (22 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2065422533/2000000000 : ℝ)) (aup := (5256397303/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk01 (p : ℝ) (hpa : (43/2 : ℝ) ≤ p) (hpb : p ≤ (22 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (87/4 : ℝ) with hl | hr
  ·
    rcases le_total p (173/8 : ℝ) with hal | har
    ·
      rcases le_total p (345/16 : ℝ) with haal | haar
      ·
        rcases le_total p (689/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar016 p hpa haaal
        ·
          exact lower21_scalar017 p haaar haal
      ·
        rcases le_total p (691/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar018 p haar haabl
        ·
          exact lower21_scalar019 p haabr hal
    ·
      rcases le_total p (347/16 : ℝ) with habl | habr
      ·
        rcases le_total p (693/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar020 p har habal
        ·
          exact lower21_scalar021 p habar habl
      ·
        rcases le_total p (695/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar022 p habr habbl
        ·
          exact lower21_scalar023 p habbr hl
  ·
    rcases le_total p (175/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (349/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (697/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar024 p hr hbaal
        ·
          exact lower21_scalar025 p hbaar hbal
      ·
        rcases le_total p (699/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar026 p hbar hbabl
        ·
          exact lower21_scalar027 p hbabr hbl
    ·
      rcases le_total p (351/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (701/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar028 p hbr hbbal
        ·
          exact lower21_scalar029 p hbbar hbbl
      ·
        rcases le_total p (703/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar030 p hbbr hbbbl
        ·
          exact lower21_scalar031 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk01
