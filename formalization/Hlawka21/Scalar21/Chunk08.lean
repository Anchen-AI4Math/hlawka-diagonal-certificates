import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar128 (p : ℝ) (hpa : (25 : ℝ) ≤ p) (hpb : p ≤ (801/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(25 : ℝ) ≤ (171978099/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (171978099/10000000000 : ℝ)) (by norm_num) (by norm_num) 25 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20171978099/10000000000 : ℝ) ≤ (5142330007/5000000000 : ℝ)^(25 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5142330007/5000000000 : ℝ)) (X := (20171978099/10000000000 : ℝ)) (by norm_num) 25 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1306155439/1250000000 : ℝ)^(25 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1306155439/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 25 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (25 : ℝ)) (beta := (801/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5142330007/5000000000 : ℝ)) (aup := (1306155439/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar129 (p : ℝ) (hpa : (801/32 : ℝ) ≤ p) (hpb : p ≤ (401/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(801/32 : ℝ) ≤ (34221377/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (34221377/2000000000 : ℝ)) (by norm_num) (by norm_num) 801 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4034221377/2000000000 : ℝ) ≤ (2571070471/2500000000 : ℝ)^(801/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2571070471/2500000000 : ℝ)) (X := (4034221377/2000000000 : ℝ)) (by norm_num) 801 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10448670261/10000000000 : ℝ)^(801/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10448670261/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 801 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (801/32 : ℝ)) (beta := (401/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2571070471/2500000000 : ℝ)) (aup := (10448670261/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar130 (p : ℝ) (hpa : (401/16 : ℝ) ≤ p) (hpb : p ≤ (803/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(401/16 : ℝ) ≤ (34048017/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (34048017/2000000000 : ℝ)) (by norm_num) (by norm_num) 401 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4034048017/2000000000 : ℝ) ≤ (10283904799/10000000000 : ℝ)^(401/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10283904799/10000000000 : ℝ)) (X := (4034048017/2000000000 : ℝ)) (by norm_num) 401 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10448098471/10000000000 : ℝ)^(401/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10448098471/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 401 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (401/16 : ℝ)) (beta := (803/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10283904799/10000000000 : ℝ)) (aup := (10448098471/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar131 (p : ℝ) (hpa : (803/32 : ℝ) ≤ p) (hpb : p ≤ (201/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(803/32 : ℝ) ≤ (42344419/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (42344419/2500000000 : ℝ)) (by norm_num) (by norm_num) 803 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5042344419/2500000000 : ℝ) ≤ (2570882189/2500000000 : ℝ)^(803/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2570882189/2500000000 : ℝ)) (X := (5042344419/2500000000 : ℝ)) (by norm_num) 803 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1305941017/1250000000 : ℝ)^(803/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1305941017/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 803 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (803/32 : ℝ)) (beta := (201/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2570882189/2500000000 : ℝ)) (aup := (1305941017/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar132 (p : ℝ) (hpa : (201/8 : ℝ) ≤ p) (hpb : p ≤ (805/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(201/8 : ℝ) ≤ (33703927/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (33703927/2000000000 : ℝ)) (by norm_num) (by norm_num) 201 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4033703927/2000000000 : ℝ) ≤ (8226523/8000000 : ℝ)^(201/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (8226523/8000000 : ℝ)) (X := (4033703927/2000000000 : ℝ)) (by norm_num) 201 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10446959251/10000000000 : ℝ)^(201/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10446959251/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 201 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (201/8 : ℝ)) (beta := (805/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (8226523/8000000 : ℝ)) (aup := (10446959251/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar133 (p : ℝ) (hpa : (805/32 : ℝ) ≤ p) (hpb : p ≤ (403/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(805/32 : ℝ) ≤ (167665941/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (167665941/10000000000 : ℝ)) (by norm_num) (by norm_num) 805 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20167665941/10000000000 : ℝ) ≤ (10282779777/10000000000 : ℝ)^(805/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10282779777/10000000000 : ℝ)) (X := (20167665941/10000000000 : ℝ)) (by norm_num) 805 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1044639181/1000000000 : ℝ)^(805/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1044639181/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 805 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (805/32 : ℝ)) (beta := (403/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10282779777/10000000000 : ℝ)) (aup := (1044639181/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar134 (p : ℝ) (hpa : (403/16 : ℝ) ≤ p) (hpb : p ≤ (807/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(403/16 : ℝ) ≤ (41704143/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (41704143/2500000000 : ℝ)) (by norm_num) (by norm_num) 403 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5041704143/2500000000 : ℝ) ≤ (642650427/625000000 : ℝ)^(403/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (642650427/625000000 : ℝ)) (X := (5041704143/2500000000 : ℝ)) (by norm_num) 403 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (652864113/625000000 : ℝ)^(403/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (652864113/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 403 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (403/16 : ℝ)) (beta := (807/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (642650427/625000000 : ℝ)) (aup := (652864113/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar135 (p : ℝ) (hpa : (807/32 : ℝ) ≤ p) (hpb : p ≤ (101/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(807/32 : ℝ) ≤ (82985753/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (82985753/5000000000 : ℝ)) (by norm_num) (by norm_num) 807 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10082985753/5000000000 : ℝ) ≤ (10282034911/10000000000 : ℝ)^(807/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10282034911/10000000000 : ℝ)) (X := (10082985753/5000000000 : ℝ)) (by norm_num) 807 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10445261239/10000000000 : ℝ)^(807/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10445261239/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 807 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (807/32 : ℝ)) (beta := (101/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10282034911/10000000000 : ℝ)) (aup := (10445261239/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar136 (p : ℝ) (hpa : (101/4 : ℝ) ≤ p) (hpb : p ≤ (809/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(101/4 : ℝ) ≤ (1032067/62500000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (1032067/62500000 : ℝ)) (by norm_num) (by norm_num) 101 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (126032067/62500000 : ℝ) ≤ (10281664009/10000000000 : ℝ)^(101/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10281664009/10000000000 : ℝ)) (X := (126032067/62500000 : ℝ)) (by norm_num) 101 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5222349049/5000000000 : ℝ)^(101/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5222349049/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 101 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (101/4 : ℝ)) (beta := (809/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10281664009/10000000000 : ℝ)) (aup := (5222349049/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar137 (p : ℝ) (hpa : (809/32 : ℝ) ≤ p) (hpb : p ≤ (405/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(809/32 : ℝ) ≤ (82147097/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (82147097/5000000000 : ℝ)) (by norm_num) (by norm_num) 809 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10082147097/5000000000 : ℝ) ≤ (10281294123/10000000000 : ℝ)^(809/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10281294123/10000000000 : ℝ)) (X := (10082147097/5000000000 : ℝ)) (by norm_num) 809 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10444136379/10000000000 : ℝ)^(809/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10444136379/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 809 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (809/32 : ℝ)) (beta := (405/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10281294123/10000000000 : ℝ)) (aup := (10444136379/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar138 (p : ℝ) (hpa : (405/16 : ℝ) ≤ p) (hpb : p ≤ (811/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(405/16 : ℝ) ≤ (81730953/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (81730953/5000000000 : ℝ)) (by norm_num) (by norm_num) 405 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10081730953/5000000000 : ℝ) ≤ (10280925249/10000000000 : ℝ)^(405/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10280925249/10000000000 : ℝ)) (X := (10081730953/5000000000 : ℝ)) (by norm_num) 405 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5221788039/5000000000 : ℝ)^(405/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5221788039/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 405 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (405/16 : ℝ)) (beta := (811/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10280925249/10000000000 : ℝ)) (aup := (5221788039/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar139 (p : ℝ) (hpa : (811/32 : ℝ) ≤ p) (hpb : p ≤ (203/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(811/32 : ℝ) ≤ (81316917/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (81316917/5000000000 : ℝ)) (by norm_num) (by norm_num) 811 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10081316917/5000000000 : ℝ) ≤ (10280557381/10000000000 : ℝ)^(811/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10280557381/10000000000 : ℝ)) (X := (10081316917/5000000000 : ℝ)) (by norm_num) 811 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2610754297/2500000000 : ℝ)^(811/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2610754297/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 811 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (811/32 : ℝ)) (beta := (203/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10280557381/10000000000 : ℝ)) (aup := (2610754297/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar140 (p : ℝ) (hpa : (203/8 : ℝ) ≤ p) (hpb : p ≤ (813/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(203/8 : ℝ) ≤ (161809957/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (161809957/10000000000 : ℝ)) (by norm_num) (by norm_num) 203 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20161809957/10000000000 : ℝ) ≤ (2570047629/2500000000 : ℝ)^(203/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2570047629/2500000000 : ℝ)) (X := (20161809957/10000000000 : ℝ)) (by norm_num) 203 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2088491941/2000000000 : ℝ)^(203/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2088491941/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 203 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (203/8 : ℝ)) (beta := (813/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2570047629/2500000000 : ℝ)) (aup := (2088491941/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar141 (p : ℝ) (hpa : (813/32 : ℝ) ≤ p) (hpb : p ≤ (407/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(813/32 : ℝ) ≤ (160990253/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (160990253/10000000000 : ℝ)) (by norm_num) (by norm_num) 813 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20160990253/10000000000 : ℝ) ≤ (205596493/200000000 : ℝ)^(813/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (205596493/200000000 : ℝ)) (X := (20160990253/10000000000 : ℝ)) (by norm_num) 813 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5220951811/5000000000 : ℝ)^(813/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5220951811/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 813 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (813/32 : ℝ)) (beta := (407/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (205596493/200000000 : ℝ)) (aup := (5220951811/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar142 (p : ℝ) (hpa : (407/16 : ℝ) ≤ p) (hpb : p ≤ (815/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(407/16 : ℝ) ≤ (80087351/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (80087351/5000000000 : ℝ)) (by norm_num) (by norm_num) 407 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10080087351/5000000000 : ℝ) ≤ (10279459779/10000000000 : ℝ)^(407/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10279459779/10000000000 : ℝ)) (X := (10080087351/5000000000 : ℝ)) (by norm_num) 407 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1305168617/1250000000 : ℝ)^(407/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1305168617/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 407 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (407/16 : ℝ)) (beta := (815/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10279459779/10000000000 : ℝ)) (aup := (1305168617/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar143 (p : ℝ) (hpa : (815/32 : ℝ) ≤ p) (hpb : p ≤ (51/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(815/32 : ℝ) ≤ (79681641/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (79681641/5000000000 : ℝ)) (by norm_num) (by norm_num) 815 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10079681641/5000000000 : ℝ) ≤ (10279095897/10000000000 : ℝ)^(815/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10279095897/10000000000 : ℝ)) (X := (10079681641/5000000000 : ℝ)) (by norm_num) 815 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (261019891/250000000 : ℝ)^(815/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (261019891/250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 815 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (815/32 : ℝ)) (beta := (51/2 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10279095897/10000000000 : ℝ)) (aup := (261019891/250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk08 (p : ℝ) (hpa : (25 : ℝ) ≤ p) (hpb : p ≤ (51/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (101/4 : ℝ) with hl | hr
  ·
    rcases le_total p (201/8 : ℝ) with hal | har
    ·
      rcases le_total p (401/16 : ℝ) with haal | haar
      ·
        rcases le_total p (801/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar128 p hpa haaal
        ·
          exact lower21_scalar129 p haaar haal
      ·
        rcases le_total p (803/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar130 p haar haabl
        ·
          exact lower21_scalar131 p haabr hal
    ·
      rcases le_total p (403/16 : ℝ) with habl | habr
      ·
        rcases le_total p (805/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar132 p har habal
        ·
          exact lower21_scalar133 p habar habl
      ·
        rcases le_total p (807/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar134 p habr habbl
        ·
          exact lower21_scalar135 p habbr hl
  ·
    rcases le_total p (203/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (405/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (809/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar136 p hr hbaal
        ·
          exact lower21_scalar137 p hbaar hbal
      ·
        rcases le_total p (811/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar138 p hbar hbabl
        ·
          exact lower21_scalar139 p hbabr hbl
    ·
      rcases le_total p (407/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (813/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar140 p hbr hbbal
        ·
          exact lower21_scalar141 p hbbar hbbl
      ·
        rcases le_total p (815/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar142 p hbbr hbbbl
        ·
          exact lower21_scalar143 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk08
