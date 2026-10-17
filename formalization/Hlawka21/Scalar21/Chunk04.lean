import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar064 (p : ℝ) (hpa : (23 : ℝ) ≤ p) (hpb : p ≤ (737/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(23 : ℝ) ≤ (238031971/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (238031971/10000000000 : ℝ)) (by norm_num) (by norm_num) 23 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20238031971/10000000000 : ℝ) ≤ (5155629127/5000000000 : ℝ)^(23 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5155629127/5000000000 : ℝ)) (X := (20238031971/10000000000 : ℝ)) (by norm_num) 23 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10489249177/10000000000 : ℝ)^(23 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10489249177/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 23 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (23 : ℝ)) (beta := (737/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5155629127/5000000000 : ℝ)) (aup := (10489249177/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar065 (p : ℝ) (hpa : (737/32 : ℝ) ≤ p) (hpb : p ≤ (369/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(737/32 : ℝ) ≤ (118413069/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (118413069/5000000000 : ℝ)) (by norm_num) (by norm_num) 737 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10118413069/5000000000 : ℝ) ≤ (10310802751/10000000000 : ℝ)^(737/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10310802751/10000000000 : ℝ)) (X := (10118413069/5000000000 : ℝ)) (by norm_num) 737 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (524428469/500000000 : ℝ)^(737/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (524428469/500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 737 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (737/32 : ℝ)) (beta := (369/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10310802751/10000000000 : ℝ)) (aup := (524428469/500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar066 (p : ℝ) (hpa : (369/16 : ℝ) ≤ p) (hpb : p ≤ (739/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(369/16 : ℝ) ≤ (47125283/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (47125283/2000000000 : ℝ)) (by norm_num) (by norm_num) 369 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4047125283/2000000000 : ℝ) ≤ (2577587159/2500000000 : ℝ)^(369/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2577587159/2500000000 : ℝ)) (X := (4047125283/2000000000 : ℝ)) (by norm_num) 369 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2621972867/2500000000 : ℝ)^(369/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2621972867/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 369 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (369/16 : ℝ)) (beta := (739/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2577587159/2500000000 : ℝ)) (aup := (2621972867/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar067 (p : ℝ) (hpa : (739/32 : ℝ) ≤ p) (hpb : p ≤ (185/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(739/32 : ℝ) ≤ (234432769/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (234432769/10000000000 : ℝ)) (by norm_num) (by norm_num) 739 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20234432769/10000000000 : ℝ) ≤ (5154947951/5000000000 : ℝ)^(739/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5154947951/5000000000 : ℝ)) (X := (20234432769/10000000000 : ℝ)) (by norm_num) 739 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2621803859/2500000000 : ℝ)^(739/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2621803859/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 739 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (739/32 : ℝ)) (beta := (185/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5154947951/5000000000 : ℝ)) (aup := (2621803859/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar068 (p : ℝ) (hpa : (185/8 : ℝ) ≤ p) (hpb : p ≤ (741/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(185/8 : ℝ) ≤ (233245169/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (233245169/10000000000 : ℝ)) (by norm_num) (by norm_num) 185 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20233245169/10000000000 : ℝ) ≤ (10309444543/10000000000 : ℝ)^(185/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10309444543/10000000000 : ℝ)) (X := (20233245169/10000000000 : ℝ)) (by norm_num) 185 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10486541273/10000000000 : ℝ)^(185/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10486541273/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 185 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (185/8 : ℝ)) (beta := (741/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10309444543/10000000000 : ℝ)) (aup := (10486541273/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar069 (p : ℝ) (hpa : (741/32 : ℝ) ≤ p) (hpb : p ≤ (371/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(741/32 : ℝ) ≤ (116031793/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (116031793/5000000000 : ℝ)) (by norm_num) (by norm_num) 741 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10116031793/5000000000 : ℝ) ≤ (10308994553/10000000000 : ℝ)^(741/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10308994553/10000000000 : ℝ)) (X := (10116031793/5000000000 : ℝ)) (by norm_num) 741 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5242934487/5000000000 : ℝ)^(741/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5242934487/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 741 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (741/32 : ℝ)) (beta := (371/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10308994553/10000000000 : ℝ)) (aup := (5242934487/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar070 (p : ℝ) (hpa : (371/16 : ℝ) ≤ p) (hpb : p ≤ (743/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(371/16 : ℝ) ≤ (230887989/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (230887989/10000000000 : ℝ)) (by norm_num) (by norm_num) 371 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20230887989/10000000000 : ℝ) ≤ (412341837/400000000 : ℝ)^(371/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (412341837/400000000 : ℝ)) (X := (20230887989/10000000000 : ℝ)) (by norm_num) 371 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10485198529/10000000000 : ℝ)^(371/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10485198529/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 371 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (371/16 : ℝ)) (beta := (743/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (412341837/400000000 : ℝ)) (aup := (10485198529/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar071 (p : ℝ) (hpa : (743/32 : ℝ) ≤ p) (hpb : p ≤ (93/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(743/32 : ℝ) ≤ (229718347/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (229718347/10000000000 : ℝ)) (by norm_num) (by norm_num) 743 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20229718347/10000000000 : ℝ) ≤ (5154049327/5000000000 : ℝ)^(743/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5154049327/5000000000 : ℝ)) (X := (20229718347/10000000000 : ℝ)) (by norm_num) 743 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2621132483/2500000000 : ℝ)^(743/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2621132483/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 743 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (743/32 : ℝ)) (beta := (93/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5154049327/5000000000 : ℝ)) (aup := (2621132483/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar072 (p : ℝ) (hpa : (93/4 : ℝ) ≤ p) (hpb : p ≤ (745/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(93/4 : ℝ) ≤ (22855463/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (22855463/1000000000 : ℝ)) (by norm_num) (by norm_num) 93 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2022855463/1000000000 : ℝ) ≤ (2576913183/2500000000 : ℝ)^(93/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2576913183/2500000000 : ℝ)) (X := (2022855463/1000000000 : ℝ)) (by norm_num) 93 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (419354527/400000000 : ℝ)^(93/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (419354527/400000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (93/4 : ℝ)) (beta := (745/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2576913183/2500000000 : ℝ)) (aup := (419354527/400000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar073 (p : ℝ) (hpa : (745/32 : ℝ) ≤ p) (hpb : p ≤ (373/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(745/32 : ℝ) ≤ (227396809/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (227396809/10000000000 : ℝ)) (by norm_num) (by norm_num) 745 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20227396809/10000000000 : ℝ) ≤ (2061441631/2000000000 : ℝ)^(745/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2061441631/2000000000 : ℝ)) (X := (20227396809/10000000000 : ℝ)) (by norm_num) 745 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10483198249/10000000000 : ℝ)^(745/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10483198249/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 745 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (745/32 : ℝ)) (beta := (373/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2061441631/2000000000 : ℝ)) (aup := (10483198249/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar074 (p : ℝ) (hpa : (373/16 : ℝ) ≤ p) (hpb : p ≤ (747/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(373/16 : ℝ) ≤ (56561213/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (56561213/2500000000 : ℝ)) (by norm_num) (by norm_num) 373 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5056561213/2500000000 : ℝ) ≤ (2061352983/2000000000 : ℝ)^(373/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2061352983/2000000000 : ℝ)) (X := (5056561213/2500000000 : ℝ)) (by norm_num) 373 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10482535149/10000000000 : ℝ)^(373/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10482535149/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 373 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (373/16 : ℝ)) (beta := (747/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2061352983/2000000000 : ℝ)) (aup := (10482535149/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar075 (p : ℝ) (hpa : (747/32 : ℝ) ≤ p) (hpb : p ≤ (187/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(747/32 : ℝ) ≤ (56274683/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (56274683/2500000000 : ℝ)) (by norm_num) (by norm_num) 747 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5056274683/2500000000 : ℝ) ≤ (10306323007/10000000000 : ℝ)^(747/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10306323007/10000000000 : ℝ)) (X := (5056274683/2500000000 : ℝ)) (by norm_num) 747 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2096374773/2000000000 : ℝ)^(747/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2096374773/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 747 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (747/32 : ℝ)) (beta := (187/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10306323007/10000000000 : ℝ)) (aup := (2096374773/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar076 (p : ℝ) (hpa : (187/8 : ℝ) ≤ p) (hpb : p ≤ (749/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(187/8 : ℝ) ≤ (223958417/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (223958417/10000000000 : ℝ)) (by norm_num) (by norm_num) 187 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20223958417/10000000000 : ℝ) ≤ (412235297/400000000 : ℝ)^(187/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (412235297/400000000 : ℝ)) (X := (20223958417/10000000000 : ℝ)) (by norm_num) 187 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1310151799/1250000000 : ℝ)^(187/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1310151799/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 187 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (187/8 : ℝ)) (beta := (749/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (412235297/400000000 : ℝ)) (aup := (1310151799/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar077 (p : ℝ) (hpa : (749/32 : ℝ) ≤ p) (hpb : p ≤ (375/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(749/32 : ℝ) ≤ (222823879/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (222823879/10000000000 : ℝ)) (by norm_num) (by norm_num) 749 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20222823879/10000000000 : ℝ) ≤ (5152721581/5000000000 : ℝ)^(749/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5152721581/5000000000 : ℝ)) (X := (20222823879/10000000000 : ℝ)) (by norm_num) 749 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (131006959/125000000 : ℝ)^(749/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (131006959/125000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 749 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (749/32 : ℝ)) (beta := (375/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5152721581/5000000000 : ℝ)) (aup := (131006959/125000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar078 (p : ℝ) (hpa : (375/16 : ℝ) ≤ p) (hpb : p ≤ (751/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(375/16 : ℝ) ≤ (221695089/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (221695089/10000000000 : ℝ)) (by norm_num) (by norm_num) 375 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20221695089/10000000000 : ℝ) ≤ (10305005213/10000000000 : ℝ)^(375/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10305005213/10000000000 : ℝ)) (X := (20221695089/10000000000 : ℝ)) (by norm_num) 375 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2619975211/2500000000 : ℝ)^(375/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2619975211/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 375 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (375/16 : ℝ)) (beta := (751/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10305005213/10000000000 : ℝ)) (aup := (2619975211/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar079 (p : ℝ) (hpa : (751/32 : ℝ) ≤ p) (hpb : p ≤ (47/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(751/32 : ℝ) ≤ (220572017/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (220572017/10000000000 : ℝ)) (by norm_num) (by norm_num) 751 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20220572017/10000000000 : ℝ) ≤ (10304568571/10000000000 : ℝ)^(751/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10304568571/10000000000 : ℝ)) (X := (20220572017/10000000000 : ℝ)) (by norm_num) 751 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2095849351/2000000000 : ℝ)^(751/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2095849351/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 751 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (751/32 : ℝ)) (beta := (47/2 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10304568571/10000000000 : ℝ)) (aup := (2095849351/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk04 (p : ℝ) (hpa : (23 : ℝ) ≤ p) (hpb : p ≤ (47/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (93/4 : ℝ) with hl | hr
  ·
    rcases le_total p (185/8 : ℝ) with hal | har
    ·
      rcases le_total p (369/16 : ℝ) with haal | haar
      ·
        rcases le_total p (737/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar064 p hpa haaal
        ·
          exact lower21_scalar065 p haaar haal
      ·
        rcases le_total p (739/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar066 p haar haabl
        ·
          exact lower21_scalar067 p haabr hal
    ·
      rcases le_total p (371/16 : ℝ) with habl | habr
      ·
        rcases le_total p (741/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar068 p har habal
        ·
          exact lower21_scalar069 p habar habl
      ·
        rcases le_total p (743/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar070 p habr habbl
        ·
          exact lower21_scalar071 p habbr hl
  ·
    rcases le_total p (187/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (373/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (745/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar072 p hr hbaal
        ·
          exact lower21_scalar073 p hbaar hbal
      ·
        rcases le_total p (747/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar074 p hbar hbabl
        ·
          exact lower21_scalar075 p hbabr hbl
    ·
      rcases le_total p (375/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (749/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar076 p hbr hbbal
        ·
          exact lower21_scalar077 p hbbar hbbl
      ·
        rcases le_total p (751/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar078 p hbbr hbbbl
        ·
          exact lower21_scalar079 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk04
