import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower26_scalar048 (p : ℝ) (hpa : (29 : ℝ) ≤ p) (hpb : p ≤ (465/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(29 : ℝ) ≤ (17622127/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (17622127/1000000000 : ℝ)) (by norm_num) (by norm_num) 29 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2017622127/1000000000 : ℝ) ≤ (2048998847/2000000000 : ℝ)^(29 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2048998847/2000000000 : ℝ)) (X := (2017622127/1000000000 : ℝ)) (by norm_num) 29 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10386098979/10000000000 : ℝ)^(29 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10386098979/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 29 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (29 : ℝ)) (beta := (465/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2048998847/2000000000 : ℝ)) (aup := (10386098979/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar049 (p : ℝ) (hpa : (465/16 : ℝ) ≤ p) (hpb : p ≤ (233/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(465/16 : ℝ) ≤ (174694117/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (174694117/10000000000 : ℝ)) (by norm_num) (by norm_num) 465 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20174694117/10000000000 : ℝ) ≤ (1280554287/1250000000 : ℝ)^(465/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1280554287/1250000000 : ℝ)) (X := (20174694117/10000000000 : ℝ)) (by norm_num) 465 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5192626433/5000000000 : ℝ)^(465/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5192626433/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 465 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (465/16 : ℝ)) (beta := (233/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1280554287/1250000000 : ℝ)) (aup := (5192626433/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar050 (p : ℝ) (hpa : (233/8 : ℝ) ≤ p) (hpb : p ≤ (467/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(233/8 : ℝ) ≤ (173180199/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (173180199/10000000000 : ℝ)) (by norm_num) (by norm_num) 233 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20173180199/10000000000 : ℝ) ≤ (10243877019/10000000000 : ℝ)^(233/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10243877019/10000000000 : ℝ)) (X := (20173180199/10000000000 : ℝ)) (by norm_num) 233 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10384410453/10000000000 : ℝ)^(233/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10384410453/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 233 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (233/8 : ℝ)) (beta := (467/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10243877019/10000000000 : ℝ)) (aup := (10384410453/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar051 (p : ℝ) (hpa : (467/16 : ℝ) ≤ p) (hpb : p ≤ (117/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(467/16 : ℝ) ≤ (858397/50000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (858397/50000000 : ℝ)) (by norm_num) (by norm_num) 467 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (100858397/50000000 : ℝ) ≤ (5121661193/5000000000 : ℝ)^(467/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5121661193/5000000000 : ℝ)) (X := (100858397/50000000 : ℝ)) (by norm_num) 467 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2595892929/2500000000 : ℝ)^(467/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2595892929/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 467 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (467/16 : ℝ)) (beta := (117/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5121661193/5000000000 : ℝ)) (aup := (2595892929/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar052 (p : ℝ) (hpa : (117/4 : ℝ) ≤ p) (hpb : p ≤ (469/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(117/4 : ℝ) ≤ (21273951/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (21273951/1250000000 : ℝ)) (by norm_num) (by norm_num) 117 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2521273951/1250000000 : ℝ) ≤ (1280346297/1250000000 : ℝ)^(117/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1280346297/1250000000 : ℝ)) (X := (2521273951/1250000000 : ℝ)) (by norm_num) 117 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1038273663/1000000000 : ℝ)^(117/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1038273663/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 117 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (117/4 : ℝ)) (beta := (469/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1280346297/1250000000 : ℝ)) (aup := (1038273663/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar053 (p : ℝ) (hpa : (469/16 : ℝ) ≤ p) (hpb : p ≤ (235/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(469/16 : ℝ) ≤ (42179177/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (42179177/2500000000 : ℝ)) (by norm_num) (by norm_num) 469 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5042179177/2500000000 : ℝ) ≤ (10242220971/10000000000 : ℝ)^(469/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10242220971/10000000000 : ℝ)) (X := (5042179177/2500000000 : ℝ)) (by norm_num) 469 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10381905173/10000000000 : ℝ)^(469/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10381905173/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 469 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (469/16 : ℝ)) (beta := (235/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10242220971/10000000000 : ℝ)) (aup := (10381905173/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar054 (p : ℝ) (hpa : (235/8 : ℝ) ≤ p) (hpb : p ≤ (471/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(235/8 : ℝ) ≤ (167254591/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (167254591/10000000000 : ℝ)) (by norm_num) (by norm_num) 235 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20167254591/10000000000 : ℝ) ≤ (1280209269/1250000000 : ℝ)^(235/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1280209269/1250000000 : ℝ)) (X := (20167254591/10000000000 : ℝ)) (by norm_num) 235 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10381077319/10000000000 : ℝ)^(235/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10381077319/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 235 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (235/8 : ℝ)) (beta := (471/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1280209269/1250000000 : ℝ)) (aup := (10381077319/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar055 (p : ℝ) (hpa : (471/16 : ℝ) ≤ p) (hpb : p ≤ (59/2 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(471/16 : ℝ) ≤ (20725643/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (20725643/1250000000 : ℝ)) (by norm_num) (by norm_num) 471 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2520725643/1250000000 : ℝ) ≤ (10241129901/10000000000 : ℝ)^(471/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10241129901/10000000000 : ℝ)) (X := (2520725643/1250000000 : ℝ)) (by norm_num) 471 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5190126523/5000000000 : ℝ)^(471/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5190126523/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 471 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (471/16 : ℝ)) (beta := (59/2 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10241129901/10000000000 : ℝ)) (aup := (5190126523/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar056 (p : ℝ) (hpa : (59/2 : ℝ) ≤ p) (hpb : p ≤ (473/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(59/2 : ℝ) ≤ (82184129/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (82184129/5000000000 : ℝ)) (by norm_num) (by norm_num) 59 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10082184129/5000000000 : ℝ) ≤ (51202941/50000000 : ℝ)^(59/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (51202941/50000000 : ℝ)) (X := (10082184129/5000000000 : ℝ)) (by norm_num) 59 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2594858083/2500000000 : ℝ)^(59/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2594858083/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 59 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (59/2 : ℝ)) (beta := (473/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (51202941/50000000 : ℝ)) (aup := (2594858083/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar057 (p : ℝ) (hpa : (473/16 : ℝ) ≤ p) (hpb : p ≤ (237/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(473/16 : ℝ) ≤ (6517753/400000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (6517753/400000000 : ℝ)) (by norm_num) (by norm_num) 473 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (806517753/400000000 : ℝ) ≤ (10240049029/10000000000 : ℝ)^(473/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10240049029/10000000000 : ℝ)) (X := (806517753/400000000 : ℝ)) (by norm_num) 473 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10378615151/10000000000 : ℝ)^(473/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10378615151/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 473 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (473/16 : ℝ)) (beta := (237/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10240049029/10000000000 : ℝ)) (aup := (10378615151/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar058 (p : ℝ) (hpa : (237/8 : ℝ) ≤ p) (hpb : p ≤ (475/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(237/8 : ℝ) ≤ (20191467/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (20191467/1250000000 : ℝ)) (by norm_num) (by norm_num) 237 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2520191467/1250000000 : ℝ) ≤ (2559878093/2500000000 : ℝ)^(237/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2559878093/2500000000 : ℝ)) (X := (2520191467/1250000000 : ℝ)) (by norm_num) 237 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10377801483/10000000000 : ℝ)^(237/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10377801483/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 237 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (237/8 : ℝ)) (beta := (475/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2559878093/2500000000 : ℝ)) (aup := (10377801483/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar059 (p : ℝ) (hpa : (475/16 : ℝ) ≤ p) (hpb : p ≤ (119/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(475/16 : ℝ) ≤ (40032971/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (40032971/2500000000 : ℝ)) (by norm_num) (by norm_num) 475 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5040032971/2500000000 : ℝ) ≤ (1023897821/1000000000 : ℝ)^(475/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1023897821/1000000000 : ℝ)) (X := (5040032971/2500000000 : ℝ)) (by norm_num) 475 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1297123913/1250000000 : ℝ)^(475/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1297123913/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 475 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (475/16 : ℝ)) (beta := (119/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1023897821/1000000000 : ℝ)) (aup := (1297123913/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar060 (p : ℝ) (hpa : (119/4 : ℝ) ≤ p) (hpb : p ≤ (477/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(119/4 : ℝ) ≤ (39686041/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (39686041/2500000000 : ℝ)) (by norm_num) (by norm_num) 119 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5039686041/2500000000 : ℝ) ≤ (409537861/400000000 : ℝ)^(119/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (409537861/400000000 : ℝ)) (X := (5039686041/2500000000 : ℝ)) (by norm_num) 119 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10376184593/10000000000 : ℝ)^(119/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10376184593/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 119 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (119/4 : ℝ)) (beta := (477/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (409537861/400000000 : ℝ)) (aup := (10376184593/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar061 (p : ℝ) (hpa : (477/16 : ℝ) ≤ p) (hpb : p ≤ (239/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(477/16 : ℝ) ≤ (157368469/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (157368469/10000000000 : ℝ)) (by norm_num) (by norm_num) 477 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20157368469/10000000000 : ℝ) ≤ (10237917301/10000000000 : ℝ)^(477/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10237917301/10000000000 : ℝ)) (X := (20157368469/10000000000 : ℝ)) (by norm_num) 477 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (415015253/400000000 : ℝ)^(477/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (415015253/400000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 477 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (477/16 : ℝ)) (beta := (239/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10237917301/10000000000 : ℝ)) (aup := (415015253/400000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar062 (p : ℝ) (hpa : (239/8 : ℝ) ≤ p) (hpb : p ≤ (479/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(239/8 : ℝ) ≤ (156004697/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (156004697/10000000000 : ℝ)) (by norm_num) (by norm_num) 239 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20156004697/10000000000 : ℝ) ≤ (10237390519/10000000000 : ℝ)^(239/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10237390519/10000000000 : ℝ)) (X := (20156004697/10000000000 : ℝ)) (by norm_num) 239 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10374581481/10000000000 : ℝ)^(239/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10374581481/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 239 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (239/8 : ℝ)) (beta := (479/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10237390519/10000000000 : ℝ)) (aup := (10374581481/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar063 (p : ℝ) (hpa : (479/16 : ℝ) ≤ p) (hpb : p ≤ (30 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(479/16 : ℝ) ≤ (154652743/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (154652743/10000000000 : ℝ)) (by norm_num) (by norm_num) 479 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20154652743/10000000000 : ℝ) ≤ (5118433081/5000000000 : ℝ)^(479/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5118433081/5000000000 : ℝ)) (X := (20154652743/10000000000 : ℝ)) (by norm_num) 479 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5186892519/5000000000 : ℝ)^(479/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5186892519/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 479 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (479/16 : ℝ)) (beta := (30 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5118433081/5000000000 : ℝ)) (aup := (5186892519/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_chunk03 (p : ℝ) (hpa : (29 : ℝ) ≤ p) (hpb : p ≤ (30 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (59/2 : ℝ) with hl | hr
  ·
    rcases le_total p (117/4 : ℝ) with hal | har
    ·
      rcases le_total p (233/8 : ℝ) with haal | haar
      ·
        rcases le_total p (465/16 : ℝ) with haaal | haaar
        ·
          exact lower26_scalar048 p hpa haaal
        ·
          exact lower26_scalar049 p haaar haal
      ·
        rcases le_total p (467/16 : ℝ) with haabl | haabr
        ·
          exact lower26_scalar050 p haar haabl
        ·
          exact lower26_scalar051 p haabr hal
    ·
      rcases le_total p (235/8 : ℝ) with habl | habr
      ·
        rcases le_total p (469/16 : ℝ) with habal | habar
        ·
          exact lower26_scalar052 p har habal
        ·
          exact lower26_scalar053 p habar habl
      ·
        rcases le_total p (471/16 : ℝ) with habbl | habbr
        ·
          exact lower26_scalar054 p habr habbl
        ·
          exact lower26_scalar055 p habbr hl
  ·
    rcases le_total p (119/4 : ℝ) with hbl | hbr
    ·
      rcases le_total p (237/8 : ℝ) with hbal | hbar
      ·
        rcases le_total p (473/16 : ℝ) with hbaal | hbaar
        ·
          exact lower26_scalar056 p hr hbaal
        ·
          exact lower26_scalar057 p hbaar hbal
      ·
        rcases le_total p (475/16 : ℝ) with hbabl | hbabr
        ·
          exact lower26_scalar058 p hbar hbabl
        ·
          exact lower26_scalar059 p hbabr hbl
    ·
      rcases le_total p (239/8 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (477/16 : ℝ) with hbbal | hbbar
        ·
          exact lower26_scalar060 p hbr hbbal
        ·
          exact lower26_scalar061 p hbbar hbbl
      ·
        rcases le_total p (479/16 : ℝ) with hbbbl | hbbbr
        ·
          exact lower26_scalar062 p hbbr hbbbl
        ·
          exact lower26_scalar063 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower26_chunk03
