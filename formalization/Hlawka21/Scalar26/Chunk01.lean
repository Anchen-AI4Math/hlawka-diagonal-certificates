import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower26_scalar016 (p : ℝ) (hpa : (27 : ℝ) ≤ p) (hpb : p ≤ (433/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(27 : ℝ) ≤ (29102469/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (29102469/1250000000 : ℝ)) (by norm_num) (by norm_num) 27 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2529102469/1250000000 : ℝ) ≤ (2566110959/2500000000 : ℝ)^(27 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2566110959/2500000000 : ℝ)) (X := (2529102469/1250000000 : ℝ)) (by norm_num) 27 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10415284983/10000000000 : ℝ)^(27 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10415284983/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 27 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (27 : ℝ)) (beta := (433/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2566110959/2500000000 : ℝ)) (aup := (10415284983/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar017 (p : ℝ) (hpa : (433/16 : ℝ) ≤ p) (hpb : p ≤ (217/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(433/16 : ℝ) ≤ (23080211/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (23080211/1000000000 : ℝ)) (by norm_num) (by norm_num) 433 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2023080211/1000000000 : ℝ) ≤ (5131893651/5000000000 : ℝ)^(433/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5131893651/5000000000 : ℝ)) (X := (2023080211/1000000000 : ℝ)) (by norm_num) 433 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1301788287/1250000000 : ℝ)^(433/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1301788287/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 433 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (433/16 : ℝ)) (beta := (217/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5131893651/5000000000 : ℝ)) (aup := (1301788287/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar018 (p : ℝ) (hpa : (217/8 : ℝ) ≤ p) (hpb : p ≤ (435/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(217/8 : ℝ) ≤ (114400977/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (114400977/5000000000 : ℝ)) (by norm_num) (by norm_num) 217 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10114400977/5000000000 : ℝ) ≤ (10263134159/10000000000 : ℝ)^(217/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10263134159/10000000000 : ℝ)) (X := (10114400977/5000000000 : ℝ)) (by norm_num) 217 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10413332211/10000000000 : ℝ)^(217/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10413332211/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 217 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (217/8 : ℝ)) (beta := (435/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10263134159/10000000000 : ℝ)) (aup := (10413332211/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar019 (p : ℝ) (hpa : (435/16 : ℝ) ≤ p) (hpb : p ≤ (109/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(435/16 : ℝ) ≤ (226819131/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (226819131/10000000000 : ℝ)) (by norm_num) (by norm_num) 435 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20226819131/10000000000 : ℝ) ≤ (513124219/500000000 : ℝ)^(435/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (513124219/500000000 : ℝ)) (X := (20226819131/10000000000 : ℝ)) (by norm_num) 435 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1301545337/1250000000 : ℝ)^(435/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1301545337/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 435 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (435/16 : ℝ)) (beta := (109/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (513124219/500000000 : ℝ)) (aup := (1301545337/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar020 (p : ℝ) (hpa : (109/4 : ℝ) ≤ p) (hpb : p ≤ (437/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(109/4 : ℝ) ≤ (224853491/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (224853491/10000000000 : ℝ)) (by norm_num) (by norm_num) 109 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20224853491/10000000000 : ℝ) ≤ (10261837939/10000000000 : ℝ)^(109/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10261837939/10000000000 : ℝ)) (X := (20224853491/10000000000 : ℝ)) (by norm_num) 109 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10411397717/10000000000 : ℝ)^(109/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10411397717/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 109 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (109/4 : ℝ)) (beta := (437/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10261837939/10000000000 : ℝ)) (aup := (10411397717/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar021 (p : ℝ) (hpa : (437/16 : ℝ) ≤ p) (hpb : p ≤ (219/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(437/16 : ℝ) ≤ (111452443/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (111452443/5000000000 : ℝ)) (by norm_num) (by norm_num) 437 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10111452443/5000000000 : ℝ) ≤ (1026119481/1000000000 : ℝ)^(437/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1026119481/1000000000 : ℝ)) (X := (10111452443/5000000000 : ℝ)) (by norm_num) 437 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10410437243/10000000000 : ℝ)^(437/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10410437243/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 437 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (437/16 : ℝ)) (beta := (219/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (1026119481/1000000000 : ℝ)) (aup := (10410437243/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar022 (p : ℝ) (hpa : (219/8 : ℝ) ≤ p) (hpb : p ≤ (439/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(219/8 : ℝ) ≤ (13810823/625000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (13810823/625000000 : ℝ)) (by norm_num) (by norm_num) 219 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1263810823/625000000 : ℝ) ≤ (10260554967/10000000000 : ℝ)^(219/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10260554967/10000000000 : ℝ)) (X := (1263810823/625000000 : ℝ)) (by norm_num) 219 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10409481243/10000000000 : ℝ)^(219/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10409481243/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 219 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (219/8 : ℝ)) (beta := (439/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10260554967/10000000000 : ℝ)) (aup := (10409481243/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar023 (p : ℝ) (hpa : (439/16 : ℝ) ≤ p) (hpb : p ≤ (55/2 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(439/16 : ℝ) ≤ (21905819/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (21905819/1000000000 : ℝ)) (by norm_num) (by norm_num) 439 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2021905819/1000000000 : ℝ) ≤ (641244899/625000000 : ℝ)^(439/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (641244899/625000000 : ℝ)) (X := (2021905819/1000000000 : ℝ)) (by norm_num) 439 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2081705937/2000000000 : ℝ)^(439/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2081705937/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 439 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (439/16 : ℝ)) (beta := (55/2 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (641244899/625000000 : ℝ)) (aup := (2081705937/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar024 (p : ℝ) (hpa : (55/2 : ℝ) ≤ p) (hpb : p ≤ (441/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(55/2 : ℝ) ≤ (1696561/78125000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (1696561/78125000 : ℝ)) (by norm_num) (by norm_num) 55 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (157946561/78125000 : ℝ) ≤ (5129642519/5000000000 : ℝ)^(55/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5129642519/5000000000 : ℝ)) (X := (157946561/78125000 : ℝ)) (by norm_num) 55 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10407582539/10000000000 : ℝ)^(55/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10407582539/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 55 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (55/2 : ℝ)) (beta := (441/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5129642519/5000000000 : ℝ)) (aup := (10407582539/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar025 (p : ℝ) (hpa : (441/16 : ℝ) ≤ p) (hpb : p ≤ (221/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(441/16 : ℝ) ≤ (215277877/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (215277877/10000000000 : ℝ)) (by norm_num) (by norm_num) 441 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20215277877/10000000000 : ℝ) ≤ (5129327451/5000000000 : ℝ)^(441/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5129327451/5000000000 : ℝ)) (X := (20215277877/10000000000 : ℝ)) (by norm_num) 441 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (416265591/400000000 : ℝ)^(441/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (416265591/400000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 441 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (441/16 : ℝ)) (beta := (221/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5129327451/5000000000 : ℝ)) (aup := (416265591/400000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar026 (p : ℝ) (hpa : (221/8 : ℝ) ≤ p) (hpb : p ≤ (443/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(221/8 : ℝ) ≤ (42682451/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (42682451/2000000000 : ℝ)) (by norm_num) (by norm_num) 221 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4042682451/2000000000 : ℝ) ≤ (10258027953/10000000000 : ℝ)^(221/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10258027953/10000000000 : ℝ)) (X := (4042682451/2000000000 : ℝ)) (by norm_num) 221 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (130071267/125000000 : ℝ)^(221/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (130071267/125000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 221 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (221/8 : ℝ)) (beta := (443/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10258027953/10000000000 : ℝ)) (aup := (130071267/125000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar027 (p : ℝ) (hpa : (443/16 : ℝ) ≤ p) (hpb : p ≤ (111/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(443/16 : ℝ) ≤ (211562801/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (211562801/10000000000 : ℝ)) (by norm_num) (by norm_num) 443 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20211562801/10000000000 : ℝ) ≤ (2051480833/2000000000 : ℝ)^(443/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2051480833/2000000000 : ℝ)) (X := (20211562801/10000000000 : ℝ)) (by norm_num) 443 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10404767267/10000000000 : ℝ)^(443/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10404767267/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 443 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (443/16 : ℝ)) (beta := (111/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2051480833/2000000000 : ℝ)) (aup := (10404767267/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar028 (p : ℝ) (hpa : (111/4 : ℝ) ≤ p) (hpb : p ≤ (445/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(111/4 : ℝ) ≤ (104864687/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (104864687/5000000000 : ℝ)) (by norm_num) (by norm_num) 111 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10104864687/5000000000 : ℝ) ≤ (5128391757/5000000000 : ℝ)^(111/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5128391757/5000000000 : ℝ)) (X := (10104864687/5000000000 : ℝ)) (by norm_num) 111 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2080767493/2000000000 : ℝ)^(111/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2080767493/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 111 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (111/4 : ℝ)) (beta := (445/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5128391757/5000000000 : ℝ)) (aup := (2080767493/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar029 (p : ℝ) (hpa : (445/16 : ℝ) ≤ p) (hpb : p ≤ (223/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(445/16 : ℝ) ≤ (51977959/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (51977959/2500000000 : ℝ)) (by norm_num) (by norm_num) 445 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5051977959/2500000000 : ℝ) ≤ (5128082989/5000000000 : ℝ)^(445/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5128082989/5000000000 : ℝ)) (X := (5051977959/2500000000 : ℝ)) (by norm_num) 445 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2600727981/2500000000 : ℝ)^(445/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2600727981/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 445 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (445/16 : ℝ)) (beta := (223/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5128082989/5000000000 : ℝ)) (aup := (2600727981/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar030 (p : ℝ) (hpa : (223/8 : ℝ) ≤ p) (hpb : p ≤ (447/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(223/8 : ℝ) ≤ (4122201/200000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (4122201/200000000 : ℝ)) (by norm_num) (by norm_num) 223 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (404122201/200000000 : ℝ) ≤ (10255551531/10000000000 : ℝ)^(223/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10255551531/10000000000 : ℝ)) (X := (404122201/200000000 : ℝ)) (by norm_num) 223 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2080398123/2000000000 : ℝ)^(223/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2080398123/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 223 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (223/8 : ℝ)) (beta := (447/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10255551531/10000000000 : ℝ)) (aup := (2080398123/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar031 (p : ℝ) (hpa : (447/16 : ℝ) ≤ p) (hpb : p ≤ (28 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(447/16 : ℝ) ≤ (204323877/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (204323877/10000000000 : ℝ)) (by norm_num) (by norm_num) 447 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20204323877/10000000000 : ℝ) ≤ (10254940151/10000000000 : ℝ)^(447/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10254940151/10000000000 : ℝ)) (X := (20204323877/10000000000 : ℝ)) (by norm_num) 447 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10401073509/10000000000 : ℝ)^(447/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10401073509/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 447 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (447/16 : ℝ)) (beta := (28 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10254940151/10000000000 : ℝ)) (aup := (10401073509/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_chunk01 (p : ℝ) (hpa : (27 : ℝ) ≤ p) (hpb : p ≤ (28 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (55/2 : ℝ) with hl | hr
  ·
    rcases le_total p (109/4 : ℝ) with hal | har
    ·
      rcases le_total p (217/8 : ℝ) with haal | haar
      ·
        rcases le_total p (433/16 : ℝ) with haaal | haaar
        ·
          exact lower26_scalar016 p hpa haaal
        ·
          exact lower26_scalar017 p haaar haal
      ·
        rcases le_total p (435/16 : ℝ) with haabl | haabr
        ·
          exact lower26_scalar018 p haar haabl
        ·
          exact lower26_scalar019 p haabr hal
    ·
      rcases le_total p (219/8 : ℝ) with habl | habr
      ·
        rcases le_total p (437/16 : ℝ) with habal | habar
        ·
          exact lower26_scalar020 p har habal
        ·
          exact lower26_scalar021 p habar habl
      ·
        rcases le_total p (439/16 : ℝ) with habbl | habbr
        ·
          exact lower26_scalar022 p habr habbl
        ·
          exact lower26_scalar023 p habbr hl
  ·
    rcases le_total p (111/4 : ℝ) with hbl | hbr
    ·
      rcases le_total p (221/8 : ℝ) with hbal | hbar
      ·
        rcases le_total p (441/16 : ℝ) with hbaal | hbaar
        ·
          exact lower26_scalar024 p hr hbaal
        ·
          exact lower26_scalar025 p hbaar hbal
      ·
        rcases le_total p (443/16 : ℝ) with hbabl | hbabr
        ·
          exact lower26_scalar026 p hbar hbabl
        ·
          exact lower26_scalar027 p hbabr hbl
    ·
      rcases le_total p (223/8 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (445/16 : ℝ) with hbbal | hbbar
        ·
          exact lower26_scalar028 p hbr hbbal
        ·
          exact lower26_scalar029 p hbbar hbbl
      ·
        rcases le_total p (447/16 : ℝ) with hbbbl | hbbbr
        ·
          exact lower26_scalar030 p hbbr hbbbl
        ·
          exact lower26_scalar031 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower26_chunk01
