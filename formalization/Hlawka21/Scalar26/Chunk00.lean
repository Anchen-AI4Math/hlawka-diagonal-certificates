import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower26_scalar000 (p : ℝ) (hpa : (26 : ℝ) ≤ p) (hpb : p ≤ (417/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(26 : ℝ) ≤ (26760891/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (26760891/1000000000 : ℝ)) (by norm_num) (by norm_num) 26 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2026760891/1000000000 : ℝ) ≤ (10275432171/10000000000 : ℝ)^(26 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10275432171/10000000000 : ℝ)) (X := (2026760891/1000000000 : ℝ)) (by norm_num) 26 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5215798701/5000000000 : ℝ)^(26 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5215798701/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 26 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (26 : ℝ)) (beta := (417/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10275432171/10000000000 : ℝ)) (aup := (5215798701/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar001 (p : ℝ) (hpa : (417/16 : ℝ) ≤ p) (hpb : p ≤ (209/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(417/16 : ℝ) ≤ (132644891/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (132644891/5000000000 : ℝ)) (by norm_num) (by norm_num) 417 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10132644891/5000000000 : ℝ) ≤ (10274717557/10000000000 : ℝ)^(417/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10274717557/10000000000 : ℝ)) (X := (10132644891/5000000000 : ℝ)) (by norm_num) 417 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10430540429/10000000000 : ℝ)^(417/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10430540429/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 417 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (417/16 : ℝ)) (beta := (209/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10274717557/10000000000 : ℝ)) (aup := (10430540429/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar002 (p : ℝ) (hpa : (209/8 : ℝ) ≤ p) (hpb : p ≤ (419/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(209/8 : ℝ) ≤ (262990751/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (262990751/10000000000 : ℝ)) (by norm_num) (by norm_num) 209 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20262990751/10000000000 : ℝ) ≤ (2568501699/2500000000 : ℝ)^(209/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2568501699/2500000000 : ℝ)) (X := (20262990751/10000000000 : ℝ)) (by norm_num) 209 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (521474431/500000000 : ℝ)^(209/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (521474431/500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 209 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (209/8 : ℝ)) (beta := (419/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2568501699/2500000000 : ℝ)) (aup := (521474431/500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar003 (p : ℝ) (hpa : (419/16 : ℝ) ≤ p) (hpb : p ≤ (105/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(419/16 : ℝ) ≤ (65177911/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (65177911/2500000000 : ℝ)) (by norm_num) (by norm_num) 419 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5065177911/2500000000 : ℝ) ≤ (5136649929/5000000000 : ℝ)^(419/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5136649929/5000000000 : ℝ)) (X := (5065177911/2500000000 : ℝ)) (by norm_num) 419 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (651777621/625000000 : ℝ)^(419/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (651777621/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 419 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (419/16 : ℝ)) (beta := (105/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5136649929/5000000000 : ℝ)) (aup := (651777621/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar004 (p : ℝ) (hpa : (105/4 : ℝ) ≤ p) (hpb : p ≤ (421/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(105/4 : ℝ) ≤ (258452289/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (258452289/10000000000 : ℝ)) (by norm_num) (by norm_num) 105 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20258452289/10000000000 : ℝ) ≤ (10272596711/10000000000 : ℝ)^(105/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10272596711/10000000000 : ℝ)) (X := (20258452289/10000000000 : ℝ)) (by norm_num) 105 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10427400341/10000000000 : ℝ)^(105/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10427400341/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 105 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (105/4 : ℝ)) (beta := (421/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10272596711/10000000000 : ℝ)) (aup := (10427400341/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar005 (p : ℝ) (hpa : (421/16 : ℝ) ≤ p) (hpb : p ≤ (211/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(421/16 : ℝ) ≤ (256212513/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (256212513/10000000000 : ℝ)) (by norm_num) (by norm_num) 421 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20256212513/10000000000 : ℝ) ≤ (410875893/400000000 : ℝ)^(421/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (410875893/400000000 : ℝ)) (X := (20256212513/10000000000 : ℝ)) (by norm_num) 421 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5213181899/5000000000 : ℝ)^(421/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5213181899/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 421 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (421/16 : ℝ)) (beta := (211/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (410875893/400000000 : ℝ)) (aup := (5213181899/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar006 (p : ℝ) (hpa : (211/8 : ℝ) ≤ p) (hpb : p ≤ (423/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(211/8 : ℝ) ≤ (253992147/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (253992147/10000000000 : ℝ)) (by norm_num) (by norm_num) 211 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20253992147/10000000000 : ℝ) ≤ (10271201669/10000000000 : ℝ)^(211/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10271201669/10000000000 : ℝ)) (X := (20253992147/10000000000 : ℝ)) (by norm_num) 211 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10425332269/10000000000 : ℝ)^(211/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10425332269/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 211 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (211/8 : ℝ)) (beta := (423/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10271201669/10000000000 : ℝ)) (aup := (10425332269/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar007 (p : ℝ) (hpa : (423/16 : ℝ) ≤ p) (hpb : p ≤ (53/2 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(423/16 : ℝ) ≤ (251791023/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (251791023/10000000000 : ℝ)) (by norm_num) (by norm_num) 423 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20251791023/10000000000 : ℝ) ≤ (10270509713/10000000000 : ℝ)^(423/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10270509713/10000000000 : ℝ)) (X := (20251791023/10000000000 : ℝ)) (by norm_num) 423 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10424305719/10000000000 : ℝ)^(423/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10424305719/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 423 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (423/16 : ℝ)) (beta := (53/2 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10270509713/10000000000 : ℝ)) (aup := (10424305719/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar008 (p : ℝ) (hpa : (53/2 : ℝ) ≤ p) (hpb : p ≤ (425/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(53/2 : ℝ) ≤ (124804487/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (124804487/5000000000 : ℝ)) (by norm_num) (by norm_num) 53 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10124804487/5000000000 : ℝ) ≤ (2567455357/2500000000 : ℝ)^(53/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2567455357/2500000000 : ℝ)) (X := (10124804487/5000000000 : ℝ)) (by norm_num) 53 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (651455257/625000000 : ℝ)^(53/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (651455257/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 53 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (53/2 : ℝ)) (beta := (425/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2567455357/2500000000 : ℝ)) (aup := (651455257/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar009 (p : ℝ) (hpa : (425/16 : ℝ) ≤ p) (hpb : p ≤ (213/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(425/16 : ℝ) ≤ (49489167/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (49489167/2000000000 : ℝ)) (by norm_num) (by norm_num) 425 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4049489167/2000000000 : ℝ) ≤ (2053827357/2000000000 : ℝ)^(425/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2053827357/2000000000 : ℝ)) (X := (4049489167/2000000000 : ℝ)) (by norm_num) 425 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10422267411/10000000000 : ℝ)^(425/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10422267411/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 425 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (425/16 : ℝ)) (beta := (213/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (2053827357/2000000000 : ℝ)) (aup := (10422267411/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar010 (p : ℝ) (hpa : (213/8 : ℝ) ≤ p) (hpb : p ≤ (427/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(213/8 : ℝ) ≤ (122650721/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (122650721/5000000000 : ℝ)) (by norm_num) (by norm_num) 213 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10122650721/5000000000 : ℝ) ≤ (10268455753/10000000000 : ℝ)^(213/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10268455753/10000000000 : ℝ)) (X := (10122650721/5000000000 : ℝ)) (by norm_num) 213 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5210627791/5000000000 : ℝ)^(213/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5210627791/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 213 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (213/8 : ℝ)) (beta := (427/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10268455753/10000000000 : ℝ)) (aup := (5210627791/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar011 (p : ℝ) (hpa : (427/16 : ℝ) ≤ p) (hpb : p ≤ (107/4 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(427/16 : ℝ) ≤ (243175633/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (243175633/10000000000 : ℝ)) (by norm_num) (by norm_num) 427 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20243175633/10000000000 : ℝ) ≤ (5133889153/5000000000 : ℝ)^(427/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5133889153/5000000000 : ℝ)) (X := (20243175633/10000000000 : ℝ)) (by norm_num) 427 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1042024859/1000000000 : ℝ)^(427/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1042024859/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 427 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (427/16 : ℝ)) (beta := (107/4 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5133889153/5000000000 : ℝ)) (aup := (1042024859/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar012 (p : ℝ) (hpa : (107/4 : ℝ) ≤ p) (hpb : p ≤ (429/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(107/4 : ℝ) ≤ (120534123/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (120534123/5000000000 : ℝ)) (by norm_num) (by norm_num) 107 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10120534123/5000000000 : ℝ) ≤ (10267104413/10000000000 : ℝ)^(107/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10267104413/10000000000 : ℝ)) (X := (10120534123/5000000000 : ℝ)) (by norm_num) 107 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10419246401/10000000000 : ℝ)^(107/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10419246401/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 107 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (107/4 : ℝ)) (beta := (429/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10267104413/10000000000 : ℝ)) (aup := (10419246401/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar013 (p : ℝ) (hpa : (429/16 : ℝ) ≤ p) (hpb : p ≤ (215/8 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(429/16 : ℝ) ≤ (119489561/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (119489561/5000000000 : ℝ)) (by norm_num) (by norm_num) 429 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10119489561/5000000000 : ℝ) ≤ (20051629/19531250 : ℝ)^(429/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (20051629/19531250 : ℝ)) (X := (10119489561/5000000000 : ℝ)) (by norm_num) 429 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10418248979/10000000000 : ℝ)^(429/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10418248979/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 429 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (429/16 : ℝ)) (beta := (215/8 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (20051629/19531250 : ℝ)) (aup := (10418248979/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar014 (p : ℝ) (hpa : (215/8 : ℝ) ≤ p) (hpb : p ≤ (431/16 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(215/8 : ℝ) ≤ (236908103/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (236908103/10000000000 : ℝ)) (by norm_num) (by norm_num) 215 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20236908103/10000000000 : ℝ) ≤ (10265767181/10000000000 : ℝ)^(215/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10265767181/10000000000 : ℝ)) (X := (20236908103/10000000000 : ℝ)) (by norm_num) 215 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10417256291/10000000000 : ℝ)^(215/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10417256291/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 215 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (215/8 : ℝ)) (beta := (431/16 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (10265767181/10000000000 : ℝ)) (aup := (10417256291/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_scalar015 (p : ℝ) (hpa : (431/16 : ℝ) ≤ p) (hpb : p ≤ (27 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  have ht : (87/100 : ℝ)^(431/16 : ℝ) ≤ (234855031/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (87/100 : ℝ)) (X := (234855031/10000000000 : ℝ)) (by norm_num) (by norm_num) 431 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20234855031/10000000000 : ℝ) ≤ (5132551893/5000000000 : ℝ)^(431/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5132551893/5000000000 : ℝ)) (X := (20234855031/10000000000 : ℝ)) (by norm_num) 431 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10416268303/10000000000 : ℝ)^(431/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10416268303/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 431 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (431/16 : ℝ)) (beta := (27 : ℝ))
    (t := (87/100 : ℝ)) (Aup := (5132551893/5000000000 : ℝ)) (aup := (10416268303/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower26_chunk00 (p : ℝ) (hpa : (26 : ℝ) ≤ p) (hpb : p ≤ (27 : ℝ)) :
    (443/1000 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (53/2 : ℝ) with hl | hr
  ·
    rcases le_total p (105/4 : ℝ) with hal | har
    ·
      rcases le_total p (209/8 : ℝ) with haal | haar
      ·
        rcases le_total p (417/16 : ℝ) with haaal | haaar
        ·
          exact lower26_scalar000 p hpa haaal
        ·
          exact lower26_scalar001 p haaar haal
      ·
        rcases le_total p (419/16 : ℝ) with haabl | haabr
        ·
          exact lower26_scalar002 p haar haabl
        ·
          exact lower26_scalar003 p haabr hal
    ·
      rcases le_total p (211/8 : ℝ) with habl | habr
      ·
        rcases le_total p (421/16 : ℝ) with habal | habar
        ·
          exact lower26_scalar004 p har habal
        ·
          exact lower26_scalar005 p habar habl
      ·
        rcases le_total p (423/16 : ℝ) with habbl | habbr
        ·
          exact lower26_scalar006 p habr habbl
        ·
          exact lower26_scalar007 p habbr hl
  ·
    rcases le_total p (107/4 : ℝ) with hbl | hbr
    ·
      rcases le_total p (213/8 : ℝ) with hbal | hbar
      ·
        rcases le_total p (425/16 : ℝ) with hbaal | hbaar
        ·
          exact lower26_scalar008 p hr hbaal
        ·
          exact lower26_scalar009 p hbaar hbal
      ·
        rcases le_total p (427/16 : ℝ) with hbabl | hbabr
        ·
          exact lower26_scalar010 p hbar hbabl
        ·
          exact lower26_scalar011 p hbabr hbl
    ·
      rcases le_total p (215/8 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (429/16 : ℝ) with hbbal | hbbar
        ·
          exact lower26_scalar012 p hbr hbbal
        ·
          exact lower26_scalar013 p hbbar hbbl
      ·
        rcases le_total p (431/16 : ℝ) with hbbbl | hbbbr
        ·
          exact lower26_scalar014 p hbbr hbbbl
        ·
          exact lower26_scalar015 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower26_chunk00
