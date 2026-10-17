import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar000 (p : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (673/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(21 : ℝ) ≤ (65891203/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (65891203/2000000000 : ℝ)) (by norm_num) (by norm_num) 21 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4065891203/2000000000 : ℝ) ≤ (2585905583/2500000000 : ℝ)^(21 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2585905583/2500000000 : ℝ)) (X := (4065891203/2000000000 : ℝ)) (by norm_num) 21 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10537074721/10000000000 : ℝ)^(21 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10537074721/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (21 : ℝ)) (beta := (673/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2585905583/2500000000 : ℝ)) (aup := (10537074721/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar001 (p : ℝ) (hpa : (673/32 : ℝ) ≤ p) (hpb : p ≤ (337/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(673/32 : ℝ) ≤ (327787043/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (327787043/10000000000 : ℝ)) (by norm_num) (by norm_num) 673 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20327787043/10000000000 : ℝ) ≤ (10343062713/10000000000 : ℝ)^(673/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10343062713/10000000000 : ℝ)) (X := (20327787043/10000000000 : ℝ)) (by norm_num) 673 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5268127833/5000000000 : ℝ)^(673/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5268127833/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 673 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (673/32 : ℝ)) (beta := (337/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10343062713/10000000000 : ℝ)) (aup := (5268127833/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar002 (p : ℝ) (hpa : (337/16 : ℝ) ≤ p) (hpb : p ≤ (675/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(337/16 : ℝ) ≤ (13045061/400000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (13045061/400000000 : ℝ)) (by norm_num) (by norm_num) 337 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (813045061/400000000 : ℝ) ≤ (2068500997/2000000000 : ℝ)^(337/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2068500997/2000000000 : ℝ)) (X := (813045061/400000000 : ℝ)) (by norm_num) 337 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (41154059/39062500 : ℝ)^(337/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (41154059/39062500 : ℝ)) (X := (3 : ℝ)) (by norm_num) 337 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (337/16 : ℝ)) (beta := (675/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2068500997/2000000000 : ℝ)) (aup := (41154059/39062500 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar003 (p : ℝ) (hpa : (675/32 : ℝ) ≤ p) (hpb : p ≤ (169/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(675/32 : ℝ) ≤ (16223721/500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (16223721/500000000 : ℝ)) (by norm_num) (by norm_num) 675 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1016223721/500000000 : ℝ) ≤ (10341949139/10000000000 : ℝ)^(675/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10341949139/10000000000 : ℝ)) (X := (1016223721/500000000 : ℝ)) (by norm_num) 675 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (421385001/400000000 : ℝ)^(675/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (421385001/400000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 675 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (675/32 : ℝ)) (beta := (169/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10341949139/10000000000 : ℝ)) (aup := (421385001/400000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar004 (p : ℝ) (hpa : (169/8 : ℝ) ≤ p) (hpb : p ≤ (677/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(169/8 : ℝ) ≤ (80707671/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (80707671/2500000000 : ℝ)) (by norm_num) (by norm_num) 169 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5080707671/2500000000 : ℝ) ≤ (2068279033/2000000000 : ℝ)^(169/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2068279033/2000000000 : ℝ)) (X := (5080707671/2500000000 : ℝ)) (by norm_num) 169 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10533813417/10000000000 : ℝ)^(169/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10533813417/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 169 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (169/8 : ℝ)) (beta := (677/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2068279033/2000000000 : ℝ)) (aup := (10533813417/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar005 (p : ℝ) (hpa : (677/32 : ℝ) ≤ p) (hpb : p ≤ (339/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(677/32 : ℝ) ≤ (12847811/400000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (12847811/400000000 : ℝ)) (by norm_num) (by norm_num) 677 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (812847811/400000000 : ℝ) ≤ (2068168611/2000000000 : ℝ)^(677/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2068168611/2000000000 : ℝ)) (X := (812847811/400000000 : ℝ)) (by norm_num) 677 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10533004269/10000000000 : ℝ)^(677/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10533004269/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 677 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (677/32 : ℝ)) (beta := (339/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2068168611/2000000000 : ℝ)) (aup := (10533004269/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar006 (p : ℝ) (hpa : (339/16 : ℝ) ≤ p) (hpb : p ≤ (679/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(339/16 : ℝ) ≤ (319568151/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (319568151/10000000000 : ℝ)) (by norm_num) (by norm_num) 339 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20319568151/10000000000 : ℝ) ≤ (10340292799/10000000000 : ℝ)^(339/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10340292799/10000000000 : ℝ)) (X := (20319568151/10000000000 : ℝ)) (by norm_num) 339 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1053219757/1000000000 : ℝ)^(339/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1053219757/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 339 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (339/16 : ℝ)) (beta := (679/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10340292799/10000000000 : ℝ)) (aup := (1053219757/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar007 (p : ℝ) (hpa : (679/32 : ℝ) ≤ p) (hpb : p ≤ (85/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(679/32 : ℝ) ≤ (317949269/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (317949269/10000000000 : ℝ)) (by norm_num) (by norm_num) 679 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20317949269/10000000000 : ℝ) ≤ (10339744387/10000000000 : ℝ)^(679/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10339744387/10000000000 : ℝ)) (X := (20317949269/10000000000 : ℝ)) (by norm_num) 679 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2632848327/2500000000 : ℝ)^(679/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2632848327/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 679 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (679/32 : ℝ)) (beta := (85/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10339744387/10000000000 : ℝ)) (aup := (2632848327/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar008 (p : ℝ) (hpa : (85/4 : ℝ) ≤ p) (hpb : p ≤ (681/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(85/4 : ℝ) ≤ (79084647/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (79084647/2500000000 : ℝ)) (by norm_num) (by norm_num) 85 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5079084647/2500000000 : ℝ) ≤ (1033919781/1000000000 : ℝ)^(85/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1033919781/1000000000 : ℝ)) (X := (5079084647/2500000000 : ℝ)) (by norm_num) 85 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10530591473/10000000000 : ℝ)^(85/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10530591473/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (85/4 : ℝ)) (beta := (681/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1033919781/1000000000 : ℝ)) (aup := (10530591473/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar009 (p : ℝ) (hpa : (681/32 : ℝ) ≤ p) (hpb : p ≤ (341/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(681/32 : ℝ) ≤ (314736067/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (314736067/10000000000 : ℝ)) (by norm_num) (by norm_num) 681 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20314736067/10000000000 : ℝ) ≤ (516932653/500000000 : ℝ)^(681/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (516932653/500000000 : ℝ)) (X := (20314736067/10000000000 : ℝ)) (by norm_num) 681 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5264896027/5000000000 : ℝ)^(681/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5264896027/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 681 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (681/32 : ℝ)) (beta := (341/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (516932653/500000000 : ℝ)) (aup := (5264896027/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar010 (p : ℝ) (hpa : (341/16 : ℝ) ≤ p) (hpb : p ≤ (683/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(341/16 : ℝ) ≤ (9785677/312500000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (9785677/312500000 : ℝ)) (by norm_num) (by norm_num) 341 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (634785677/312500000 : ℝ) ≤ (5169055063/5000000000 : ℝ)^(341/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5169055063/5000000000 : ℝ)) (X := (634785677/312500000 : ℝ)) (by norm_num) 341 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10528995039/10000000000 : ℝ)^(341/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10528995039/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 341 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (341/16 : ℝ)) (beta := (683/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5169055063/5000000000 : ℝ)) (aup := (10528995039/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar011 (p : ℝ) (hpa : (683/32 : ℝ) ≤ p) (hpb : p ≤ (171/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(683/32 : ℝ) ≤ (155777669/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (155777669/5000000000 : ℝ)) (by norm_num) (by norm_num) 683 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10155777669/5000000000 : ℝ) ≤ (10337569/10000000 : ℝ)^(683/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10337569/10000000 : ℝ)) (X := (10155777669/5000000000 : ℝ)) (by norm_num) 683 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5264100209/5000000000 : ℝ)^(683/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5264100209/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 683 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (683/32 : ℝ)) (beta := (171/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10337569/10000000 : ℝ)) (aup := (5264100209/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar012 (p : ℝ) (hpa : (171/8 : ℝ) ≤ p) (hpb : p ≤ (685/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(171/8 : ℝ) ≤ (38747131/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (38747131/1250000000 : ℝ)) (by norm_num) (by norm_num) 171 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2538747131/1250000000 : ℝ) ≤ (10337029673/10000000000 : ℝ)^(171/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10337029673/10000000000 : ℝ)) (X := (2538747131/1250000000 : ℝ)) (by norm_num) 171 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10527408181/10000000000 : ℝ)^(171/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10527408181/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 171 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (171/8 : ℝ)) (beta := (685/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10337029673/10000000000 : ℝ)) (aup := (10527408181/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar013 (p : ℝ) (hpa : (685/32 : ℝ) ≤ p) (hpb : p ≤ (343/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(685/32 : ℝ) ≤ (308406753/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (308406753/10000000000 : ℝ)) (by norm_num) (by norm_num) 685 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20308406753/10000000000 : ℝ) ≤ (1292061517/1250000000 : ℝ)^(685/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1292061517/1250000000 : ℝ)) (X := (20308406753/10000000000 : ℝ)) (by norm_num) 685 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2631654579/2500000000 : ℝ)^(685/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2631654579/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 685 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (685/32 : ℝ)) (beta := (343/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1292061517/1250000000 : ℝ)) (aup := (2631654579/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar014 (p : ℝ) (hpa : (343/16 : ℝ) ≤ p) (hpb : p ≤ (687/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(343/16 : ℝ) ≤ (306844413/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (306844413/10000000000 : ℝ)) (by norm_num) (by norm_num) 343 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20306844413/10000000000 : ℝ) ≤ (516797819/500000000 : ℝ)^(343/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (516797819/500000000 : ℝ)) (X := (20306844413/10000000000 : ℝ)) (by norm_num) 343 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2631457703/2500000000 : ℝ)^(343/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2631457703/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 343 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (343/16 : ℝ)) (beta := (687/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (516797819/500000000 : ℝ)) (aup := (2631457703/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar015 (p : ℝ) (hpa : (687/32 : ℝ) ≤ p) (hpb : p ≤ (43/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(687/32 : ℝ) ≤ (76322497/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (76322497/2500000000 : ℝ)) (by norm_num) (by norm_num) 687 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5076322497/2500000000 : ℝ) ≤ (2583855599/2500000000 : ℝ)^(687/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2583855599/2500000000 : ℝ)) (X := (5076322497/2500000000 : ℝ)) (by norm_num) 687 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (526252283/500000000 : ℝ)^(687/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (526252283/500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 687 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (687/32 : ℝ)) (beta := (43/2 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2583855599/2500000000 : ℝ)) (aup := (526252283/500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk00 (p : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (43/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (85/4 : ℝ) with hl | hr
  ·
    rcases le_total p (169/8 : ℝ) with hal | har
    ·
      rcases le_total p (337/16 : ℝ) with haal | haar
      ·
        rcases le_total p (673/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar000 p hpa haaal
        ·
          exact lower21_scalar001 p haaar haal
      ·
        rcases le_total p (675/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar002 p haar haabl
        ·
          exact lower21_scalar003 p haabr hal
    ·
      rcases le_total p (339/16 : ℝ) with habl | habr
      ·
        rcases le_total p (677/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar004 p har habal
        ·
          exact lower21_scalar005 p habar habl
      ·
        rcases le_total p (679/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar006 p habr habbl
        ·
          exact lower21_scalar007 p habbr hl
  ·
    rcases le_total p (171/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (341/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (681/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar008 p hr hbaal
        ·
          exact lower21_scalar009 p hbaar hbal
      ·
        rcases le_total p (683/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar010 p hbar hbabl
        ·
          exact lower21_scalar011 p hbabr hbl
    ·
      rcases le_total p (343/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (685/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar012 p hbr hbbal
        ·
          exact lower21_scalar013 p hbbar hbbl
      ·
        rcases le_total p (687/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar014 p hbbr hbbbl
        ·
          exact lower21_scalar015 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk00
