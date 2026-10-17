import Hlawka21.FixedWitness

/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar112 (p : ℝ) (hpa : (49/2 : ℝ) ≤ p) (hpb : p ≤ (785/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(49/2 : ℝ) ≤ (186536439/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (186536439/10000000000 : ℝ)) (by norm_num) (by norm_num) 49 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20186536439/10000000000 : ℝ) ≤ (10290856031/10000000000 : ℝ)^(49/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10290856031/10000000000 : ℝ)) (X := (20186536439/10000000000 : ℝ)) (by norm_num) 49 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1307327359/1250000000 : ℝ)^(49/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1307327359/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 49 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (49/2 : ℝ)) (beta := (785/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10290856031/10000000000 : ℝ)) (aup := (1307327359/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar113 (p : ℝ) (hpa : (785/32 : ℝ) ≤ p) (hpb : p ≤ (393/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(785/32 : ℝ) ≤ (7423659/400000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (7423659/400000000 : ℝ)) (by norm_num) (by norm_num) 785 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (807423659/400000000 : ℝ) ≤ (10290460547/10000000000 : ℝ)^(785/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10290460547/10000000000 : ℝ)) (X := (807423659/400000000 : ℝ)) (by norm_num) 785 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2091604293/2000000000 : ℝ)^(785/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2091604293/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 785 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (785/32 : ℝ)) (beta := (393/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10290460547/10000000000 : ℝ)) (aup := (2091604293/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar114 (p : ℝ) (hpa : (393/16 : ℝ) ≤ p) (hpb : p ≤ (787/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(393/16 : ℝ) ≤ (92325649/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (92325649/5000000000 : ℝ)) (by norm_num) (by norm_num) 393 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10092325649/5000000000 : ℝ) ≤ (5145033091/5000000000 : ℝ)^(393/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5145033091/5000000000 : ℝ)) (X := (10092325649/5000000000 : ℝ)) (by norm_num) 393 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2614356403/2500000000 : ℝ)^(393/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2614356403/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 393 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (393/16 : ℝ)) (beta := (787/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5145033091/5000000000 : ℝ)) (aup := (2614356403/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar115 (p : ℝ) (hpa : (787/32 : ℝ) ≤ p) (hpb : p ≤ (197/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(787/32 : ℝ) ≤ (183715883/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (183715883/10000000000 : ℝ)) (by norm_num) (by norm_num) 787 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20183715883/10000000000 : ℝ) ≤ (10289672933/10000000000 : ℝ)^(787/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10289672933/10000000000 : ℝ)) (X := (20183715883/10000000000 : ℝ)) (by norm_num) 787 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5228415653/5000000000 : ℝ)^(787/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5228415653/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 787 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (787/32 : ℝ)) (beta := (197/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10289672933/10000000000 : ℝ)) (aup := (5228415653/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar116 (p : ℝ) (hpa : (197/8 : ℝ) ≤ p) (hpb : p ≤ (789/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(197/8 : ℝ) ≤ (22848151/1250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (22848151/1250000000 : ℝ)) (by norm_num) (by norm_num) 197 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2522848151/1250000000 : ℝ) ≤ (5144640397/5000000000 : ℝ)^(197/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5144640397/5000000000 : ℝ)) (X := (2522848151/1250000000 : ℝ)) (by norm_num) 197 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10456238543/10000000000 : ℝ)^(197/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10456238543/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 197 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (197/8 : ℝ)) (beta := (789/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5144640397/5000000000 : ℝ)) (aup := (10456238543/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar117 (p : ℝ) (hpa : (789/32 : ℝ) ≤ p) (hpb : p ≤ (395/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(789/32 : ℝ) ≤ (181859247/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (181859247/10000000000 : ℝ)) (by norm_num) (by norm_num) 789 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20181859247/10000000000 : ℝ) ≤ (64305561/62500000 : ℝ)^(789/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (64305561/62500000 : ℝ)) (X := (20181859247/10000000000 : ℝ)) (by norm_num) 789 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2613911829/2500000000 : ℝ)^(789/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2613911829/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 789 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (789/32 : ℝ)) (beta := (395/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (64305561/62500000 : ℝ)) (aup := (2613911829/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar118 (p : ℝ) (hpa : (395/16 : ℝ) ≤ p) (hpb : p ≤ (791/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(395/16 : ℝ) ≤ (180937977/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (180937977/10000000000 : ℝ)) (by norm_num) (by norm_num) 395 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20180937977/10000000000 : ℝ) ≤ (10288499827/10000000000 : ℝ)^(395/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10288499827/10000000000 : ℝ)) (X := (20180937977/10000000000 : ℝ)) (by norm_num) 395 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10455057619/10000000000 : ℝ)^(395/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10455057619/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 395 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (395/16 : ℝ)) (beta := (791/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10288499827/10000000000 : ℝ)) (aup := (10455057619/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar119 (p : ℝ) (hpa : (791/32 : ℝ) ≤ p) (hpb : p ≤ (99/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(791/32 : ℝ) ≤ (90010687/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (90010687/5000000000 : ℝ)) (by norm_num) (by norm_num) 791 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10090010687/5000000000 : ℝ) ≤ (1028811099/1000000000 : ℝ)^(791/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1028811099/1000000000 : ℝ)) (X := (10090010687/5000000000 : ℝ)) (by norm_num) 791 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5227234723/5000000000 : ℝ)^(791/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5227234723/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 791 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (791/32 : ℝ)) (beta := (99/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1028811099/1000000000 : ℝ)) (aup := (5227234723/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar120 (p : ℝ) (hpa : (99/4 : ℝ) ≤ p) (hpb : p ≤ (793/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(99/4 : ℝ) ≤ (89554707/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (89554707/5000000000 : ℝ)) (by norm_num) (by norm_num) 99 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10089554707/5000000000 : ℝ) ≤ (2057544649/2000000000 : ℝ)^(99/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2057544649/2000000000 : ℝ)) (X := (10089554707/5000000000 : ℝ)) (by norm_num) 99 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10453882791/10000000000 : ℝ)^(99/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10453882791/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 99 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (99/4 : ℝ)) (beta := (793/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2057544649/2000000000 : ℝ)) (aup := (10453882791/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar121 (p : ℝ) (hpa : (793/32 : ℝ) ≤ p) (hpb : p ≤ (397/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(793/32 : ℝ) ≤ (89101037/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (89101037/5000000000 : ℝ)) (by norm_num) (by norm_num) 793 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10089101037/5000000000 : ℝ) ≤ (5143668293/5000000000 : ℝ)^(793/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5143668293/5000000000 : ℝ)) (X := (10089101037/5000000000 : ℝ)) (by norm_num) 793 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10453297649/10000000000 : ℝ)^(793/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10453297649/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 793 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (793/32 : ℝ)) (beta := (397/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5143668293/5000000000 : ℝ)) (aup := (10453297649/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar122 (p : ℝ) (hpa : (397/16 : ℝ) ≤ p) (hpb : p ≤ (795/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(397/16 : ℝ) ≤ (17729933/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (17729933/1000000000 : ℝ)) (by norm_num) (by norm_num) 397 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (2017729933/1000000000 : ℝ) ≤ (10286951009/10000000000 : ℝ)^(397/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10286951009/10000000000 : ℝ)) (X := (2017729933/1000000000 : ℝ)) (by norm_num) 397 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10452714013/10000000000 : ℝ)^(397/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10452714013/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 397 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (397/16 : ℝ)) (beta := (795/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10286951009/10000000000 : ℝ)) (aup := (10452714013/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar123 (p : ℝ) (hpa : (795/32 : ℝ) ≤ p) (hpb : p ≤ (199/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(795/32 : ℝ) ≤ (4410029/250000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (4410029/250000000 : ℝ)) (by norm_num) (by norm_num) 795 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (504410029/250000000 : ℝ) ≤ (10286566509/10000000000 : ℝ)^(795/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10286566509/10000000000 : ℝ)) (X := (504410029/250000000 : ℝ)) (by norm_num) 795 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5226065939/5000000000 : ℝ)^(795/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5226065939/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 795 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (795/32 : ℝ)) (beta := (199/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10286566509/10000000000 : ℝ)) (aup := (5226065939/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar124 (p : ℝ) (hpa : (199/8 : ℝ) ≤ p) (hpb : p ≤ (797/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(199/8 : ℝ) ≤ (8775377/500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (8775377/500000000 : ℝ)) (by norm_num) (by norm_num) 199 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (1008775377/500000000 : ℝ) ≤ (10286183083/10000000000 : ℝ)^(199/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10286183083/10000000000 : ℝ)) (X := (1008775377/500000000 : ℝ)) (by norm_num) 199 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5225775619/5000000000 : ℝ)^(199/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5225775619/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 199 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (199/8 : ℝ)) (beta := (797/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10286183083/10000000000 : ℝ)) (aup := (5225775619/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar125 (p : ℝ) (hpa : (797/32 : ℝ) ≤ p) (hpb : p ≤ (399/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(797/32 : ℝ) ≤ (87309223/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (87309223/5000000000 : ℝ)) (by norm_num) (by norm_num) 797 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10087309223/5000000000 : ℝ) ≤ (2571450181/2500000000 : ℝ)^(797/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2571450181/2500000000 : ℝ)) (X := (10087309223/5000000000 : ℝ)) (by norm_num) 797 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10450972087/10000000000 : ℝ)^(797/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10450972087/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 797 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (797/32 : ℝ)) (beta := (399/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2571450181/2500000000 : ℝ)) (aup := (10450972087/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar126 (p : ℝ) (hpa : (399/16 : ℝ) ≤ p) (hpb : p ≤ (799/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(399/16 : ℝ) ≤ (173733857/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (173733857/10000000000 : ℝ)) (by norm_num) (by norm_num) 399 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20173733857/10000000000 : ℝ) ≤ (1028541943/1000000000 : ℝ)^(399/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1028541943/1000000000 : ℝ)) (X := (20173733857/10000000000 : ℝ)) (by norm_num) 399 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10450394419/10000000000 : ℝ)^(399/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10450394419/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 399 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (399/16 : ℝ)) (beta := (799/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (1028541943/1000000000 : ℝ)) (aup := (10450394419/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar127 (p : ℝ) (hpa : (799/32 : ℝ) ≤ p) (hpb : p ≤ (25 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(799/32 : ℝ) ≤ (172853749/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (172853749/10000000000 : ℝ)) (by norm_num) (by norm_num) 799 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20172853749/10000000000 : ℝ) ≤ (2057007839/2000000000 : ℝ)^(799/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2057007839/2000000000 : ℝ)) (X := (20172853749/10000000000 : ℝ)) (by norm_num) 799 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10449818229/10000000000 : ℝ)^(799/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10449818229/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 799 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (799/32 : ℝ)) (beta := (25 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2057007839/2000000000 : ℝ)) (aup := (10449818229/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk07 (p : ℝ) (hpa : (49/2 : ℝ) ≤ p) (hpb : p ≤ (25 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (99/4 : ℝ) with hl | hr
  ·
    rcases le_total p (197/8 : ℝ) with hal | har
    ·
      rcases le_total p (393/16 : ℝ) with haal | haar
      ·
        rcases le_total p (785/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar112 p hpa haaal
        ·
          exact lower21_scalar113 p haaar haal
      ·
        rcases le_total p (787/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar114 p haar haabl
        ·
          exact lower21_scalar115 p haabr hal
    ·
      rcases le_total p (395/16 : ℝ) with habl | habr
      ·
        rcases le_total p (789/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar116 p har habal
        ·
          exact lower21_scalar117 p habar habl
      ·
        rcases le_total p (791/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar118 p habr habbl
        ·
          exact lower21_scalar119 p habbr hl
  ·
    rcases le_total p (199/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (397/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (793/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar120 p hr hbaal
        ·
          exact lower21_scalar121 p hbaar hbal
      ·
        rcases le_total p (795/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar122 p hbar hbabl
        ·
          exact lower21_scalar123 p hbabr hbl
    ·
      rcases le_total p (399/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (797/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar124 p hbr hbbal
        ·
          exact lower21_scalar125 p hbbar hbbl
      ·
        rcases le_total p (799/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar126 p hbbr hbbbl
        ·
          exact lower21_scalar127 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.lower21_chunk07
