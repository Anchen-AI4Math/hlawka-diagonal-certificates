import Hlawka21.ContractionCore

/- Exact grouped numeric margins for all real p in this interval.
   The geometric/Hessian implication is a separate proof obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21

theorem grouped_curvature_numeric00 (p : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ)) :
    p * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) * (284978746246398750000000/390014297326287552842569 : ℝ) ^ (p - 2) < 1 ∧
    (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) * (15647140399332897/20071372634332940 : ℝ) ^ (p - 2) < 2 * (273/625 : ℝ) - 1/p := by
  have hpn : 21 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hrt : (284978746246398750000000/390014297326287552842569 : ℝ) ^ (p - 2) ≤ (284978746246398750000000/390014297326287552842569 : ℝ) ^ (19 : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' (x := (284978746246398750000000/390014297326287552842569 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 19) (by linarith : (19 : ℝ) ≤ p - 2)
    calc _ ≤ (284978746246398750000000/390014297326287552842569 : ℝ) ^ ((19 : ℕ) : ℝ) := hh
         _ = _ := Real.rpow_natCast _ _
  have hrc : (15647140399332897/20071372634332940 : ℝ) ^ (p - 2) ≤ (15647140399332897/20071372634332940 : ℝ) ^ (19 : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' (x := (15647140399332897/20071372634332940 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 19) (by linarith : (19 : ℝ) ≤ p - 2)
    calc _ ≤ (15647140399332897/20071372634332940 : ℝ) ^ ((19 : ℕ) : ℝ) := hh
         _ = _ := Real.rpow_natCast _ _
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrt (show 0 ≤ p * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) * (284978746246398750000000/390014297326287552842569 : ℝ) ^ (19 : ℕ) by norm_num)
    have hend : (377/16 : ℝ) * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) * (284978746246398750000000/390014297326287552842569 : ℝ) ^ (19 : ℕ) < 1 := by norm_num
    nlinarith only [h1, h2, hend]
  · have h1 := mul_le_mul_of_nonneg_left hrc (show 0 ≤ (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(21 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpn
    have hend : (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) * (15647140399332897/20071372634332940 : ℝ) ^ (19 : ℕ) < 2 * (273/625 : ℝ) - 1/(21 : ℝ) := by norm_num
    linarith only [h1, hinv, hend]

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.grouped_curvature_numeric00
