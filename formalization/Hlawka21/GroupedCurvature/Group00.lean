import Hlawka21.CurvatureComparison
import Hlawka21.GroupedGeometry.Group00

/- The actual original deficit Hessian is nonnegative on this
   norm-capped convex domain for every real p in the group. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem grouped_deficit_hessian00 (p K : ℝ) (hpa : (21 : ℝ) ≤ p) (hpb : p ≤ (377/16 : ℝ))
    (hKlo : (273/625 : ℝ)*p ≤ K) (hKhi : K ≤ p/2) :
    ∀ X : Triple, X ∈ normCappedDomain p (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ)
      (1193402307/1000000000 : ℝ) (3033/2500 : ℝ) (1139124440087/716625000000 : ℝ) (3314799982801/573300000000 : ℝ) →
    ∀ Z : Triple, 0 ≤ deficitHessian p K X Z := by
  let GT : ℝ := pairTotalFactor (881/2000 : ℝ) (11847/10000 : ℝ) (342380765087/716625000000 : ℝ) (3033/2500 : ℝ) (1 : ℝ) (1/4 : ℝ)
  let GC : ℝ := pairColumnFactor (881/2000 : ℝ) (11847/10000 : ℝ) (342380765087/716625000000 : ℝ) (3033/2500 : ℝ) (2287/5000 : ℝ) (1139124440087/716625000000 : ℝ) (1 : ℝ) (1/4 : ℝ)
  have hmarg := grouped_curvature_numeric00 p hpa hpb
  have hNT : (p/2) * GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) *
      (((2287/5000 : ℝ)*(3033/2500 : ℝ))/((1139124440087/716625000000 : ℝ)*(342380765087/716625000000 : ℝ))) ^ (p-2) ≤ 1 := by
    have hbase : (((2287/5000 : ℝ)*(3033/2500 : ℝ))/((1139124440087/716625000000 : ℝ)*(342380765087/716625000000 : ℝ))) = (284978746246398750000000/390014297326287552842569 : ℝ) := by norm_num
    have hconst : GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) / 2 = (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) := by
      norm_num [GT, pairTotalFactor, shapeFactor]
    have hprod : (p/2) * GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) = p * (21307564610023996610377722996681048402690000/1298308407084853791425263060884427285176983 : ℝ) := by
      calc _ = p * (GT * ((3033/2500 : ℝ)/(1139124440087/716625000000 : ℝ)) / 2) := by ring
           _ = _ := by rw [hconst]
    rw [hbase, hprod]
    exact hmarg.1.le
  have hNC : (GC/2) * ((1193402307/1000000000 : ℝ)/(1139124440087/716625000000 : ℝ)) *
      (((2287/5000 : ℝ)*(1193402307/1000000000 : ℝ))/((1139124440087/716625000000 : ℝ)*(881/2000 : ℝ))) ^ (p-2) ≤ 2*(273/625 : ℝ)-1/p := by
    have hbase : (((2287/5000 : ℝ)*(1193402307/1000000000 : ℝ))/((1139124440087/716625000000 : ℝ)*(881/2000 : ℝ))) = (15647140399332897/20071372634332940 : ℝ) := by norm_num
    have hconst : (GC/2) * ((1193402307/1000000000 : ℝ)/(1139124440087/716625000000 : ℝ)) = (126327058956291209168800111678206383698702611380575609988568615305922999/2156404247606560976075377673111402736989790882564566440401063762338560 : ℝ) := by
      norm_num [GC, pairColumnFactor, shapeFactor]
    rw [hbase, hconst]
    exact hmarg.2.le
  have hcoef := curvature_coefficients_from_ratios (p := p) (K := K) (c := (273/625 : ℝ))
    (m := (881/2000 : ℝ)) (s := (342380765087/716625000000 : ℝ)) (U := (1193402307/1000000000 : ℝ)) (A := (3033/2500 : ℝ))
    (eta := (2287/5000 : ℝ)) (L := (1139124440087/716625000000 : ℝ)) (gT := GT) (gC := GC)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num [GT, pairTotalFactor, shapeFactor])
    (by norm_num [GC, pairColumnFactor, shapeFactor])
    hKlo hKhi hNT hNC
  intro X hX Z
  exact deficit_hessian_domain_nonneg (m := (881/2000 : ℝ)) (M := (11847/10000 : ℝ))
    (L := (1139124440087/716625000000 : ℝ)) (s := (342380765087/716625000000 : ℝ)) (t := (3033/2500 : ℝ)) (eta := (2287/5000 : ℝ))
    (eps1 := (1 : ℝ)) (eps2 := (1/4 : ℝ))
    (by linarith) (by nlinarith [hKlo]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcoef.1 hcoef.2 X hX Z

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.grouped_deficit_hessian00
