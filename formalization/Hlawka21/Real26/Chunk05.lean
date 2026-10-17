import Hlawka21.NormDomainInclusion
import Hlawka21.GroupedNonneg.Group01
import Hlawka21.Localized26.Slab080
import Hlawka21.Localized26.Slab081
import Hlawka21.Localized26.Slab082
import Hlawka21.Localized26.Slab083
import Hlawka21.Localized26.Slab084
import Hlawka21.Localized26.Slab085
import Hlawka21.Localized26.Slab086
import Hlawka21.Localized26.Slab087
import Hlawka21.Localized26.Slab088
import Hlawka21.Localized26.Slab089
import Hlawka21.Localized26.Slab090
import Hlawka21.Localized26.Slab091
import Hlawka21.Localized26.Slab092
import Hlawka21.Localized26.Slab093
import Hlawka21.Localized26.Slab094
import Hlawka21.Localized26.Slab095

/- Finite interval decisions and all domain inclusions are Lean proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localized_nonneg26_chunk05 (p : ℝ) (hpa : (31 : ℝ) ≤ p)
    (hpb : p ≤ (32 : ℝ)) (X : Triple)
    (hB : coordinateBox (477/1000 : ℝ) (1183/1000 : ℝ) (3/4 : ℝ) (1183/1000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (63/2 : ℝ) with hl | hr
  ·
    rcases le_total p (125/4 : ℝ) with hll | hlr
    ·
      rcases le_total p (249/8 : ℝ) with hlll | hllr
      ·
        rcases le_total p (497/16 : ℝ) with hllll | hlllr
        ·
          have hh := localize26_slab080 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab081 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (499/16 : ℝ) with hllrl | hllrr
        ·
          have hh := localize26_slab082 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab083 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (251/8 : ℝ) with hlrl | hlrr
      ·
        rcases le_total p (501/16 : ℝ) with hlrll | hlrlr
        ·
          have hh := localize26_slab084 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab085 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (503/16 : ℝ) with hlrrl | hlrrr
        ·
          have hh := localize26_slab086 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab087 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
  ·
    rcases le_total p (127/4 : ℝ) with hrl | hrr
    ·
      rcases le_total p (253/8 : ℝ) with hrll | hrlr
      ·
        rcases le_total p (505/16 : ℝ) with hrlll | hrllr
        ·
          have hh := localize26_slab088 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab089 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (507/16 : ℝ) with hrlrl | hrlrr
        ·
          have hh := localize26_slab090 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab091 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (255/8 : ℝ) with hrrl | hrrr
      ·
        rcases le_total p (509/16 : ℝ) with hrrll | hrrlr
        ·
          have hh := localize26_slab092 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab093 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (511/16 : ℝ) with hrrrl | hrrrr
        ·
          have hh := localize26_slab094 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize26_slab095 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.localized_nonneg26_chunk05
