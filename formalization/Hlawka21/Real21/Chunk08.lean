import Hlawka21.NormDomainInclusion
import Hlawka21.GroupedNonneg.Group01
import Hlawka21.Localized21.Slab128
import Hlawka21.Localized21.Slab129
import Hlawka21.Localized21.Slab130
import Hlawka21.Localized21.Slab131
import Hlawka21.Localized21.Slab132
import Hlawka21.Localized21.Slab133
import Hlawka21.Localized21.Slab134
import Hlawka21.Localized21.Slab135
import Hlawka21.Localized21.Slab136
import Hlawka21.Localized21.Slab137
import Hlawka21.Localized21.Slab138
import Hlawka21.Localized21.Slab139
import Hlawka21.Localized21.Slab140
import Hlawka21.Localized21.Slab141
import Hlawka21.Localized21.Slab142
import Hlawka21.Localized21.Slab143

/- Finite interval decisions and all domain inclusions are Lean proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 40000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localized_nonneg21_chunk08 (p : ℝ) (hpa : (25 : ℝ) ≤ p)
    (hpb : p ≤ (51/2 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  rcases le_total p (101/4 : ℝ) with hl | hr
  ·
    rcases le_total p (201/8 : ℝ) with hll | hlr
    ·
      rcases le_total p (401/16 : ℝ) with hlll | hllr
      ·
        rcases le_total p (801/32 : ℝ) with hllll | hlllr
        ·
          have hh := localize21_slab128 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab129 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (803/32 : ℝ) with hllrl | hllrr
        ·
          have hh := localize21_slab130 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab131 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (403/16 : ℝ) with hlrl | hlrr
      ·
        rcases le_total p (805/32 : ℝ) with hlrll | hlrlr
        ·
          have hh := localize21_slab132 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab133 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (807/32 : ℝ) with hlrrl | hlrrr
        ·
          have hh := localize21_slab134 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab135 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
  ·
    rcases le_total p (203/8 : ℝ) with hrl | hrr
    ·
      rcases le_total p (405/16 : ℝ) with hrll | hrlr
      ·
        rcases le_total p (809/32 : ℝ) with hrlll | hrllr
        ·
          have hh := localize21_slab136 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab137 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (811/32 : ℝ) with hrlrl | hrlrr
        ·
          have hh := localize21_slab138 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab139 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
    ·
      rcases le_total p (407/16 : ℝ) with hrrl | hrrr
      ·
        rcases le_total p (813/32 : ℝ) with hrrll | hrrlr
        ·
          have hh := localize21_slab140 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab141 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
      ·
        rcases le_total p (815/32 : ℝ) with hrrrl | hrrrr
        ·
          have hh := localize21_slab142 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD
        ·
          have hh := localize21_slab143 p (by linarith) (by linarith) X hB hS hT hG
          have hTA : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) := lt_of_lt_of_le hT (by norm_num)
          have hD : X ∈ normCappedDomain p (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) (149298789/125000000 : ℝ) (3033/2500 : ℝ) (82967765642843/51460500000000 : ℝ) (59752599691237/10292100000000 : ℝ) :=
            normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num)
          exact grouped_deficit_nonneg01 p (by linarith) (by linarith) X hD

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.localized_nonneg21_chunk08
