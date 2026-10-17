import Hlawka21.Orientation
import Hlawka21.CoarseConnection21
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
/- Arbitrary strict real-three failures, including zero and unequal-norm
   input triples, are reflected, rescaled and oriented before LP localization.
   The generic normalization/orientation argument is attributed to Ezzeri Esa
   and @bwdaugherty (Apache-2.0); constants and LP connection are cutoff-specific. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem coarse_failure21 {p q : ℝ} (hp : 21 ≤ p)
    (hlinear : (273/625 : ℝ) * p < cyclicConstant p)
    (hq0 : 0 < q) (hq : q ≤ (1011/2500 : ℝ))
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Triple,
      coordinateBox (189/500 : ℝ) (607/500 : ℝ)
        (349/500 : ℝ) (607/500 : ℝ) X ∧
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
      lpNorm p (X 0 + X 1 + X 2) < 3 * q ∧
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625) * p) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  set K := cyclicConstant p with hKdef
  have hK : (5733/625 : ℝ) < K := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT, hTq⟩ :=
    Failure.scaled_failure hp1 (by linarith) hq0 (by linarith) henvelope x y z hf
  set T := lpNorm p (x + y + z) with hTdef
  have hT : T < 3033/2500 := by linarith
  -- Failure gives `K G < 3 - T`.
  have hG0 := pairGapSum_nonneg hp1.le x y z
  have hKG : K * pairGapSum (lpNorm p) x y z < 3 - T := by
    have h := hf
    rw [hlawkaDeficit_eq, tripleGap, hS] at h
    linarith
  have hG : (5733/625 : ℝ) * pairGapSum (lpNorm p) x y z + T < 3 := by
    have := mul_le_mul_of_nonneg_right hK.le hG0
    linarith
  have hTone : 1 ≤ T := by linarith
  have hGp : pairGapSum (lpNorm p) x y z < 2 / ((273/625) * p) := by
    rw [lt_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hlinear.le hG0
    nlinarith
  have hxy0 := pairGap_nonneg hp1.le x y
  have hxz0 := pairGap_nonneg hp1.le x z
  have hyz0 := pairGap_nonneg hp1.le y z
  have hGsplit := hG
  dsimp only [pairGapSum, pairGap] at hGsplit hxy0 hxz0 hyz0
  -- Pass 0.
  have hNx := lpNorm_nonneg p x
  have hNy := lpNorm_nonneg p y
  have hNz := lpNorm_nonneg p z
  obtain ⟨i, s, hs, hsxy⟩ := exists_signed_coord_bound (m := (21 : ℝ)) (B := (3033/1250 : ℝ)) (E := (13/100 : ℝ)) (by norm_num) hp (by norm_num) (x + y)
    (by linarith [lpNorm_add hp1.le x y])
  obtain ⟨j, r, hr, hrxz⟩ := exists_signed_coord_bound (m := (21 : ℝ)) (B := (3033/1250 : ℝ)) (E := (13/100 : ℝ)) (by norm_num) hp (by norm_num) (x + z)
    (by linarith [lpNorm_add hp1.le x z])
  obtain ⟨k, t, ht, htyz⟩ := exists_signed_coord_bound (m := (21 : ℝ)) (B := (3033/1250 : ℝ)) (E := (13/100 : ℝ)) (by norm_num) hp (by norm_num) (y + z)
    (by linarith [lpNorm_add hp1.le y z])
  simp only [Pi.add_apply, mul_add] at hsxy hrxz htyz
  have hxa (l : Fin 3) : |x l| ≤ lpNorm p x := norm_apply_le_lpNorm hp1.le x l
  have hya (l : Fin 3) : |y l| ≤ lpNorm p y := norm_apply_le_lpNorm hp1.le y l
  have hza (l : Fin 3) : |z l| ≤ lpNorm p z := norm_apply_le_lpNorm hp1.le z l
  have habs (l : Fin 3) : |x l + y l + z l| ≤ T := norm_apply_le_lpNorm hp1.le (x + y + z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    exact signed_conflict_bound (G := (11/50 : ℝ)) (E := (13/100 : ℝ)) hs hr (hxa i) (hya i) (hza i) (habs i) hsxy hrxz
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hik : i ≠ k := by
    intro heq
    subst k
    have hcol : |y i + x i + z i| ≤ T := by
      rw [show y i + x i + z i = x i + y i + z i by ring]; exact habs i
    exact signed_conflict_bound (G := (11/50 : ℝ)) (E := (13/100 : ℝ)) (P1 := lpNorm p (x + y)) hs ht (hya i) (hxa i) (hza i) hcol (by linarith) htyz
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hcol : |z j + x j + y j| ≤ T := by
      rw [show z j + x j + y j = x j + y j + z j by ring]; exact habs j
    exact signed_conflict_bound (G := (11/50 : ℝ)) (E := (13/100 : ℝ)) (P1 := lpNorm p (x + z)) (P2 := lpNorm p (y + z)) hr ht (hza j) (hxa j) (hya j) hcol (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  -- Orientation.
  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = T := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have huv : lpNorm p (u + v) = lpNorm p (x + y) := by
    dsimp [u, v]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have huw : lpNorm p (u + w) = lpNorm p (x + z) := by
    dsimp [u, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hvw : lpNorm p (v + w) = lpNorm p (y + z) := by
    dsimp [v, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hpgs : pairGapSum (lpNorm p) u v w = pairGapSum (lpNorm p) x y z := by
    simp only [pairGapSum, pairGap, hu, hv, hw, huv, huw, hvw]
  have e0 : v 0 + w 0 = t * y k + t * z k := by simp [v, w, orient, e, f, signs]
  have e1 : u 1 + w 1 = r * x j + r * z j := by simp [u, w, orient, e, f, signs]
  have e2 : u 2 + v 2 = s * x i + s * y i := by simp [u, v, orient, e, f, signs]
  let X : Triple := ![u, v, w]
  have hNX : ∀ l, lpNorm p (X l) ≤ T := by
    intro l
    fin_cases l
    · change lpNorm p u ≤ T
      rw [hu]; exact hxT
    · change lpNorm p v ≤ T
      rw [hv]; exact hyT
    · change lpNorm p w ≤ T
      rw [hw]; exact hzT
  have hlin : T - (5733/625 : ℝ) * (lpNorm p (v + w) + lpNorm p (u + w) + lpNorm p (u + v)) ≤
      3 - 6 * (5733/625 : ℝ) := by
    rw [← hpgs] at hG
    dsimp only [pairGapSum, pairGap] at hG
    rw [hu, hv, hw] at hG
    linarith
  have hbox := coarse_box21_oriented p hp X (fun l ↦ lpNorm p (X l))
    ![lpNorm p (v + w), lpNorm p (u + w), lpNorm p (u + v)] T
    (fun _ ↦ rfl) rfl rfl rfl (by change T = lpNorm p (u + v + w); exact hsumNorm.symm)
    (by change lpNorm p u + lpNorm p v + lpNorm p w = 3; rw [hu, hv, hw]; exact hS)
    hNX hTone hT.le
    (by change lpNorm p (v + w) - (v 0 + w 0) ≤ (13/100 : ℝ); rw [hvw, e0]; linarith)
    (by change lpNorm p (u + w) - (u 1 + w 1) ≤ (13/100 : ℝ); rw [huw, e1]; linarith)
    (by change lpNorm p (u + v) - (u 2 + v 2) ≤ (13/100 : ℝ); rw [huv, e2]; linarith)
    hlin
  refine ⟨![u, v, w], hbox, ?_, ?_, ?_, ?_⟩
  · change lpNorm p u + lpNorm p v + lpNorm p w = 3
    rw [hu, hv, hw]; exact hS
  · change lpNorm p (u + v + w) < 3 * q
    rw [hsumNorm]; exact hTq
  · change pairGapSum (lpNorm p) u v w < 2 / ((273/625) * p)
    rw [hpgs]; exact hGp
  · change hlawkaDeficit p K u v w < 0
    dsimp [u, v, w]
    rwa [hlawkaDeficit_orient p K e signs x y z hsigns]

end HlawkaSchatten.DiagonalCutoff21
