import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 17, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab017 (p : ℝ) (hpa : (689/32 : ℝ) ≤ p) (hpb : p ≤ (345/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2123294413169/94048500000000 : ℝ) (1457201/125000000 : ℝ) (4000000564291/18809700000000 : ℝ) (3033/2500 : ℝ) (968365233/500000000 : ℝ) (968320053/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192600537/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2209/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(1111/2500 : ℝ)
      else (1899/2500 : ℝ) ≤ X j i ∧ X j i ≤ (5917/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2123294413169/94048500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1457201/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (14233353/15625000 : ℝ) ^ p + (993360829/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14233353/15625000 : ℝ)) (y := (993360829/1000000000 : ℝ)) (X := (1337958455649/10000000000000 : ℝ)) (Y := (86620432172609/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993360829/1000000000 : ℝ) ^ p + (14233353/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (993360829/1000000000 : ℝ)) (y := (14233353/15625000 : ℝ)) (X := (86620432172609/100000000000000 : ℝ)) (Y := (1337958455649/10000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1904295421/1000000000 : ℝ)) (τ := (14233353/15625000 : ℝ)) (σ := (993360829/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (385933988/410422233 : ℝ) ^ p + (404593429/410422233 : ℝ) ^ p := by
    exact cert_lt (x := (385933988/410422233 : ℝ)) (y := (404593429/410422233 : ℝ)) (X := (26539719132393/100000000000000 : ℝ)) (Y := (734602817589/1000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (14233353/15625000 : ℝ)) (n' := (410422233/500000000 : ℝ)) (Ab := (96483497/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (22921341/25000000 : ℝ) ^ p + (248070591/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (22921341/25000000 : ℝ)) (y := (248070591/250000000 : ℝ)) (X := (1923109682599/12500000000000 : ℝ)) (Y := (84615137830603/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248070591/250000000 : ℝ) ^ p + (22921341/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (248070591/250000000 : ℝ)) (y := (22921341/25000000 : ℝ)) (X := (84615137830603/100000000000000 : ℝ)) (Y := (1923109682599/12500000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (477284001/250000000 : ℝ)) (τ := (22921341/25000000 : ℝ)) (σ := (248070591/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (389133459/413966738 : ℝ) ^ p + (204068967/206983369 : ℝ) ^ p := by
    exact cert_lt (x := (389133459/413966738 : ℝ)) (y := (204068967/206983369 : ℝ)) (X := (26344081273097/100000000000000 : ℝ)) (Y := (73655919821101/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (22921341/25000000 : ℝ)) (n' := (206983369/250000000 : ℝ)) (Ab := (389133459/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (917147113/1000000000 : ℝ) ^ p + (992224389/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917147113/1000000000 : ℝ)) (y := (992224389/1000000000 : ℝ)) (X := (15491412173933/100000000000000 : ℝ)) (Y := (1690172059079/2000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992224389/1000000000 : ℝ) ^ p + (917147113/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992224389/1000000000 : ℝ)) (y := (917147113/1000000000 : ℝ)) (X := (1690172059079/2000000000000 : ℝ)) (Y := (15491412173933/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (954685751/500000000 : ℝ)) (τ := (917147113/1000000000 : ℝ)) (σ := (992224389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (778583068/828283793 : ℝ) ^ p + (816626185/828283793 : ℝ) ^ p := by
    exact cert_lt (x := (778583068/828283793 : ℝ)) (y := (816626185/828283793 : ℝ)) (X := (658362189647/2500000000000 : ℝ)) (Y := (73665513568511/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (917147113/1000000000 : ℝ)) (n' := (828283793/1000000000 : ℝ)) (Ab := (194645767/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (917161499/1000000000 : ℝ) ^ p + (31006923/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (917161499/1000000000 : ℝ)) (y := (31006923/31250000 : ℝ)) (X := (968540783439/6250000000000 : ℝ)) (Y := (84503363583941/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (31006923/31250000 : ℝ) ^ p + (917161499/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31006923/31250000 : ℝ)) (y := (917161499/1000000000 : ℝ)) (X := (84503363583941/100000000000000 : ℝ)) (Y := (968540783439/6250000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (381876607/200000000 : ℝ)) (τ := (917161499/1000000000 : ℝ)) (σ := (31006923/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (778598563/828300963 : ℝ) ^ p + (816643355/828300963 : ℝ) ^ p := by
    exact cert_lt (x := (778598563/828300963 : ℝ)) (y := (816643355/828300963 : ℝ)) (X := (6583504347253/25000000000000 : ℝ)) (Y := (73665983606467/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (917161499/1000000000 : ℝ)) (n' := (828300963/1000000000 : ℝ)) (Ab := (778598563/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (229290551/250000000 : ℝ) ^ p + (248055349/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (229290551/250000000 : ℝ)) (y := (248055349/250000000 : ℝ)) (X := (15496909387491/100000000000000 : ℝ)) (Y := (42251553244993/50000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248055349/250000000 : ℝ) ^ p + (229290551/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248055349/250000000 : ℝ)) (y := (229290551/250000000 : ℝ)) (X := (42251553244993/50000000000000 : ℝ)) (Y := (15496909387491/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (4773459/2500000 : ℝ)) (τ := (229290551/250000000 : ℝ)) (σ := (248055349/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (389299661/414150902 : ℝ) ^ p + (204161049/207075451 : ℝ) ^ p := by
    exact cert_lt (x := (389299661/414150902 : ℝ)) (y := (204161049/207075451 : ℝ)) (X := (3291749298791/12500000000000 : ℝ)) (Y := (36833003314433/50000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (229290551/250000000 : ℝ)) (n' := (207075451/250000000 : ℝ)) (Ab := (389299661/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (917162239/1000000000 : ℝ) ^ p + (992221389/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (917162239/1000000000 : ℝ)) (y := (992221389/1000000000 : ℝ)) (X := (15496922139137/100000000000000 : ℝ)) (Y := (21125773408827/25000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992221389/1000000000 : ℝ) ^ p + (917162239/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992221389/1000000000 : ℝ)) (y := (917162239/1000000000 : ℝ)) (X := (21125773408827/25000000000000 : ℝ)) (Y := (15496922139137/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477345907/250000000 : ℝ)) (τ := (917162239/1000000000 : ℝ)) (σ := (992221389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (389299680/414150923 : ℝ) ^ p + (408322119/414150923 : ℝ) ^ p := by
    exact cert_lt (x := (389299680/414150923 : ℝ)) (y := (408322119/414150923 : ℝ)) (X := (822937290973/3125000000000 : ℝ)) (Y := (9208250972327/12500000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (917162239/1000000000 : ℝ)) (n' := (414150923/500000000 : ℝ)) (Ab := (2433123/3125000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (716533/781250 : ℝ) ^ p + (992221389/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (716533/781250 : ℝ)) (y := (992221389/1000000000 : ℝ)) (X := (1549692250347/10000000000000 : ℝ)) (Y := (21125773408827/25000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992221389/1000000000 : ℝ) ^ p + (716533/781250 : ℝ) ^ p := by
    exact cert_lt (x := (992221389/1000000000 : ℝ)) (y := (716533/781250 : ℝ)) (X := (21125773408827/25000000000000 : ℝ)) (Y := (1549692250347/10000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1909383629/1000000000 : ℝ)) (τ := (716533/781250 : ℝ)) (σ := (992221389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (778599361/828301847 : ℝ) ^ p + (816644239/828301847 : ℝ) ^ p := by
    exact cert_lt (x := (778599361/828301847 : ℝ)) (y := (816644239/828301847 : ℝ)) (X := (13166996677449/50000000000000 : ℝ)) (Y := (73666007805991/100000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (716533/781250 : ℝ)) (n' := (828301847/1000000000 : ℝ)) (Ab := (778599361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1909383629/1000000000 : ℝ)) (τ := (716533/781250 : ℝ)) (σ := (992221389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (716533/781250 : ℝ)) (n' := (828301847/1000000000 : ℝ)) (Ab := (778599361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1909383629/1000000000 : ℝ)) (τ := (716533/781250 : ℝ)) (σ := (992221389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (716533/781250 : ℝ)) (n' := (828301847/1000000000 : ℝ)) (Ab := (778599361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1909383629/1000000000 : ℝ)) (τ := (716533/781250 : ℝ)) (σ := (992221389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (716533/781250 : ℝ)) (n' := (828301847/1000000000 : ℝ)) (Ab := (778599361/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1909383629/1000000000 : ℝ)) (τ := (716533/781250 : ℝ)) (σ := (992221389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1644361742/1807399463 : ℝ) ^ p + (1795741855/1807399463 : ℝ) ^ p := by
    exact cert_lt (x := (1644361742/1807399463 : ℝ)) (y := (1795741855/1807399463 : ℝ)) (X := (813941307767/6250000000000 : ℝ)) (Y := (10872117426887/12500000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1104432208/1192600537 : ℝ) ^ p + (1180942929/1192600537 : ℝ) ^ p := by
    exact cert_lt (x := (1104432208/1192600537 : ℝ)) (y := (1180942929/1192600537 : ℝ)) (X := (19088095624173/100000000000000 : ℝ)) (Y := (20227976187263/25000000000000 : ℝ)) 345 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992221389/1000000000 : ℝ)) (U := (1192600537/1000000000 : ℝ)) (Ab := (822180871/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (716533/781250 : ℝ)) (σ := (992221389/1000000000 : ℝ)) (Ab := (69027013/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab017
