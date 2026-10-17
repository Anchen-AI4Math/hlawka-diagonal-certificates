import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 42, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab042 (p : ℝ) (hpa : (229/8 : ℝ) ≤ p) (hpb : p ≤ (459/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (359485435981/25361750000000 : ℝ) (3630433/500000000 : ℝ) (1600000304341/10144700000000 : ℝ) (591/500 : ℝ) (976127571/500000000 : ℝ) (244019019/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (578508079/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10867/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5559/10000 : ℝ)
      else (1643/2000 : ℝ) ≤ X j i ∧ X j i ≤ (718/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (359485435981/25361750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3630433/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (469812441/500000000 : ℝ) ^ p + (993628183/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469812441/500000000 : ℝ)) (y := (993628183/1000000000 : ℝ)) (X := (1675453845977/10000000000000 : ℝ)) (Y := (20811370209159/25000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993628183/1000000000 : ℝ) ^ p + (469812441/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993628183/1000000000 : ℝ)) (y := (469812441/500000000 : ℝ)) (X := (20811370209159/25000000000000 : ℝ)) (Y := (1675453845977/10000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (386650613/200000000 : ℝ)) (τ := (469812441/500000000 : ℝ)) (σ := (993628183/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (821948071/867289070 : ℝ) ^ p + (430014102/433644535 : ℝ) ^ p := by
    exact cert_lt (x := (821948071/867289070 : ℝ)) (y := (430014102/433644535 : ℝ)) (X := (10714997116389/50000000000000 : ℝ)) (Y := (78570006920603/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (469812441/500000000 : ℝ)) (n' := (86728907/100000000 : ℝ)) (Ab := (821948071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (942926361/1000000000 : ℝ) ^ p + (992882549/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942926361/1000000000 : ℝ)) (y := (992882549/1000000000 : ℝ)) (X := (1158007183723/6250000000000 : ℝ)) (Y := (81471903366989/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992882549/1000000000 : ℝ) ^ p + (942926361/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992882549/1000000000 : ℝ)) (y := (942926361/1000000000 : ℝ)) (X := (81471903366989/100000000000000 : ℝ)) (Y := (1158007183723/6250000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (193580891/100000000 : ℝ)) (τ := (942926361/1000000000 : ℝ)) (σ := (992882549/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (75038370/79188371 : ℝ) ^ p + (863811215/871072081 : ℝ) ^ p := by
    exact cert_lt (x := (75038370/79188371 : ℝ)) (y := (863811215/871072081 : ℝ)) (X := (5336827096183/25000000000000 : ℝ)) (Y := (7865269238913/10000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (942926361/1000000000 : ℝ)) (n' := (871072081/1000000000 : ℝ)) (Ab := (82542207/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (188603947/200000000 : ℝ) ^ p + (124107519/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (188603947/200000000 : ℝ)) (y := (124107519/125000000 : ℝ)) (X := (4645205464059/25000000000000 : ℝ)) (Y := (16283839549509/20000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124107519/125000000 : ℝ) ^ p + (188603947/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (124107519/125000000 : ℝ)) (y := (188603947/200000000 : ℝ)) (X := (16283839549509/20000000000000 : ℝ)) (Y := (4645205464059/25000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1935879887/1000000000 : ℝ)) (τ := (188603947/200000000 : ℝ)) (σ := (124107519/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (825520141/871178883 : ℝ) ^ p + (863918017/871178883 : ℝ) ^ p := by
    exact cert_lt (x := (825520141/871178883 : ℝ)) (y := (863918017/871178883 : ℝ)) (X := (2134498370431/10000000000000 : ℝ)) (Y := (39327508777987/50000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (188603947/200000000 : ℝ)) (n' := (871178883/1000000000 : ℝ)) (Ab := (825520141/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (943022361/1000000000 : ℝ) ^ p + (992859521/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (943022361/1000000000 : ℝ)) (y := (992859521/1000000000 : ℝ)) (X := (1858230624721/10000000000000 : ℝ)) (Y := (81417713326923/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992859521/1000000000 : ℝ) ^ p + (943022361/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992859521/1000000000 : ℝ)) (y := (943022361/1000000000 : ℝ)) (X := (81417713326923/100000000000000 : ℝ)) (Y := (1858230624721/10000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (967940941/500000000 : ℝ)) (τ := (943022361/1000000000 : ℝ)) (σ := (992859521/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (412761449/435590943 : ℝ) ^ p + (431960510/435590943 : ℝ) ^ p := by
    exact cert_lt (x := (412761449/435590943 : ℝ)) (y := (431960510/435590943 : ℝ)) (X := (5336229494067/25000000000000 : ℝ)) (Y := (78655082926457/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (943022361/1000000000 : ℝ)) (n' := (435590943/500000000 : ℝ)) (Ab := (412761449/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (188604487/200000000 : ℝ) ^ p + (992859503/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188604487/200000000 : ℝ)) (y := (992859503/1000000000 : ℝ)) (X := (18582348078621/100000000000000 : ℝ)) (Y := (40708835491251/50000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992859503/1000000000 : ℝ) ^ p + (188604487/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992859503/1000000000 : ℝ)) (y := (188604487/200000000 : ℝ)) (X := (40708835491251/50000000000000 : ℝ)) (Y := (18582348078621/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (967940969/500000000 : ℝ)) (τ := (188604487/200000000 : ℝ)) (σ := (992859503/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (825522976/871181971 : ℝ) ^ p + (863921105/871181971 : ℝ) ^ p := by
    exact cert_lt (x := (825522976/871181971 : ℝ)) (y := (863921105/871181971 : ℝ)) (X := (10672458044213/50000000000000 : ℝ)) (Y := (15731016955353/20000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (188604487/200000000 : ℝ)) (n' := (871181971/1000000000 : ℝ)) (Ab := (25797593/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (471511219/500000000 : ℝ) ^ p + (496429751/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (471511219/500000000 : ℝ)) (y := (496429751/500000000 : ℝ)) (X := (18582349774491/100000000000000 : ℝ)) (Y := (16283533726007/20000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496429751/500000000 : ℝ) ^ p + (471511219/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496429751/500000000 : ℝ)) (y := (471511219/500000000 : ℝ)) (X := (16283533726007/20000000000000 : ℝ)) (Y := (18582349774491/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (96794097/50000000 : ℝ)) (τ := (471511219/500000000 : ℝ)) (σ := (496429751/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (825522979/871181974 : ℝ) ^ p + (431960554/435590987 : ℝ) ^ p := by
    exact cert_lt (x := (825522979/871181974 : ℝ)) (y := (431960554/435590987 : ℝ)) (X := (21344916205053/100000000000000 : ℝ)) (Y := (7865508484207/10000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (471511219/500000000 : ℝ)) (n' := (435590987/500000000 : ℝ)) (Ab := (825522979/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (96794097/50000000 : ℝ)) (τ := (471511219/500000000 : ℝ)) (σ := (496429751/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (471511219/500000000 : ℝ)) (n' := (435590987/500000000 : ℝ)) (Ab := (825522979/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (96794097/50000000 : ℝ)) (τ := (471511219/500000000 : ℝ)) (σ := (496429751/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (471511219/500000000 : ℝ)) (n' := (435590987/500000000 : ℝ)) (Ab := (825522979/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (96794097/50000000 : ℝ)) (τ := (471511219/500000000 : ℝ)) (σ := (496429751/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (471511219/500000000 : ℝ)) (n' := (435590987/500000000 : ℝ)) (Ab := (825522979/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (96794097/50000000 : ℝ)) (τ := (471511219/500000000 : ℝ)) (σ := (496429751/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (471511219/500000000 : ℝ)) (n' := (435590987/500000000 : ℝ)) (Ab := (825522979/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (96794097/50000000 : ℝ)) (τ := (471511219/500000000 : ℝ)) (σ := (496429751/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (852446181/921491921 : ℝ) ^ p + (917861488/921491921 : ℝ) ^ p := by
    exact cert_lt (x := (852446181/921491921 : ℝ)) (y := (917861488/921491921 : ℝ)) (X := (10706754934149/100000000000000 : ℝ)) (Y := (89293245384121/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (543316672/578508079 : ℝ) ^ p + (574877646/578508079 : ℝ) ^ p := by
    exact cert_lt (x := (543316672/578508079 : ℝ)) (y := (574877646/578508079 : ℝ)) (X := (32270980703/195312500000 : ℝ)) (Y := (83477258725747/100000000000000 : ℝ)) 459 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496429751/500000000 : ℝ)) (U := (578508079/500000000 : ℝ)) (Ab := (852446181/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (471511219/500000000 : ℝ)) (σ := (496429751/500000000 : ℝ)) (Ab := (8489323/7812500 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab042
