import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 53, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab053 (p : ℝ) (hpa : (469/16 : ℝ) ≤ p) (hpb : p ≤ (235/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (358455532747/25970875000000 : ℝ) (7066241/1000000000 : ℝ) (3200000623301/20776700000000 : ℝ) (591/500 : ℝ) (976679721/500000000 : ℝ) (488315291/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157425837/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2177/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2791/5000 : ℝ)
      else (4119/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5747/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (358455532747/25970875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7066241/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (941104639/1000000000 : ℝ) ^ p + (39750143/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (941104639/1000000000 : ℝ)) (y := (39750143/40000000 : ℝ)) (X := (3362356242747/20000000000000 : ℝ)) (Y := (41594119498427/50000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (39750143/40000000 : ℝ) ^ p + (941104639/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39750143/40000000 : ℝ)) (y := (941104639/1000000000 : ℝ)) (X := (41594119498427/50000000000000 : ℝ)) (Y := (3362356242747/20000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (967429107/500000000 : ℝ)) (τ := (941104639/1000000000 : ℝ)) (σ := (39750143/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (823985718/868477297 : ℝ) ^ p + (861411056/868477297 : ℝ) ^ p := by
    exact cert_lt (x := (823985718/868477297 : ℝ)) (y := (861411056/868477297 : ℝ)) (X := (21335885317301/100000000000000 : ℝ)) (Y := (3146564624173/4000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (941104639/1000000000 : ℝ)) (n' := (868477297/1000000000 : ℝ)) (Ab := (411992859/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (944350471/1000000000 : ℝ) ^ p + (198603653/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (944350471/1000000000 : ℝ)) (y := (198603653/200000000 : ℝ)) (X := (2325133000273/12500000000000 : ℝ)) (Y := (81398954898127/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198603653/200000000 : ℝ) ^ p + (944350471/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198603653/200000000 : ℝ)) (y := (944350471/1000000000 : ℝ)) (X := (81398954898127/100000000000000 : ℝ)) (Y := (2325133000273/12500000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (60542773/31250000 : ℝ)) (τ := (944350471/1000000000 : ℝ)) (σ := (198603653/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (827399835/872188258 : ℝ) ^ p + (865122017/872188258 : ℝ) ^ p := by
    exact cert_lt (x := (827399835/872188258 : ℝ)) (y := (865122017/872188258 : ℝ)) (X := (10627597263249/50000000000000 : ℝ)) (Y := (78744806356849/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (944350471/1000000000 : ℝ)) (n' := (436094129/500000000 : ℝ)) (Ab := (165479967/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (236109881/250000000 : ℝ) ^ p + (992996831/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (236109881/250000000 : ℝ)) (y := (992996831/1000000000 : ℝ)) (X := (2331582442833/12500000000000 : ℝ)) (Y := (40673679825057/50000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992996831/1000000000 : ℝ) ^ p + (236109881/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992996831/1000000000 : ℝ)) (y := (236109881/250000000 : ℝ)) (X := (40673679825057/50000000000000 : ℝ)) (Y := (2331582442833/12500000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (387487271/200000000 : ℝ)) (τ := (236109881/250000000 : ℝ)) (σ := (992996831/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (413746667/436144947 : ℝ) ^ p + (123603379/124612842 : ℝ) ^ p := by
    exact cert_lt (x := (413746667/436144947 : ℝ)) (y := (123603379/124612842 : ℝ)) (X := (10626496529649/50000000000000 : ℝ)) (Y := (78747007779663/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (236109881/250000000 : ℝ)) (n' := (436144947/500000000 : ℝ)) (Ab := (413746667/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (472220977/500000000 : ℝ) ^ p + (198599249/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (472220977/500000000 : ℝ)) (y := (198599249/200000000 : ℝ)) (X := (18654069372223/100000000000000 : ℝ)) (Y := (81345949493159/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198599249/200000000 : ℝ) ^ p + (472220977/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198599249/200000000 : ℝ)) (y := (472220977/500000000 : ℝ)) (X := (81345949493159/100000000000000 : ℝ)) (Y := (18654069372223/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1937438199/1000000000 : ℝ)) (τ := (472220977/500000000 : ℝ)) (σ := (198599249/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (827495885/872292667 : ℝ) ^ p + (865226426/872292667 : ℝ) ^ p := by
    exact cert_lt (x := (827495885/872292667 : ℝ)) (y := (865226426/872292667 : ℝ)) (X := (21252933010799/100000000000000 : ℝ)) (Y := (78747067836133/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (472220977/500000000 : ℝ)) (n' := (872292667/1000000000 : ℝ)) (Ab := (165499177/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (47222101/50000000 : ℝ) ^ p + (992996229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (47222101/50000000 : ℝ)) (y := (992996229/1000000000 : ℝ)) (X := (9327053832663/50000000000000 : ℝ)) (Y := (81345910990911/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992996229/1000000000 : ℝ) ^ p + (47222101/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992996229/1000000000 : ℝ)) (y := (47222101/50000000 : ℝ)) (X := (81345910990911/100000000000000 : ℝ)) (Y := (9327053832663/50000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1937438249/1000000000 : ℝ)) (τ := (47222101/50000000 : ℝ)) (σ := (992996229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (413747977/436146371 : ℝ) ^ p + (865226501/872292742 : ℝ) ^ p := by
    exact cert_lt (x := (413747977/436146371 : ℝ)) (y := (865226501/872292742 : ℝ)) (X := (21252931389969/100000000000000 : ℝ)) (Y := (78747069460447/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (47222101/50000000 : ℝ)) (n' := (436146371/500000000 : ℝ)) (Ab := (413747977/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (944442021/1000000000 : ℝ) ^ p + (992996229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944442021/1000000000 : ℝ)) (y := (992996229/1000000000 : ℝ)) (X := (746164329821/4000000000000 : ℝ)) (Y := (81345910990911/100000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992996229/1000000000 : ℝ) ^ p + (944442021/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992996229/1000000000 : ℝ)) (y := (944442021/1000000000 : ℝ)) (X := (81345910990911/100000000000000 : ℝ)) (Y := (746164329821/4000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (7749753/4000000 : ℝ)) (τ := (944442021/1000000000 : ℝ)) (σ := (992996229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (827495955/872292743 : ℝ) ^ p + (123603786/124613249 : ℝ) ^ p := by
    exact cert_lt (x := (827495955/872292743 : ℝ)) (y := (123603786/124613249 : ℝ)) (X := (10626465714357/50000000000000 : ℝ)) (Y := (15749413896421/20000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (944442021/1000000000 : ℝ)) (n' := (872292743/1000000000 : ℝ)) (Ab := (165499191/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (7749753/4000000 : ℝ)) (τ := (944442021/1000000000 : ℝ)) (σ := (992996229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (944442021/1000000000 : ℝ)) (n' := (872292743/1000000000 : ℝ)) (Ab := (165499191/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (7749753/4000000 : ℝ)) (τ := (944442021/1000000000 : ℝ)) (σ := (992996229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (944442021/1000000000 : ℝ)) (n' := (872292743/1000000000 : ℝ)) (Ab := (165499191/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (7749753/4000000 : ℝ)) (τ := (944442021/1000000000 : ℝ)) (σ := (992996229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (944442021/1000000000 : ℝ)) (n' := (872292743/1000000000 : ℝ)) (Ab := (165499191/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (7749753/4000000 : ℝ)) (τ := (944442021/1000000000 : ℝ)) (σ := (992996229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (944442021/1000000000 : ℝ)) (n' := (872292743/1000000000 : ℝ)) (Ab := (165499191/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (7749753/4000000 : ℝ)) (τ := (944442021/1000000000 : ℝ)) (σ := (992996229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1707441041/1842574163 : ℝ) ^ p + (1835507922/1842574163 : ℝ) ^ p := by
    exact cert_lt (x := (1707441041/1842574163 : ℝ)) (y := (1835507922/1842574163 : ℝ)) (X := (10673250685871/100000000000000 : ℝ)) (Y := (223316873753/250000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1088483124/1157425837 : ℝ) ^ p + (1150359596/1157425837 : ℝ) ^ p := by
    exact cert_lt (x := (1088483124/1157425837 : ℝ)) (y := (1150359596/1157425837 : ℝ)) (X := (4115906465257/25000000000000 : ℝ)) (Y := (20884093719043/25000000000000 : ℝ)) 235 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992996229/1000000000 : ℝ)) (U := (1157425837/1000000000 : ℝ)) (Ab := (1707441041/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (944442021/1000000000 : ℝ)) (σ := (992996229/1000000000 : ℝ)) (Ab := (272120781/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab053
