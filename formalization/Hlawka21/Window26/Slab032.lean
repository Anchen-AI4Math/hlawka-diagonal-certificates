import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 32, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab032 (p : ℝ) (hpa : (28 : ℝ) ≤ p) (hpb : p ≤ (449/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2816134043/193812500000 : ℝ) (3723597/500000000 : ℝ) (50000009303/310100000000 : ℝ) (591/500 : ℝ) (97560243/50000000 : ℝ) (487774321/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231326801/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10849/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2769/5000 : ℝ)
      else (8193/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11483/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2816134043/193812500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3723597/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (469106911/500000000 : ℝ) ^ p + (124188733/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (469106911/500000000 : ℝ)) (y := (124188733/125000000 : ℝ)) (X := (3340027249779/20000000000000 : ℝ)) (Y := (41649941822061/50000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124188733/125000000 : ℝ) ^ p + (469106911/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124188733/125000000 : ℝ)) (y := (469106911/500000000 : ℝ)) (X := (41649941822061/50000000000000 : ℝ)) (Y := (3340027249779/20000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (965861843/500000000 : ℝ)) (τ := (469106911/500000000 : ℝ)) (σ := (124188733/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (820008643/866148653 : ℝ) ^ p + (858701459/866148653 : ℝ) ^ p := by
    exact cert_lt (x := (820008643/866148653 : ℝ)) (y := (858701459/866148653 : ℝ)) (X := (21519986853421/100000000000000 : ℝ)) (Y := (78480013976889/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (469106911/500000000 : ℝ)) (n' := (866148653/1000000000 : ℝ)) (Ab := (820008643/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (235391713/250000000 : ℝ) ^ p + (992754791/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (235391713/250000000 : ℝ)) (y := (992754791/1000000000 : ℝ)) (X := (9229288068169/50000000000000 : ℝ)) (Y := (81541442522851/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992754791/1000000000 : ℝ) ^ p + (235391713/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992754791/1000000000 : ℝ)) (y := (235391713/250000000 : ℝ)) (X := (81541442522851/100000000000000 : ℝ)) (Y := (9229288068169/50000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1934321643/1000000000 : ℝ)) (τ := (235391713/250000000 : ℝ)) (σ := (992754791/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (823538233/869998914 : ℝ) ^ p + (15973180/16111091 : ℝ) ^ p := by
    exact cert_lt (x := (823538233/869998914 : ℝ)) (y := (15973180/16111091 : ℝ)) (X := (21435414017967/100000000000000 : ℝ)) (Y := (78564587208137/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (235391713/250000000 : ℝ)) (n' := (434999457/500000000 : ℝ)) (Ab := (823538233/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (470832211/500000000 : ℝ) ^ p + (992731463/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470832211/500000000 : ℝ)) (y := (992731463/1000000000 : ℝ)) (X := (3702465730023/20000000000000 : ℝ)) (Y := (81487689588009/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992731463/1000000000 : ℝ) ^ p + (470832211/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992731463/1000000000 : ℝ)) (y := (470832211/500000000 : ℝ)) (X := (81487689588009/100000000000000 : ℝ)) (Y := (3702465730023/20000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (386879177/200000000 : ℝ)) (τ := (470832211/500000000 : ℝ)) (σ := (992731463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (823640745/870110749 : ℝ) ^ p + (862663555/870110749 : ℝ) ^ p := by
    exact cert_lt (x := (823640745/870110749 : ℝ)) (y := (862663555/870110749 : ℝ)) (X := (10716483534367/50000000000000 : ℝ)) (Y := (78567033850227/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (470832211/500000000 : ℝ)) (n' := (870110749/1000000000 : ℝ)) (Ab := (164728149/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (188333449/200000000 : ℝ) ^ p + (992730787/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (188333449/200000000 : ℝ)) (y := (992730787/1000000000 : ℝ)) (X := (9256943060153/50000000000000 : ℝ)) (Y := (81486132442237/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992730787/1000000000 : ℝ) ^ p + (188333449/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992730787/1000000000 : ℝ)) (y := (188333449/200000000 : ℝ)) (X := (81486132442237/100000000000000 : ℝ)) (Y := (9256943060153/50000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (120899877/62500000 : ℝ)) (τ := (188333449/200000000 : ℝ)) (σ := (992730787/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (823643711/870113985 : ℝ) ^ p + (287555597/290037995 : ℝ) ^ p := by
    exact cert_lt (x := (823643711/870113985 : ℝ)) (y := (287555597/290037995 : ℝ)) (X := (2679112013403/12500000000000 : ℝ)) (Y := (15713420927347/20000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (188333449/200000000 : ℝ)) (n' := (174022797/200000000 : ℝ)) (Ab := (823643711/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (941667327/1000000000 : ℝ) ^ p + (992730767/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (941667327/1000000000 : ℝ)) (y := (992730767/1000000000 : ℝ)) (X := (18513931362207/100000000000000 : ℝ)) (Y := (81486086373273/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992730767/1000000000 : ℝ) ^ p + (941667327/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992730767/1000000000 : ℝ)) (y := (941667327/1000000000 : ℝ)) (X := (81486086373273/100000000000000 : ℝ)) (Y := (18513931362207/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (967199047/500000000 : ℝ)) (τ := (941667327/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (823643798/870114079 : ℝ) ^ p + (862666885/870114079 : ℝ) ^ p := by
    exact cert_lt (x := (823643798/870114079 : ℝ)) (y := (862666885/870114079 : ℝ)) (X := (21432894661537/100000000000000 : ℝ)) (Y := (78567106692949/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (941667327/1000000000 : ℝ)) (n' := (870114079/1000000000 : ℝ)) (Ab := (411821899/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (941667329/1000000000 : ℝ) ^ p + (992730767/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (941667329/1000000000 : ℝ)) (y := (992730767/1000000000 : ℝ)) (X := (1851393246567/10000000000000 : ℝ)) (Y := (81486086373273/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992730767/1000000000 : ℝ) ^ p + (941667329/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992730767/1000000000 : ℝ)) (y := (941667329/1000000000 : ℝ)) (X := (81486086373273/100000000000000 : ℝ)) (Y := (1851393246567/10000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (120899881/62500000 : ℝ)) (τ := (941667329/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (274547933/290038027 : ℝ) ^ p + (287555629/290038027 : ℝ) ^ p := by
    exact cert_lt (x := (274547933/290038027 : ℝ)) (y := (287555629/290038027 : ℝ)) (X := (10716447004647/50000000000000 : ℝ)) (Y := (39283553368349/50000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (941667329/1000000000 : ℝ)) (n' := (870114081/1000000000 : ℝ)) (Ab := (823643799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (120899881/62500000 : ℝ)) (τ := (941667329/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (941667329/1000000000 : ℝ)) (n' := (870114081/1000000000 : ℝ)) (Ab := (823643799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (120899881/62500000 : ℝ)) (τ := (941667329/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (941667329/1000000000 : ℝ)) (n' := (870114081/1000000000 : ℝ)) (Ab := (823643799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (120899881/62500000 : ℝ)) (τ := (941667329/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (941667329/1000000000 : ℝ)) (n' := (870114081/1000000000 : ℝ)) (Ab := (823643799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (120899881/62500000 : ℝ)) (τ := (941667329/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (941667329/1000000000 : ℝ)) (n' := (870114081/1000000000 : ℝ)) (Ab := (823643799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (120899881/62500000 : ℝ)) (τ := (941667329/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (340494238/368673199 : ℝ) ^ p + (1835918801/1843365995 : ℝ) ^ p := by
    exact cert_lt (x := (340494238/368673199 : ℝ)) (y := (1835918801/1843365995 : ℝ)) (X := (10738691144637/100000000000000 : ℝ)) (Y := (89261309120857/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1084888432/1156634005 : ℝ) ^ p + (1149186811/1156634005 : ℝ) ^ p := by
    exact cert_lt (x := (1084888432/1156634005 : ℝ)) (y := (1149186811/1156634005 : ℝ)) (X := (8289479096421/50000000000000 : ℝ)) (Y := (83421042539251/100000000000000 : ℝ)) 449 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992730767/1000000000 : ℝ)) (U := (231326801/200000000 : ℝ)) (Ab := (170247119/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (941667329/1000000000 : ℝ)) (σ := (992730767/1000000000 : ℝ)) (Ab := (67805527/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab032
