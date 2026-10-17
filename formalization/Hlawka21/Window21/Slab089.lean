import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 89, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab089 (p : ℝ) (hpa : (761/32 : ℝ) ≤ p) (hpb : p ≤ (381/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2096189044697/103876500000000 : ℝ) (2597057/250000000 : ℝ) (4000000623259/20775300000000 : ℝ) (3033/2500 : ℝ) (97131103/50000000 : ℝ) (971273877/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596752037/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5563/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4589/10000 : ℝ)
      else (7739/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2096189044697/103876500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2597057/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (459891659/500000000 : ℝ) ^ p + (198770759/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (459891659/500000000 : ℝ)) (y := (198770759/200000000 : ℝ)) (X := (853378439441/6250000000000 : ℝ)) (Y := (86345963649463/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198770759/200000000 : ℝ) ^ p + (459891659/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198770759/200000000 : ℝ)) (y := (459891659/500000000 : ℝ)) (X := (86345963649463/100000000000000 : ℝ)) (Y := (853378439441/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913637113/1000000000 : ℝ)) (τ := (459891659/500000000 : ℝ)) (σ := (198770759/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783487871/829175617 : ℝ) ^ p + (818787389/829175617 : ℝ) ^ p := by
    exact cert_lt (x := (783487871/829175617 : ℝ)) (y := (818787389/829175617 : ℝ)) (X := (25934226034901/100000000000000 : ℝ)) (Y := (74065774936419/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459891659/500000000 : ℝ)) (n' := (829175617/1000000000 : ℝ)) (Ab := (783487871/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (9253987/10000000 : ℝ) ^ p + (992812077/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (9253987/10000000 : ℝ)) (y := (992812077/1000000000 : ℝ)) (X := (15783618517049/100000000000000 : ℝ)) (Y := (10527049768729/12500000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992812077/1000000000 : ℝ) ^ p + (9253987/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (992812077/1000000000 : ℝ)) (y := (9253987/10000000 : ℝ)) (X := (10527049768729/12500000000000 : ℝ)) (Y := (15783618517049/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918210777/1000000000 : ℝ)) (τ := (9253987/10000000 : ℝ)) (σ := (992812077/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (789533446/835815385 : ℝ) ^ p + (825427157/835815385 : ℝ) ^ p := by
    exact cert_lt (x := (789533446/835815385 : ℝ)) (y := (825427157/835815385 : ℝ)) (X := (25756261529853/100000000000000 : ℝ)) (Y := (37121870007393/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (9253987/10000000 : ℝ)) (n' := (167163077/200000000 : ℝ)) (Ab := (394766723/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925640909/1000000000 : ℝ) ^ p + (992763203/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925640909/1000000000 : ℝ)) (y := (992763203/1000000000 : ℝ)) (X := (15882285089141/100000000000000 : ℝ)) (Y := (10514716486709/12500000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992763203/1000000000 : ℝ) ^ p + (925640909/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992763203/1000000000 : ℝ)) (y := (925640909/1000000000 : ℝ)) (X := (10514716486709/12500000000000 : ℝ)) (Y := (15882285089141/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (119900257/62500000 : ℝ)) (τ := (925640909/1000000000 : ℝ)) (σ := (992763203/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (157958671/167220178 : ℝ) ^ p + (412856331/418050445 : ℝ) ^ p := by
    exact cert_lt (x := (157958671/167220178 : ℝ)) (y := (412856331/418050445 : ℝ)) (X := (2574866281403/10000000000000 : ℝ)) (Y := (37125669047509/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925640909/1000000000 : ℝ)) (n' := (83610089/100000000 : ℝ)) (Ab := (157958671/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (925651247/1000000000 : ℝ) ^ p + (992761109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925651247/1000000000 : ℝ)) (y := (992761109/1000000000 : ℝ)) (X := (127092076089/800000000000 : ℝ)) (Y := (5257094189129/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992761109/1000000000 : ℝ) ^ p + (925651247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992761109/1000000000 : ℝ)) (y := (925651247/1000000000 : ℝ)) (X := (5257094189129/6250000000000 : ℝ)) (Y := (127092076089/800000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (479603089/250000000 : ℝ)) (τ := (925651247/1000000000 : ℝ)) (σ := (992761109/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (789804448/836113075 : ℝ) ^ p + (825724847/836113075 : ℝ) ^ p := by
    exact cert_lt (x := (789804448/836113075 : ℝ)) (y := (825724847/836113075 : ℝ)) (X := (25748338988351/100000000000000 : ℝ)) (Y := (7425166227279/10000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (925651247/1000000000 : ℝ)) (n' := (33444523/40000000 : ℝ)) (Ab := (24681389/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (115706461/125000000 : ℝ) ^ p + (49638051/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (115706461/125000000 : ℝ)) (y := (49638051/50000000 : ℝ)) (X := (15886689741107/100000000000000 : ℝ)) (Y := (42056663731803/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (49638051/50000000 : ℝ) ^ p + (115706461/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (49638051/50000000 : ℝ)) (y := (115706461/125000000 : ℝ)) (X := (42056663731803/50000000000000 : ℝ)) (Y := (15886689741107/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479603177/250000000 : ℝ)) (τ := (115706461/125000000 : ℝ)) (σ := (49638051/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789804921/836113595 : ℝ) ^ p + (825725367/836113595 : ℝ) ^ p := by
    exact cert_lt (x := (789804921/836113595 : ℝ)) (y := (825725367/836113595 : ℝ)) (X := (12874162429969/50000000000000 : ℝ)) (Y := (9281459513379/12500000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (115706461/125000000 : ℝ)) (n' := (167222719/200000000 : ℝ)) (Ab := (789804921/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925651707/1000000000 : ℝ) ^ p + (124095127/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (925651707/1000000000 : ℝ)) (y := (124095127/125000000 : ℝ)) (X := (15886697506161/100000000000000 : ℝ)) (Y := (5257082462087/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124095127/125000000 : ℝ) ^ p + (925651707/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124095127/125000000 : ℝ)) (y := (925651707/1000000000 : ℝ)) (X := (5257082462087/6250000000000 : ℝ)) (Y := (15886697506161/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918412723/1000000000 : ℝ)) (τ := (925651707/1000000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789804941/836113617 : ℝ) ^ p + (825725389/836113617 : ℝ) ^ p := by
    exact cert_lt (x := (789804941/836113617 : ℝ)) (y := (825725389/836113617 : ℝ)) (X := (25748324253241/100000000000000 : ℝ)) (Y := (74251676692327/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925651707/1000000000 : ℝ)) (n' := (836113617/1000000000 : ℝ)) (Ab := (789804941/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (231412927/250000000 : ℝ) ^ p + (124095127/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (231412927/250000000 : ℝ)) (y := (124095127/125000000 : ℝ)) (X := (15886697914849/100000000000000 : ℝ)) (Y := (5257082462087/6250000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124095127/125000000 : ℝ) ^ p + (231412927/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124095127/125000000 : ℝ)) (y := (231412927/250000000 : ℝ)) (X := (5257082462087/6250000000000 : ℝ)) (Y := (15886697914849/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (394902471/418056809 : ℝ) ^ p + (412862695/418056809 : ℝ) ^ p := by
    exact cert_lt (x := (394902471/418056809 : ℝ)) (y := (412862695/418056809 : ℝ)) (X := (25748324296237/100000000000000 : ℝ)) (Y := (74251676718931/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (n' := (418056809/500000000 : ℝ)) (Ab := (394902471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (479603181/250000000 : ℝ)) (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657255641/1806495926 : ℝ) ^ p + (898053849/903247963 : ℝ) ^ p := by
    exact cert_lt (x := (1657255641/1806495926 : ℝ)) (y := (898053849/903247963 : ℝ)) (X := (12831631227299/100000000000000 : ℝ)) (Y := (43584184555863/50000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (556295708/596752037 : ℝ) ^ p + (591557923/596752037 : ℝ) ^ p := by
    exact cert_lt (x := (556295708/596752037 : ℝ)) (y := (591557923/596752037 : ℝ)) (X := (4698288969443/25000000000000 : ℝ)) (Y := (81206844685171/100000000000000 : ℝ)) 381 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124095127/125000000 : ℝ)) (U := (596752037/500000000 : ℝ)) (Ab := (1657255641/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231412927/250000000 : ℝ)) (σ := (124095127/125000000 : ℝ)) (Ab := (139073927/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab089
