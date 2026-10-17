import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 2, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab002 (p : ℝ) (hpa : (209/8 : ℝ) ≤ p) (hpb : p ≤ (419/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (90920745037/5786687500000 : ℝ) (8067253/1000000000 : ℝ) (1600000277761/9258700000000 : ℝ) (591/500 : ℝ) (973878597/500000000 : ℝ) (97381693/100000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1155430913/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10793/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5467/10000 : ℝ)
      else (203/250 : ℝ) ≤ X j i ∧ X j i ≤ (5733/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (90920745037/5786687500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (8067253/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (933556569/1000000000 : ℝ) ^ p + (198625577/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (933556569/1000000000 : ℝ)) (y := (198625577/200000000 : ℝ)) (X := (16521823928443/100000000000000 : ℝ)) (Y := (652173399583/781250000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198625577/200000000 : ℝ) ^ p + (933556569/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198625577/200000000 : ℝ)) (y := (933556569/1000000000 : ℝ)) (X := (652173399583/781250000000 : ℝ)) (Y := (16521823928443/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (963342227/500000000 : ℝ)) (τ := (933556569/1000000000 : ℝ)) (σ := (198625577/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (203407987/215583501 : ℝ) ^ p + (854266751/862334004 : ℝ) ^ p := by
    exact cert_lt (x := (203407987/215583501 : ℝ)) (y := (854266751/862334004 : ℝ)) (X := (10909393637791/50000000000000 : ℝ)) (Y := (78181213648767/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (933556569/1000000000 : ℝ)) (n' := (215583501/250000000 : ℝ)) (Ab := (203407987/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (187413797/200000000 : ℝ) ^ p + (496172247/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (187413797/200000000 : ℝ)) (y := (496172247/500000000 : ℝ)) (X := (9114604607837/50000000000000 : ℝ)) (Y := (2555337728531/3125000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496172247/500000000 : ℝ) ^ p + (187413797/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496172247/500000000 : ℝ)) (y := (187413797/200000000 : ℝ)) (X := (2555337728531/3125000000000 : ℝ)) (Y := (9114604607837/50000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1929413479/1000000000 : ℝ)) (τ := (187413797/200000000 : ℝ)) (σ := (496172247/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (817334237/866395694 : ℝ) ^ p + (858328441/866395694 : ℝ) ^ p := by
    exact cert_lt (x := (817334237/866395694 : ℝ)) (y := (858328441/866395694 : ℝ)) (X := (1086404866051/5000000000000 : ℝ)) (Y := (9783988004779/12500000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (187413797/200000000 : ℝ)) (n' := (433197847/500000000 : ℝ)) (Ab := (817334237/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (14643451/15625000 : ℝ) ^ p + (992318033/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14643451/15625000 : ℝ)) (y := (992318033/1000000000 : ℝ)) (X := (18286290274979/100000000000000 : ℝ)) (Y := (10214215810383/12500000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992318033/1000000000 : ℝ) ^ p + (14643451/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (992318033/1000000000 : ℝ)) (y := (14643451/15625000 : ℝ)) (X := (10214215810383/12500000000000 : ℝ)) (Y := (18286290274979/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1929498897/1000000000 : ℝ)) (τ := (14643451/15625000 : ℝ)) (σ := (992318033/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (817451927/866524821 : ℝ) ^ p + (858457568/866524821 : ℝ) ^ p := by
    exact cert_lt (x := (817451927/866524821 : ℝ)) (y := (858457568/866524821 : ℝ)) (X := (21725226284253/100000000000000 : ℝ)) (Y := (19568693730859/25000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (14643451/15625000 : ℝ)) (n' := (866524821/1000000000 : ℝ)) (Ab := (817451927/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (187436881/200000000 : ℝ) ^ p + (496158597/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (187436881/200000000 : ℝ)) (y := (496158597/500000000 : ℝ)) (X := (731523988373/4000000000000 : ℝ)) (Y := (4085595862293/5000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496158597/500000000 : ℝ) ^ p + (187436881/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496158597/500000000 : ℝ)) (y := (187436881/200000000 : ℝ)) (X := (4085595862293/5000000000000 : ℝ)) (Y := (731523988373/4000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1929501599/1000000000 : ℝ)) (τ := (187436881/200000000 : ℝ)) (σ := (496158597/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (204363913/216632227 : ℝ) ^ p + (858461655/866528908 : ℝ) ^ p := by
    exact cert_lt (x := (204363913/216632227 : ℝ)) (y := (858461655/866528908 : ℝ)) (X := (10862567713909/50000000000000 : ℝ)) (Y := (78274865777537/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (187436881/200000000 : ℝ)) (n' := (216632227/250000000 : ℝ)) (Ab := (204363913/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (468592259/500000000 : ℝ) ^ p + (992317167/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468592259/500000000 : ℝ)) (y := (992317167/1000000000 : ℝ)) (X := (18288157454629/100000000000000 : ℝ)) (Y := (40855929511567/50000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992317167/1000000000 : ℝ) ^ p + (468592259/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992317167/1000000000 : ℝ)) (y := (468592259/500000000 : ℝ)) (X := (40855929511567/50000000000000 : ℝ)) (Y := (18288157454629/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (385900337/200000000 : ℝ)) (τ := (468592259/500000000 : ℝ)) (σ := (992317167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (408727885/433264519 : ℝ) ^ p + (858461785/866529038 : ℝ) ^ p := by
    exact cert_lt (x := (408727885/433264519 : ℝ)) (y := (858461785/866529038 : ℝ)) (X := (10862566100003/50000000000000 : ℝ)) (Y := (19568717166857/25000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (468592259/500000000 : ℝ)) (n' := (433264519/500000000 : ℝ)) (Ab := (81745577/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (23429613/25000000 : ℝ) ^ p + (992317167/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23429613/25000000 : ℝ)) (y := (992317167/1000000000 : ℝ)) (X := (18288158476671/100000000000000 : ℝ)) (Y := (40855929511567/50000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992317167/1000000000 : ℝ) ^ p + (23429613/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (992317167/1000000000 : ℝ)) (y := (23429613/25000000 : ℝ)) (X := (40855929511567/50000000000000 : ℝ)) (Y := (18288158476671/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1929501687/1000000000 : ℝ)) (τ := (23429613/25000000 : ℝ)) (σ := (992317167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (817455773/866529041 : ℝ) ^ p + (858461788/866529041 : ℝ) ^ p := by
    exact cert_lt (x := (817455773/866529041 : ℝ)) (y := (858461788/866529041 : ℝ)) (X := (21725132318249/100000000000000 : ℝ)) (Y := (78274868734117/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (23429613/25000000 : ℝ)) (n' := (866529041/1000000000 : ℝ)) (Ab := (817455773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1929501687/1000000000 : ℝ)) (τ := (23429613/25000000 : ℝ)) (σ := (992317167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (23429613/25000000 : ℝ)) (n' := (866529041/1000000000 : ℝ)) (Ab := (817455773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1929501687/1000000000 : ℝ)) (τ := (23429613/25000000 : ℝ)) (σ := (992317167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (23429613/25000000 : ℝ)) (n' := (866529041/1000000000 : ℝ)) (Ab := (817455773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1929501687/1000000000 : ℝ)) (τ := (23429613/25000000 : ℝ)) (σ := (992317167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (23429613/25000000 : ℝ)) (n' := (866529041/1000000000 : ℝ)) (Ab := (817455773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1929501687/1000000000 : ℝ)) (τ := (23429613/25000000 : ℝ)) (σ := (992317167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (23429613/25000000 : ℝ)) (n' := (866529041/1000000000 : ℝ)) (Ab := (817455773/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1929501687/1000000000 : ℝ)) (τ := (23429613/25000000 : ℝ)) (σ := (992317167/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1694542771/1844569087 : ℝ) ^ p + (1836501834/1844569087 : ℝ) ^ p := by
    exact cert_lt (x := (1694542771/1844569087 : ℝ)) (y := (1836501834/1844569087 : ℝ)) (X := (10844009434907/100000000000000 : ℝ)) (Y := (89155990892371/100000000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (154179746/165061559 : ℝ) ^ p + (1147363660/1155430913 : ℝ) ^ p := by
    exact cert_lt (x := (154179746/165061559 : ℝ)) (y := (1147363660/1155430913 : ℝ)) (X := (16763414048551/100000000000000 : ℝ)) (Y := (10404573299959/12500000000000 : ℝ)) 419 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992317167/1000000000 : ℝ)) (U := (1155430913/1000000000 : ℝ)) (Ab := (1694542771/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (23429613/25000000 : ℝ)) (σ := (992317167/1000000000 : ℝ)) (Ab := (539629111/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab002
