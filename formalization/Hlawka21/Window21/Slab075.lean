import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 75, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab075 (p : ℝ) (hpa : (747/32 : ℝ) ≤ p) (hpb : p ≤ (187/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2101054235573/101965500000000 : ℝ) (10613279/1000000000 : ℝ) (4000000611793/20393100000000 : ℝ) (3033/2500 : ℝ) (121347749/62500000 : ℝ) (194148691/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193326069/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11111/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1141/2500 : ℝ)
      else (3857/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5923/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2101054235573/101965500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10613279/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (459101329/500000000 : ℝ) ^ p + (49688171/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (459101329/500000000 : ℝ)) (y := (49688171/50000000 : ℝ)) (X := (13604685414399/100000000000000 : ℝ)) (Y := (86395331870407/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (49688171/50000000 : ℝ) ^ p + (459101329/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (49688171/50000000 : ℝ)) (y := (459101329/500000000 : ℝ)) (X := (86395331870407/100000000000000 : ℝ)) (Y := (13604685414399/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (955983039/500000000 : ℝ)) (τ := (459101329/500000000 : ℝ)) (σ := (49688171/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (781406915/827704941 : ℝ) ^ p + (817091662/827704941 : ℝ) ^ p := by
    exact cert_lt (x := (781406915/827704941 : ℝ)) (y := (817091662/827704941 : ℝ)) (X := (26041427928439/100000000000000 : ℝ)) (Y := (36979286703243/50000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459101329/500000000 : ℝ)) (n' := (827704941/1000000000 : ℝ)) (Ab := (156281383/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (184775643/200000000 : ℝ) ^ p + (198542781/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (184775643/200000000 : ℝ)) (y := (198542781/200000000 : ℝ)) (X := (3142492354001/20000000000000 : ℝ)) (Y := (16857511033463/20000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198542781/200000000 : ℝ) ^ p + (184775643/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198542781/200000000 : ℝ)) (y := (184775643/200000000 : ℝ)) (X := (16857511033463/20000000000000 : ℝ)) (Y := (3142492354001/20000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (47914803/25000000 : ℝ)) (τ := (184775643/200000000 : ℝ)) (σ := (198542781/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (131253607/139071869 : ℝ) ^ p + (823817935/834431214 : ℝ) ^ p := by
    exact cert_lt (x := (131253607/139071869 : ℝ)) (y := (823817935/834431214 : ℝ)) (X := (25860205399183/100000000000000 : ℝ)) (Y := (74139795731861/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (184775643/200000000 : ℝ)) (n' := (417215607/500000000 : ℝ)) (Ab := (393760821/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (924129381/1000000000 : ℝ) ^ p + (992663413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924129381/1000000000 : ℝ)) (y := (992663413/1000000000 : ℝ)) (X := (15812614641661/100000000000000 : ℝ)) (Y := (16837480319223/20000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992663413/1000000000 : ℝ) ^ p + (924129381/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992663413/1000000000 : ℝ)) (y := (924129381/1000000000 : ℝ)) (X := (16837480319223/20000000000000 : ℝ)) (Y := (15812614641661/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (958396397/500000000 : ℝ)) (τ := (924129381/1000000000 : ℝ)) (σ := (992663413/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (787791343/834727942 : ℝ) ^ p + (824114663/834727942 : ℝ) ^ p := by
    exact cert_lt (x := (787791343/834727942 : ℝ)) (y := (824114663/834727942 : ℝ)) (X := (25852268269813/100000000000000 : ℝ)) (Y := (74147732746333/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (924129381/1000000000 : ℝ)) (n' := (417363971/500000000 : ℝ)) (Ab := (787791343/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (924140379/1000000000 : ℝ) ^ p + (496330597/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924140379/1000000000 : ℝ)) (y := (496330597/500000000 : ℝ)) (X := (7908507023957/50000000000000 : ℝ)) (Y := (84183002705619/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496330597/500000000 : ℝ) ^ p + (924140379/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496330597/500000000 : ℝ)) (y := (924140379/1000000000 : ℝ)) (X := (84183002705619/100000000000000 : ℝ)) (Y := (7908507023957/50000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1916801573/1000000000 : ℝ)) (τ := (924140379/1000000000 : ℝ)) (σ := (496330597/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (393901576/417370467 : ℝ) ^ p + (824127655/834740934 : ℝ) ^ p := by
    exact cert_lt (x := (393901576/417370467 : ℝ)) (y := (824127655/834740934 : ℝ)) (X := (25851921203993/100000000000000 : ℝ)) (Y := (74148080151849/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (924140379/1000000000 : ℝ)) (n' := (417370467/500000000 : ℝ)) (Ab := (49237697/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (46207043/50000000 : ℝ) ^ p + (992661097/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46207043/50000000 : ℝ)) (y := (992661097/1000000000 : ℝ)) (X := (7908603241837/50000000000000 : ℝ)) (Y := (84182810420247/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992661097/1000000000 : ℝ) ^ p + (46207043/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992661097/1000000000 : ℝ)) (y := (46207043/50000000 : ℝ)) (X := (84182810420247/100000000000000 : ℝ)) (Y := (7908603241837/50000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1916801957/1000000000 : ℝ)) (τ := (46207043/50000000 : ℝ)) (σ := (992661097/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (393901834/417370751 : ℝ) ^ p + (824128223/834741502 : ℝ) ^ p := by
    exact cert_lt (x := (393901834/417370751 : ℝ)) (y := (824128223/834741502 : ℝ)) (X := (2585190581599/10000000000000 : ℝ)) (Y := (74148095339933/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (46207043/50000000 : ℝ)) (n' := (417370751/500000000 : ℝ)) (Ab := (196950917/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924140881/1000000000 : ℝ) ^ p + (992661093/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924140881/1000000000 : ℝ)) (y := (992661093/1000000000 : ℝ)) (X := (7908607442643/50000000000000 : ℝ)) (Y := (42091401245481/50000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992661093/1000000000 : ℝ) ^ p + (924140881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992661093/1000000000 : ℝ)) (y := (924140881/1000000000 : ℝ)) (X := (42091401245481/50000000000000 : ℝ)) (Y := (7908607442643/50000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (958400987/500000000 : ℝ)) (τ := (924140881/1000000000 : ℝ)) (σ := (992661093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (787803691/834741527 : ℝ) ^ p + (824128248/834741527 : ℝ) ^ p := by
    exact cert_lt (x := (787803691/834741527 : ℝ)) (y := (824128248/834741527 : ℝ)) (X := (1034076214407/4000000000000 : ℝ)) (Y := (37074048004211/50000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924140881/1000000000 : ℝ)) (n' := (834741527/1000000000 : ℝ)) (Ab := (787803691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (958400987/500000000 : ℝ)) (τ := (924140881/1000000000 : ℝ)) (σ := (992661093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (924140881/1000000000 : ℝ)) (n' := (834741527/1000000000 : ℝ)) (Ab := (787803691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (958400987/500000000 : ℝ)) (τ := (924140881/1000000000 : ℝ)) (σ := (992661093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (924140881/1000000000 : ℝ)) (n' := (834741527/1000000000 : ℝ)) (Ab := (787803691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (958400987/500000000 : ℝ)) (τ := (924140881/1000000000 : ℝ)) (σ := (992661093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (924140881/1000000000 : ℝ)) (n' := (834741527/1000000000 : ℝ)) (Ab := (787803691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (958400987/500000000 : ℝ)) (τ := (924140881/1000000000 : ℝ)) (σ := (992661093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (924140881/1000000000 : ℝ)) (n' := (834741527/1000000000 : ℝ)) (Ab := (787803691/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (958400987/500000000 : ℝ)) (τ := (924140881/1000000000 : ℝ)) (σ := (992661093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1654934664/1806673931 : ℝ) ^ p + (1796060652/1806673931 : ℝ) ^ p := by
    exact cert_lt (x := (1654934664/1806673931 : ℝ)) (y := (1796060652/1806673931 : ℝ)) (X := (1608228053119/12500000000000 : ℝ)) (Y := (87134175757817/100000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1111098753/1193326069 : ℝ) ^ p + (1182712790/1193326069 : ℝ) ^ p := by
    exact cert_lt (x := (1111098753/1193326069 : ℝ)) (y := (1182712790/1193326069 : ℝ)) (X := (18846200646561/100000000000000 : ℝ)) (Y := (40576900050023/50000000000000 : ℝ)) 187 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992661093/1000000000 : ℝ)) (U := (1193326069/1000000000 : ℝ)) (Ab := (206866833/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (924140881/1000000000 : ℝ)) (σ := (992661093/1000000000 : ℝ)) (Ab := (1111098753/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab075
