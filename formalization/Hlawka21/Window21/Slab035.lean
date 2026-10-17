import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 35, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab035 (p : ℝ) (hpa : (707/32 : ℝ) ≤ p) (hpb : p ≤ (177/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2116005870089/96505500000000 : ℝ) (2262507/200000000 : ℝ) (4000000579033/19301100000000 : ℝ) (3033/2500 : ℝ) (969156973/500000000 : ℝ) (969114027/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192822353/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5533/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1121/2500 : ℝ)
      else (1527/2000 : ℝ) ≤ X j i ∧ X j i ≤ (5919/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2116005870089/96505500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2262507/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (913324187/1000000000 : ℝ) ^ p + (993490869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (913324187/1000000000 : ℝ)) (y := (993490869/1000000000 : ℝ)) (X := (3363312531891/25000000000000 : ℝ)) (Y := (86546765894951/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993490869/1000000000 : ℝ) ^ p + (913324187/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993490869/1000000000 : ℝ)) (y := (913324187/1000000000 : ℝ)) (X := (86546765894951/100000000000000 : ℝ)) (Y := (3363312531891/25000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (119175941/62500000 : ℝ)) (τ := (913324187/1000000000 : ℝ)) (σ := (993490869/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (774998981/823117803 : ℝ) ^ p + (270601756/274372601 : ℝ) ^ p := by
    exact cert_lt (x := (774998981/823117803 : ℝ)) (y := (270601756/274372601 : ℝ)) (X := (26374904384481/100000000000000 : ℝ)) (Y := (575196067931/781250000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (913324187/1000000000 : ℝ)) (n' := (823117803/1000000000 : ℝ)) (Ab := (774998981/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (229792329/250000000 : ℝ) ^ p + (124052583/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (229792329/250000000 : ℝ)) (y := (124052583/125000000 : ℝ)) (X := (1549265462879/10000000000000 : ℝ)) (Y := (84507361375513/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124052583/125000000 : ℝ) ^ p + (229792329/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124052583/125000000 : ℝ)) (y := (229792329/250000000 : ℝ)) (X := (84507361375513/100000000000000 : ℝ)) (Y := (1549265462879/10000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (95579499/50000000 : ℝ)) (τ := (229792329/250000000 : ℝ)) (σ := (124052583/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (781310737/830094103 : ℝ) ^ p + (818781568/830094103 : ℝ) ^ p := by
    exact cert_lt (x := (781310737/830094103 : ℝ)) (y := (818781568/830094103 : ℝ)) (X := (26183895805927/100000000000000 : ℝ)) (Y := (14763221009947/20000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (229792329/250000000 : ℝ)) (n' := (830094103/1000000000 : ℝ)) (Ab := (781310737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (919448701/1000000000 : ℝ) ^ p + (31011411/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (919448701/1000000000 : ℝ)) (y := (31011411/31250000 : ℝ)) (X := (1559717756429/10000000000000 : ℝ)) (Y := (42201419132421/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31011411/31250000 : ℝ) ^ p + (919448701/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31011411/31250000 : ℝ)) (y := (919448701/1000000000 : ℝ)) (X := (42201419132421/50000000000000 : ℝ)) (Y := (1559717756429/10000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1911813853/1000000000 : ℝ)) (τ := (919448701/1000000000 : ℝ)) (σ := (31011411/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (781611383/830426469 : ℝ) ^ p + (273037978/276808823 : ℝ) ^ p := by
    exact cert_lt (x := (781611383/830426469 : ℝ)) (y := (273037978/276808823 : ℝ)) (X := (26174864347537/100000000000000 : ℝ)) (Y := (36912568349429/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (919448701/1000000000 : ℝ)) (n' := (830426469/1000000000 : ℝ)) (Ab := (781611383/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (229865477/250000000 : ℝ) ^ p + (992362517/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229865477/250000000 : ℝ)) (y := (992362517/1000000000 : ℝ)) (X := (7801067584311/50000000000000 : ℝ)) (Y := (8439787991387/10000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992362517/1000000000 : ℝ) ^ p + (229865477/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362517/1000000000 : ℝ)) (y := (229865477/250000000 : ℝ)) (X := (8439787991387/10000000000000 : ℝ)) (Y := (7801067584311/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (76472977/40000000 : ℝ)) (τ := (229865477/250000000 : ℝ)) (σ := (992362517/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (781625593/830442178 : ℝ) ^ p + (819129643/830442178 : ℝ) ^ p := by
    exact cert_lt (x := (781625593/830442178 : ℝ)) (y := (819129643/830442178 : ℝ)) (X := (26174437898131/100000000000000 : ℝ)) (Y := (73825563419351/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (229865477/250000000 : ℝ)) (n' := (415221089/500000000 : ℝ)) (Ab := (781625593/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (919462531/1000000000 : ℝ) ^ p + (992362393/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919462531/1000000000 : ℝ)) (y := (992362393/1000000000 : ℝ)) (X := (15602369065663/100000000000000 : ℝ)) (Y := (84397646586559/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992362393/1000000000 : ℝ) ^ p + (919462531/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362393/1000000000 : ℝ)) (y := (919462531/1000000000 : ℝ)) (X := (84397646586559/100000000000000 : ℝ)) (Y := (15602369065663/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (477956231/250000000 : ℝ)) (τ := (919462531/1000000000 : ℝ)) (σ := (992362393/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (781626263/830442919 : ℝ) ^ p + (819130384/830442919 : ℝ) ^ p := by
    exact cert_lt (x := (781626263/830442919 : ℝ)) (y := (819130384/830442919 : ℝ)) (X := (26174417566887/100000000000000 : ℝ)) (Y := (9228197943449/12500000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (919462531/1000000000 : ℝ)) (n' := (830442919/1000000000 : ℝ)) (Ab := (781626263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (919462561/1000000000 : ℝ) ^ p + (992362387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919462561/1000000000 : ℝ)) (y := (992362387/1000000000 : ℝ)) (X := (15602380328847/100000000000000 : ℝ)) (Y := (84397635296543/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992362387/1000000000 : ℝ) ^ p + (919462561/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362387/1000000000 : ℝ)) (y := (919462561/1000000000 : ℝ)) (X := (84397635296543/100000000000000 : ℝ)) (Y := (15602380328847/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477956237/250000000 : ℝ)) (τ := (919462561/1000000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (781626296/830442955 : ℝ) ^ p + (163826084/166088591 : ℝ) ^ p := by
    exact cert_lt (x := (781626296/830442955 : ℝ)) (y := (163826084/166088591 : ℝ)) (X := (6543604228023/25000000000000 : ℝ)) (Y := (36912792262741/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (919462561/1000000000 : ℝ)) (n' := (166088591/200000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (459731281/500000000 : ℝ) ^ p + (992362387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459731281/500000000 : ℝ)) (y := (992362387/1000000000 : ℝ)) (X := (15602380704287/100000000000000 : ℝ)) (Y := (84397635296543/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992362387/1000000000 : ℝ) ^ p + (459731281/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362387/1000000000 : ℝ)) (y := (459731281/500000000 : ℝ)) (X := (84397635296543/100000000000000 : ℝ)) (Y := (15602380704287/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (195406574/207610739 : ℝ) ^ p + (819130421/830442956 : ℝ) ^ p := by
    exact cert_lt (x := (195406574/207610739 : ℝ)) (y := (819130421/830442956 : ℝ)) (X := (13087208107371/50000000000000 : ℝ)) (Y := (14765116910529/20000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (549273369/602392549 : ℝ) ^ p + (598621704/602392549 : ℝ) ^ p := by
    exact cert_lt (x := (549273369/602392549 : ℝ)) (y := (598621704/602392549 : ℝ)) (X := (3242840333137/25000000000000 : ℝ)) (Y := (87028638907047/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1106588836/1192822353 : ℝ) ^ p + (393836606/397607451 : ℝ) ^ p := by
    exact cert_lt (x := (1106588836/1192822353 : ℝ)) (y := (393836606/397607451 : ℝ)) (X := (19008929232509/100000000000000 : ℝ)) (Y := (40495535671399/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992362387/1000000000 : ℝ)) (U := (1192822353/1000000000 : ℝ)) (Ab := (1647820107/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ)) (Ab := (276647209/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab035
