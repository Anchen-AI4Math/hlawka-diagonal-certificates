import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 91, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab091 (p : ℝ) (hpa : (763/32 : ℝ) ≤ p) (hpb : p ≤ (191/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (523877161631/26037375000000 : ℝ) (10356843/1000000000 : ℝ) (4000000624897/20829900000000 : ℝ) (3033/2500 : ℝ) (971385047/500000000 : ℝ) (485674043/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149191191/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11129/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4593/10000 : ℝ)
      else (7743/10000 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (523877161631/26037375000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10356843/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (115000521/125000000 : ℝ) ^ p + (124233313/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (115000521/125000000 : ℝ)) (y := (124233313/125000000 : ℝ)) (X := (2732192837679/20000000000000 : ℝ)) (Y := (86339054411039/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124233313/125000000 : ℝ) ^ p + (115000521/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (124233313/125000000 : ℝ)) (y := (115000521/125000000 : ℝ)) (X := (86339054411039/100000000000000 : ℝ)) (Y := (2732192837679/20000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (119616917/62500000 : ℝ)) (τ := (115000521/125000000 : ℝ)) (σ := (124233313/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783778813/829380490 : ℝ) ^ p + (819023647/829380490 : ℝ) ^ p := by
    exact cert_lt (x := (783778813/829380490 : ℝ)) (y := (819023647/829380490 : ℝ)) (X := (25919280732383/100000000000000 : ℝ)) (Y := (1852018003087/2500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (115000521/125000000 : ℝ)) (n' := (82938049/100000000 : ℝ)) (Ab := (783778813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (925610943/1000000000 : ℝ) ^ p + (496412959/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925610943/1000000000 : ℝ)) (y := (496412959/500000000 : ℝ)) (X := (1974194704559/12500000000000 : ℝ)) (Y := (84206459221659/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496412959/500000000 : ℝ) ^ p + (925610943/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496412959/500000000 : ℝ)) (y := (925610943/1000000000 : ℝ)) (X := (84206459221659/100000000000000 : ℝ)) (Y := (1974194704559/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918436861/1000000000 : ℝ)) (τ := (925610943/1000000000 : ℝ)) (σ := (496412959/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (789814525/836007966 : ℝ) ^ p + (275217041/278669322 : ℝ) ^ p := by
    exact cert_lt (x := (789814525/836007966 : ℝ)) (y := (275217041/278669322 : ℝ)) (X := (12870887135731/50000000000000 : ℝ)) (Y := (37129113524541/50000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (925610943/1000000000 : ℝ)) (n' := (418003983/500000000 : ℝ)) (Ab := (31592581/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925851907/1000000000 : ℝ) ^ p + (99277727/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (925851907/1000000000 : ℝ)) (y := (99277727/100000000 : ℝ)) (X := (1986501661937/12500000000000 : ℝ)) (Y := (2102700108259/2500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99277727/100000000 : ℝ) ^ p + (925851907/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99277727/100000000 : ℝ)) (y := (925851907/1000000000 : ℝ)) (X := (2102700108259/2500000000000 : ℝ)) (Y := (1986501661937/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918629177/1000000000 : ℝ)) (τ := (925851907/1000000000 : ℝ)) (σ := (99277727/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (395036537/418145957 : ℝ) ^ p + (825935071/836291914 : ℝ) ^ p := by
    exact cert_lt (x := (395036537/418145957 : ℝ)) (y := (825935071/836291914 : ℝ)) (X := (25734222554323/100000000000000 : ℝ)) (Y := (74265778333799/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925851907/1000000000 : ℝ)) (n' := (418145957/500000000 : ℝ)) (Ab := (395036537/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (231465539/250000000 : ℝ) ^ p + (992775193/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231465539/250000000 : ℝ)) (y := (992775193/1000000000 : ℝ)) (X := (1987026744103/12500000000000 : ℝ)) (Y := (1682076066161/2000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992775193/1000000000 : ℝ) ^ p + (231465539/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992775193/1000000000 : ℝ)) (y := (231465539/250000000 : ℝ)) (X := (1682076066161/2000000000000 : ℝ)) (Y := (1987026744103/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1918637349/1000000000 : ℝ)) (τ := (231465539/250000000 : ℝ)) (σ := (992775193/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (79008407/83630399 : ℝ) ^ p + (825947147/836303990 : ℝ) ^ p := by
    exact cert_lt (x := (79008407/83630399 : ℝ)) (y := (825947147/836303990 : ℝ)) (X := (12866950848967/50000000000000 : ℝ)) (Y := (74266099384363/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (231465539/250000000 : ℝ)) (n' := (83630399/100000000 : ℝ)) (Ab := (79008407/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925862591/1000000000 : ℝ) ^ p + (198555021/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (925862591/1000000000 : ℝ)) (y := (198555021/200000000 : ℝ)) (X := (15896392265549/100000000000000 : ℝ)) (Y := (8410362532021/10000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198555021/200000000 : ℝ) ^ p + (925862591/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198555021/200000000 : ℝ)) (y := (925862591/1000000000 : ℝ)) (X := (8410362532021/10000000000000 : ℝ)) (Y := (15896392265549/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (14989357/7812500 : ℝ)) (τ := (925862591/1000000000 : ℝ)) (σ := (198555021/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (395042268/418152251 : ℝ) ^ p + (825947659/836304502 : ℝ) ^ p := by
    exact cert_lt (x := (395042268/418152251 : ℝ)) (y := (825947659/836304502 : ℝ)) (X := (12866943965601/50000000000000 : ℝ)) (Y := (9283264124517/12500000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925862591/1000000000 : ℝ)) (n' := (418152251/500000000 : ℝ)) (Ab := (98760567/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (92586261/100000000 : ℝ) ^ p + (992775101/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92586261/100000000 : ℝ)) (y := (992775101/1000000000 : ℝ)) (X := (3974100013491/25000000000000 : ℝ)) (Y := (84103617229863/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992775101/1000000000 : ℝ) ^ p + (92586261/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992775101/1000000000 : ℝ)) (y := (92586261/100000000 : ℝ)) (X := (84103617229863/100000000000000 : ℝ)) (Y := (3974100013491/25000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1918637711/1000000000 : ℝ)) (τ := (92586261/100000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (87787173/92922725 : ℝ) ^ p + (39330842/39824025 : ℝ) ^ p := by
    exact cert_lt (x := (87787173/92922725 : ℝ)) (y := (39330842/39824025 : ℝ)) (X := (5146777472883/20000000000000 : ℝ)) (Y := (37133056803801/50000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (92586261/100000000 : ℝ)) (n' := (33452181/40000000 : ℝ)) (Ab := (790084557/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (925862611/1000000000 : ℝ) ^ p + (992775101/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (925862611/1000000000 : ℝ)) (y := (992775101/1000000000 : ℝ)) (X := (15896400463881/100000000000000 : ℝ)) (Y := (84103617229863/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992775101/1000000000 : ℝ) ^ p + (925862611/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992775101/1000000000 : ℝ)) (y := (925862611/1000000000 : ℝ)) (X := (84103617229863/100000000000000 : ℝ)) (Y := (15896400463881/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (395042279/418152263 : ℝ) ^ p + (825947683/836304526 : ℝ) ^ p := by
    exact cert_lt (x := (395042279/418152263 : ℝ)) (y := (825947683/836304526 : ℝ)) (X := (25733887407393/100000000000000 : ℝ)) (Y := (74266113634187/100000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (n' := (418152263/500000000 : ℝ)) (Ab := (395042279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (119914857/62500000 : ℝ)) (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (552526851/602156824 : ℝ) ^ p + (598704543/602156824 : ℝ) ^ p := by
    exact cert_lt (x := (552526851/602156824 : ℝ)) (y := (598704543/602156824 : ℝ)) (X := (6413426924019/50000000000000 : ℝ)) (Y := (5448321646543/6250000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (556400609/596764764 : ℝ) ^ p + (394390895/397843176 : ℝ) ^ p := by
    exact cert_lt (x := (556400609/596764764 : ℝ)) (y := (394390895/397843176 : ℝ)) (X := (18785732426027/100000000000000 : ℝ)) (Y := (40607134111751/50000000000000 : ℝ)) 191 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992775101/1000000000 : ℝ)) (U := (149191191/125000000 : ℝ)) (Ab := (1657580553/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925862611/1000000000 : ℝ)) (σ := (992775101/1000000000 : ℝ)) (Ab := (556400609/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab091
