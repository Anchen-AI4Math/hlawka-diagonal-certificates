import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 12, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab012 (p : ℝ) (hpa : (107/4 : ℝ) ≤ p) (hpb : p ≤ (429/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (362560595791/23700500000000 : ℝ) (7849583/1000000000 : ℝ) (800000142203/4740100000000 : ℝ) (591/500 : ℝ) (19489593/10000000 : ℝ) (974420791/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (144480179/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10813/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1373/2500 : ℝ)
      else (4073/5000 : ℝ) ≤ X j i ∧ X j i ≤ (717/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (362560595791/23700500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7849583/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (935184837/1000000000 : ℝ) ^ p + (496629977/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (935184837/1000000000 : ℝ)) (y := (496629977/500000000 : ℝ)) (X := (16583952879049/100000000000000 : ℝ)) (Y := (83416066114217/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496629977/500000000 : ℝ) ^ p + (935184837/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496629977/500000000 : ℝ)) (y := (935184837/1000000000 : ℝ)) (X := (83416066114217/100000000000000 : ℝ)) (Y := (16583952879049/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1928444791/1000000000 : ℝ)) (τ := (935184837/1000000000 : ℝ)) (σ := (496629977/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (815857157/863676502 : ℝ) ^ p + (855826919/863676502 : ℝ) ^ p := by
    exact cert_lt (x := (815857157/863676502 : ℝ)) (y := (855826919/863676502 : ℝ)) (X := (5428499884081/25000000000000 : ℝ)) (Y := (7828600135229/10000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (935184837/1000000000 : ℝ)) (n' := (431838251/500000000 : ℝ)) (Ab := (815857157/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (938643437/1000000000 : ℝ) ^ p + (496242983/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (938643437/1000000000 : ℝ)) (y := (496242983/500000000 : ℝ)) (X := (18309379315413/100000000000000 : ℝ)) (Y := (16338127672911/20000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496242983/500000000 : ℝ) ^ p + (938643437/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496242983/500000000 : ℝ)) (y := (938643437/1000000000 : ℝ)) (X := (16338127672911/20000000000000 : ℝ)) (Y := (18309379315413/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1931129403/1000000000 : ℝ)) (τ := (938643437/1000000000 : ℝ)) (σ := (496242983/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (819500980/867666159 : ℝ) ^ p + (859816576/867666159 : ℝ) ^ p := by
    exact cert_lt (x := (819500980/867666159 : ℝ)) (y := (859816576/867666159 : ℝ)) (X := (1081271326031/5000000000000 : ℝ)) (Y := (78374574355851/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (938643437/1000000000 : ℝ)) (n' := (867666159/1000000000 : ℝ)) (Ab := (40975049/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (187750047/200000000 : ℝ) ^ p + (992460611/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (187750047/200000000 : ℝ)) (y := (992460611/1000000000 : ℝ)) (X := (2295664734389/12500000000000 : ℝ)) (Y := (5102168783103/6250000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992460611/1000000000 : ℝ) ^ p + (187750047/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992460611/1000000000 : ℝ)) (y := (187750047/200000000 : ℝ)) (X := (5102168783103/6250000000000 : ℝ)) (Y := (2295664734389/12500000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (965605423/500000000 : ℝ)) (τ := (187750047/200000000 : ℝ)) (σ := (992460611/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (204903319/216947281 : ℝ) ^ p + (859939541/867789124 : ℝ) ^ p := by
    exact cert_lt (x := (204903319/216947281 : ℝ)) (y := (859939541/867789124 : ℝ)) (X := (10811353968727/50000000000000 : ℝ)) (Y := (19594323211619/25000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (187750047/200000000 : ℝ)) (n' := (216947281/250000000 : ℝ)) (Ab := (204903319/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (938753513/1000000000 : ℝ) ^ p + (992459831/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (938753513/1000000000 : ℝ)) (y := (992459831/1000000000 : ℝ)) (X := (18367037422791/100000000000000 : ℝ)) (Y := (81632980289689/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992459831/1000000000 : ℝ) ^ p + (938753513/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992459831/1000000000 : ℝ)) (y := (938753513/1000000000 : ℝ)) (X := (81632980289689/100000000000000 : ℝ)) (Y := (18367037422791/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (60350417/31250000 : ℝ)) (τ := (938753513/1000000000 : ℝ)) (σ := (992459831/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (819616723/867792898 : ℝ) ^ p + (122849045/123970414 : ℝ) ^ p := by
    exact cert_lt (x := (819616723/867792898 : ℝ)) (y := (122849045/123970414 : ℝ)) (X := (21622624834841/100000000000000 : ℝ)) (Y := (19594344067679/25000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (938753513/1000000000 : ℝ)) (n' := (433896449/500000000 : ℝ)) (Ab := (819616723/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (469376807/500000000 : ℝ) ^ p + (992459807/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469376807/500000000 : ℝ)) (y := (992459807/1000000000 : ℝ)) (X := (3673418081409/20000000000000 : ℝ)) (Y := (40816463679891/50000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992459807/1000000000 : ℝ) ^ p + (469376807/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992459807/1000000000 : ℝ)) (y := (469376807/500000000 : ℝ)) (X := (40816463679891/50000000000000 : ℝ)) (Y := (3673418081409/20000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1931213421/1000000000 : ℝ)) (τ := (469376807/500000000 : ℝ)) (σ := (992459807/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (819616829/867793014 : ℝ) ^ p + (859943431/867793014 : ℝ) ^ p := by
    exact cert_lt (x := (819616829/867793014 : ℝ)) (y := (859943431/867793014 : ℝ)) (X := (432452446331/2000000000000 : ℝ)) (Y := (15675475766977/20000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (469376807/500000000 : ℝ)) (n' := (433896507/500000000 : ℝ)) (Ab := (819616829/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (938753617/1000000000 : ℝ) ^ p + (496229903/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (938753617/1000000000 : ℝ)) (y := (496229903/500000000 : ℝ)) (X := (18367091980837/100000000000000 : ℝ)) (Y := (8163292515437/10000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496229903/500000000 : ℝ) ^ p + (938753617/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496229903/500000000 : ℝ)) (y := (938753617/1000000000 : ℝ)) (X := (8163292515437/10000000000000 : ℝ)) (Y := (18367091980837/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1931213423/1000000000 : ℝ)) (τ := (938753617/1000000000 : ℝ)) (σ := (496229903/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (819616833/867793018 : ℝ) ^ p + (859943435/867793018 : ℝ) ^ p := by
    exact cert_lt (x := (819616833/867793018 : ℝ)) (y := (859943435/867793018 : ℝ)) (X := (21622622473627/100000000000000 : ℝ)) (Y := (15675475784661/20000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (938753617/1000000000 : ℝ)) (n' := (433896509/500000000 : ℝ)) (Ab := (819616833/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1931213423/1000000000 : ℝ)) (τ := (938753617/1000000000 : ℝ)) (σ := (496229903/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (938753617/1000000000 : ℝ)) (n' := (433896509/500000000 : ℝ)) (Ab := (819616833/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1931213423/1000000000 : ℝ)) (τ := (938753617/1000000000 : ℝ)) (σ := (496229903/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (938753617/1000000000 : ℝ)) (n' := (433896509/500000000 : ℝ)) (Ab := (819616833/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1931213423/1000000000 : ℝ)) (τ := (938753617/1000000000 : ℝ)) (σ := (496229903/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (938753617/1000000000 : ℝ)) (n' := (433896509/500000000 : ℝ)) (Ab := (819616833/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1931213423/1000000000 : ℝ)) (τ := (938753617/1000000000 : ℝ)) (σ := (496229903/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (938753617/1000000000 : ℝ)) (n' := (433896509/500000000 : ℝ)) (Ab := (819616833/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1931213423/1000000000 : ℝ)) (τ := (938753617/1000000000 : ℝ)) (σ := (496229903/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (242471975/263451224 : ℝ) ^ p + (262329855/263451224 : ℝ) ^ p := by
    exact cert_lt (x := (242471975/263451224 : ℝ)) (y := (262329855/263451224 : ℝ)) (X := (10807198813679/100000000000000 : ℝ)) (Y := (89192801416999/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (135150548/144480179 : ℝ) ^ p + (1147991849/1155841432 : ℝ) ^ p := by
    exact cert_lt (x := (135150548/144480179 : ℝ)) (y := (1147991849/1155841432 : ℝ)) (X := (8349554321359/50000000000000 : ℝ)) (Y := (83300892030383/100000000000000 : ℝ)) 429 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496229903/500000000 : ℝ)) (U := (144480179/125000000 : ℝ)) (Ab := (67892153/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (938753617/1000000000 : ℝ)) (σ := (496229903/500000000 : ℝ)) (Ab := (33787637/31250000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab012
