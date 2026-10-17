import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 49, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab049 (p : ℝ) (hpa : (465/16 : ℝ) ≤ p) (hpb : p ≤ (233/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (287059600553/20599500000000 : ℝ) (7135813/1000000000 : ℝ) (640000123597/4119900000000 : ℝ) (591/500 : ℝ) (1525753/781250 : ℝ) (976431943/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157278153/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10879/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2787/5000 : ℝ)
      else (823/1000 : ℝ) ≤ X j i ∧ X j i ≤ (2873/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (287059600553/20599500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7135813/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (470287493/500000000 : ℝ) ^ p + (993708539/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (470287493/500000000 : ℝ)) (y := (993708539/1000000000 : ℝ)) (X := (16791268126039/100000000000000 : ℝ)) (Y := (20802188015093/25000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993708539/1000000000 : ℝ) ^ p + (470287493/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993708539/1000000000 : ℝ)) (y := (470287493/500000000 : ℝ)) (X := (20802188015093/25000000000000 : ℝ)) (Y := (16791268126039/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (77371341/40000000 : ℝ)) (τ := (470287493/500000000 : ℝ)) (σ := (993708539/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (823255931/868052898 : ℝ) ^ p + (860917085/868052898 : ℝ) ^ p := by
    exact cert_lt (x := (823255931/868052898 : ℝ)) (y := (860917085/868052898 : ℝ)) (X := (21369541985209/100000000000000 : ℝ)) (Y := (78630459398033/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (470287493/500000000 : ℝ)) (n' := (434026449/500000000 : ℝ)) (Ab := (823255931/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (943840921/1000000000 : ℝ) ^ p + (248242371/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (943840921/1000000000 : ℝ)) (y := (248242371/250000000 : ℝ)) (X := (18574948828533/100000000000000 : ℝ)) (Y := (81425070613983/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248242371/250000000 : ℝ) ^ p + (943840921/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248242371/250000000 : ℝ)) (y := (943840921/1000000000 : ℝ)) (X := (81425070613983/100000000000000 : ℝ)) (Y := (18574948828533/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (387362081/200000000 : ℝ)) (τ := (943840921/1000000000 : ℝ)) (σ := (248242371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (826691667/871789825 : ℝ) ^ p + (864654012/871789825 : ℝ) ^ p := by
    exact cert_lt (x := (826691667/871789825 : ℝ)) (y := (864654012/871789825 : ℝ)) (X := (10644067835907/50000000000000 : ℝ)) (Y := (39355932913187/50000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (943840921/1000000000 : ℝ)) (n' := (34871593/40000000 : ℝ)) (Ab := (826691667/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (117991439/125000000 : ℝ) ^ p + (496473853/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (117991439/125000000 : ℝ)) (y := (496473853/500000000 : ℝ)) (X := (745077774809/4000000000000 : ℝ)) (Y := (81373074339271/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496473853/500000000 : ℝ) ^ p + (117991439/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496473853/500000000 : ℝ)) (y := (117991439/125000000 : ℝ)) (X := (81373074339271/100000000000000 : ℝ)) (Y := (745077774809/4000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (968439609/500000000 : ℝ)) (τ := (117991439/125000000 : ℝ)) (σ := (496473853/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (826786792/871893297 : ℝ) ^ p + (864757484/871893297 : ℝ) ^ p := by
    exact cert_lt (x := (826786792/871893297 : ℝ)) (y := (864757484/871893297 : ℝ)) (X := (2128589030599/10000000000000 : ℝ)) (Y := (78714111117847/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (117991439/125000000 : ℝ)) (n' := (871893297/1000000000 : ℝ)) (Ab := (103348349/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (943934011/1000000000 : ℝ) ^ p + (31029597/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (943934011/1000000000 : ℝ)) (y := (31029597/31250000 : ℝ)) (X := (372567613691/2000000000000 : ℝ)) (Y := (20342909370963/25000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (31029597/31250000 : ℝ) ^ p + (943934011/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31029597/31250000 : ℝ)) (y := (943934011/1000000000 : ℝ)) (X := (20342909370963/25000000000000 : ℝ)) (Y := (372567613691/2000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (387376223/200000000 : ℝ)) (τ := (943934011/1000000000 : ℝ)) (σ := (31029597/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (826789415/871896151 : ℝ) ^ p + (864760338/871896151 : ℝ) ^ p := by
    exact cert_lt (x := (826789415/871896151 : ℝ)) (y := (864760338/871896151 : ℝ)) (X := (21285827806821/100000000000000 : ℝ)) (Y := (39357086520783/50000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (943934011/1000000000 : ℝ)) (n' := (871896151/1000000000 : ℝ)) (Ab := (165357883/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (1474897/1562500 : ℝ) ^ p + (62059193/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (1474897/1562500 : ℝ)) (y := (62059193/62500000 : ℝ)) (X := (9314210172103/50000000000000 : ℝ)) (Y := (40685799647669/50000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62059193/62500000 : ℝ) ^ p + (1474897/1562500 : ℝ) ^ p := by
    exact cert_lt (x := (62059193/62500000 : ℝ)) (y := (1474897/1562500 : ℝ)) (X := (40685799647669/50000000000000 : ℝ)) (Y := (9314210172103/50000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (121055073/62500000 : ℝ)) (τ := (1474897/1562500 : ℝ)) (σ := (62059193/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (413394744/435948115 : ℝ) ^ p + (864760417/871896230 : ℝ) ^ p := by
    exact cert_lt (x := (413394744/435948115 : ℝ)) (y := (864760417/871896230 : ℝ)) (X := (10642913186197/50000000000000 : ℝ)) (Y := (78714174755637/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (1474897/1562500 : ℝ)) (n' := (87189623/100000000 : ℝ)) (Ab := (51674343/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (471967041/500000000 : ℝ) ^ p + (992947087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (471967041/500000000 : ℝ)) (y := (992947087/1000000000 : ℝ)) (X := (9314210746881/50000000000000 : ℝ)) (Y := (81371596908557/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992947087/1000000000 : ℝ) ^ p + (471967041/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992947087/1000000000 : ℝ)) (y := (471967041/500000000 : ℝ)) (X := (81371596908557/100000000000000 : ℝ)) (Y := (9314210746881/50000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1936881169/1000000000 : ℝ)) (τ := (471967041/500000000 : ℝ)) (σ := (992947087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (826789491/871896233 : ℝ) ^ p + (864760420/871896233 : ℝ) ^ p := by
    exact cert_lt (x := (826789491/871896233 : ℝ)) (y := (864760420/871896233 : ℝ)) (X := (21285826488769/100000000000000 : ℝ)) (Y := (78714174820729/100000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (471967041/500000000 : ℝ)) (n' := (871896233/1000000000 : ℝ)) (Ab := (826789491/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1936881169/1000000000 : ℝ)) (τ := (471967041/500000000 : ℝ)) (σ := (992947087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (471967041/500000000 : ℝ)) (n' := (871896233/1000000000 : ℝ)) (Ab := (826789491/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1936881169/1000000000 : ℝ)) (τ := (471967041/500000000 : ℝ)) (σ := (992947087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (471967041/500000000 : ℝ)) (n' := (871896233/1000000000 : ℝ)) (Ab := (826789491/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1936881169/1000000000 : ℝ)) (τ := (471967041/500000000 : ℝ)) (σ := (992947087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (471967041/500000000 : ℝ)) (n' := (871896233/1000000000 : ℝ)) (Ab := (826789491/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1936881169/1000000000 : ℝ)) (τ := (471967041/500000000 : ℝ)) (σ := (992947087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (471967041/500000000 : ℝ)) (n' := (871896233/1000000000 : ℝ)) (Ab := (826789491/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1936881169/1000000000 : ℝ)) (τ := (471967041/500000000 : ℝ)) (σ := (992947087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1706527655/1842721847 : ℝ) ^ p + (1835586034/1842721847 : ℝ) ^ p := by
    exact cert_lt (x := (1706527655/1842721847 : ℝ)) (y := (1835586034/1842721847 : ℝ)) (X := (53426229549/500000000000 : ℝ)) (Y := (44657377140973/50000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1087818683/1157278153 : ℝ) ^ p + (1150142340/1157278153 : ℝ) ^ p := by
    exact cert_lt (x := (1087818683/1157278153 : ℝ)) (y := (1150142340/1157278153 : ℝ)) (X := (16484806372903/100000000000000 : ℝ)) (Y := (3340607763437/4000000000000 : ℝ)) 233 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992947087/1000000000 : ℝ)) (U := (1157278153/1000000000 : ℝ)) (Ab := (341305531/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (471967041/500000000 : ℝ)) (σ := (992947087/1000000000 : ℝ)) (Ab := (1087818683/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab049
