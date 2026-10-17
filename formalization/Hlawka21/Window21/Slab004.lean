import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 4, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab004 (p : ℝ) (hpa : (169/8 : ℝ) ≤ p) (hpb : p ≤ (677/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (532199358059/23068500000000 : ℝ) (2979991/250000000 : ℝ) (1000000138411/4613700000000 : ℝ) (3033/2500 : ℝ) (967767667/500000000 : ℝ) (967720763/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192443397/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11029/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2207/5000 : ℝ)
      else (7567/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11831/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (532199358059/23068500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2979991/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (227281379/250000000 : ℝ) ^ p + (993263871/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (227281379/250000000 : ℝ)) (y := (993263871/1000000000 : ℝ)) (X := (13324034995599/100000000000000 : ℝ)) (Y := (86675980455567/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993263871/1000000000 : ℝ) ^ p + (227281379/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993263871/1000000000 : ℝ)) (y := (227281379/250000000 : ℝ)) (X := (86675980455567/100000000000000 : ℝ)) (Y := (13324034995599/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1902389387/1000000000 : ℝ)) (τ := (227281379/250000000 : ℝ)) (σ := (993263871/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (384750433/409555935 : ℝ) ^ p + (403595953/409555935 : ℝ) ^ p := by
    exact cert_lt (x := (384750433/409555935 : ℝ)) (y := (403595953/409555935 : ℝ)) (X := (26665151675589/100000000000000 : ℝ)) (Y := (366674247237/500000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (227281379/250000000 : ℝ)) (n' := (81911187/100000000 : ℝ)) (Ab := (384750433/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (457548207/500000000 : ℝ) ^ p + (992179981/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (457548207/500000000 : ℝ)) (y := (992179981/1000000000 : ℝ)) (X := (15303230471431/100000000000000 : ℝ)) (Y := (84696784355161/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992179981/1000000000 : ℝ) ^ p + (457548207/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992179981/1000000000 : ℝ)) (y := (457548207/500000000 : ℝ)) (X := (84696784355161/100000000000000 : ℝ)) (Y := (15303230471431/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (381455279/200000000 : ℝ)) (τ := (457548207/500000000 : ℝ)) (σ := (992179981/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (775961599/826281745 : ℝ) ^ p + (814361781/826281745 : ℝ) ^ p := by
    exact cert_lt (x := (775961599/826281745 : ℝ)) (y := (814361781/826281745 : ℝ)) (X := (206766315361/781250000000 : ℝ)) (Y := (73533912936521/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (457548207/500000000 : ℝ)) (n' := (165256349/200000000 : ℝ)) (Ab := (775961599/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (457700323/500000000 : ℝ) ^ p + (198424029/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (457700323/500000000 : ℝ)) (y := (198424029/200000000 : ℝ)) (X := (3082245690179/20000000000000 : ℝ)) (Y := (84588786838723/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198424029/200000000 : ℝ) ^ p + (457700323/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198424029/200000000 : ℝ)) (y := (457700323/500000000 : ℝ)) (X := (84588786838723/100000000000000 : ℝ)) (Y := (3082245690179/20000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1907520791/1000000000 : ℝ)) (τ := (457700323/500000000 : ℝ)) (σ := (198424029/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (776289616/826645845 : ℝ) ^ p + (814725881/826645845 : ℝ) ^ p := by
    exact cert_lt (x := (776289616/826645845 : ℝ)) (y := (814725881/826645845 : ℝ)) (X := (13228028850589/50000000000000 : ℝ)) (Y := (36771971611497/50000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (457700323/500000000 : ℝ)) (n' := (165329169/200000000 : ℝ)) (Ab := (48518101/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (915415971/1000000000 : ℝ) ^ p + (496058559/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915415971/1000000000 : ℝ)) (y := (496058559/500000000 : ℝ)) (X := (1927085971271/12500000000000 : ℝ)) (Y := (84583326918643/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496058559/500000000 : ℝ) ^ p + (915415971/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496058559/500000000 : ℝ)) (y := (915415971/1000000000 : ℝ)) (X := (84583326918643/100000000000000 : ℝ)) (Y := (1927085971271/12500000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1907533089/1000000000 : ℝ)) (τ := (915415971/1000000000 : ℝ)) (σ := (496058559/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (776306137/826664183 : ℝ) ^ p + (814744219/826664183 : ℝ) ^ p := by
    exact cert_lt (x := (776306137/826664183 : ℝ)) (y := (814744219/826664183 : ℝ)) (X := (26455553071691/100000000000000 : ℝ)) (Y := (36772224100987/50000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (915415971/1000000000 : ℝ)) (n' := (826664183/1000000000 : ℝ)) (Ab := (776306137/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (457708371/500000000 : ℝ) ^ p + (496058483/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (457708371/500000000 : ℝ)) (y := (496058483/500000000 : ℝ)) (X := (120445019351/781250000000 : ℝ)) (Y := (42291526379531/50000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496058483/500000000 : ℝ) ^ p + (457708371/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496058483/500000000 : ℝ)) (y := (457708371/500000000 : ℝ)) (X := (42291526379531/50000000000000 : ℝ)) (Y := (120445019351/781250000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (476883427/250000000 : ℝ)) (τ := (457708371/500000000 : ℝ)) (σ := (496058483/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (258768989/275555035 : ℝ) ^ p + (116392163/118095015 : ℝ) ^ p := by
    exact cert_lt (x := (258768989/275555035 : ℝ)) (y := (116392163/118095015 : ℝ)) (X := (26455527235913/100000000000000 : ℝ)) (Y := (73544473590859/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (457708371/500000000 : ℝ)) (n' := (165333021/200000000 : ℝ)) (Ab := (776306967/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (915416781/1000000000 : ℝ) ^ p + (496058479/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915416781/1000000000 : ℝ)) (y := (496058479/500000000 : ℝ)) (X := (3854244093181/25000000000000 : ℝ)) (Y := (42291519164817/50000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496058479/500000000 : ℝ) ^ p + (915416781/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496058479/500000000 : ℝ)) (y := (915416781/1000000000 : ℝ)) (X := (42291519164817/50000000000000 : ℝ)) (Y := (3854244093181/25000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1907533739/1000000000 : ℝ)) (τ := (915416781/1000000000 : ℝ)) (σ := (496058479/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (388153505/413332576 : ℝ) ^ p + (203686297/206666288 : ℝ) ^ p := by
    exact cert_lt (x := (388153505/413332576 : ℝ)) (y := (203686297/206666288 : ℝ)) (X := (330694080203/1250000000000 : ℝ)) (Y := (14708894977017/20000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (915416781/1000000000 : ℝ)) (n' := (12916643/15625000 : ℝ)) (Ab := (77630701/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (915416783/1000000000 : ℝ) ^ p + (496058479/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915416783/1000000000 : ℝ)) (y := (496058479/500000000 : ℝ)) (X := (15416977085329/100000000000000 : ℝ)) (Y := (42291519164817/50000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496058479/500000000 : ℝ) ^ p + (915416783/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496058479/500000000 : ℝ)) (y := (915416783/1000000000 : ℝ)) (X := (42291519164817/50000000000000 : ℝ)) (Y := (15416977085329/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1907533741/1000000000 : ℝ)) (τ := (915416783/1000000000 : ℝ)) (σ := (496058479/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (776307011/826665154 : ℝ) ^ p + (58196085/59047511 : ℝ) ^ p := by
    exact cert_lt (x := (776307011/826665154 : ℝ)) (y := (58196085/59047511 : ℝ)) (X := (26455525783103/100000000000000 : ℝ)) (Y := (73544474940159/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (915416783/1000000000 : ℝ)) (n' := (413332577/500000000 : ℝ)) (Ab := (776307011/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1907533741/1000000000 : ℝ)) (τ := (915416783/1000000000 : ℝ)) (σ := (496058479/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (915416783/1000000000 : ℝ)) (n' := (413332577/500000000 : ℝ)) (Ab := (776307011/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1907533741/1000000000 : ℝ)) (τ := (915416783/1000000000 : ℝ)) (σ := (496058479/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (915416783/1000000000 : ℝ)) (n' := (413332577/500000000 : ℝ)) (Ab := (776307011/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1907533741/1000000000 : ℝ)) (τ := (915416783/1000000000 : ℝ)) (σ := (496058479/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (915416783/1000000000 : ℝ)) (n' := (413332577/500000000 : ℝ)) (Ab := (776307011/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1907533741/1000000000 : ℝ)) (τ := (915416783/1000000000 : ℝ)) (σ := (496058479/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1641754980/1807556603 : ℝ) ^ p + (1795636639/1807556603 : ℝ) ^ p := by
    exact cert_lt (x := (1641754980/1807556603 : ℝ)) (y := (1795636639/1807556603 : ℝ)) (X := (13062204594091/100000000000000 : ℝ)) (Y := (86937795671651/100000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1102822009/1192443397 : ℝ) ^ p + (1180523433/1192443397 : ℝ) ^ p := by
    exact cert_lt (x := (1102822009/1192443397 : ℝ)) (y := (1180523433/1192443397 : ℝ)) (X := (3829558877173/20000000000000 : ℝ)) (Y := (16170441267331/20000000000000 : ℝ)) 677 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496058479/500000000 : ℝ)) (U := (1192443397/1000000000 : ℝ)) (Ab := (82087749/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (915416783/1000000000 : ℝ)) (σ := (496058479/500000000 : ℝ)) (Ab := (1102822009/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab004
