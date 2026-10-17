import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 18, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab018 (p : ℝ) (hpa : (217/8 : ℝ) ≤ p) (hpb : p ≤ (435/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (90477980713/6008187500000 : ℝ) (3862223/500000000 : ℝ) (1600000288393/9613100000000 : ℝ) (591/500 : ℝ) (974827187/500000000 : ℝ) (487384961/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156083193/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1353/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(2753/5000 : ℝ)
      else (8161/10000 : ℝ) ≤ X j i ∧ X j i ≤ (459/400 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (90477980713/6008187500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3862223/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (936124161/1000000000 : ℝ) ^ p + (31041777/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (936124161/1000000000 : ℝ)) (y := (31041777/31250000 : ℝ)) (X := (8309947780907/50000000000000 : ℝ)) (Y := (41690061794719/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31041777/31250000 : ℝ) ^ p + (936124161/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31041777/31250000 : ℝ)) (y := (936124161/1000000000 : ℝ)) (X := (41690061794719/50000000000000 : ℝ)) (Y := (8309947780907/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (77178441/40000000 : ℝ)) (τ := (936124161/1000000000 : ℝ)) (σ := (31041777/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817142898/864446657 : ℝ) ^ p + (856722211/864446657 : ℝ) ^ p := by
    exact cert_lt (x := (817142898/864446657 : ℝ)) (y := (856722211/864446657 : ℝ)) (X := (21653712756571/100000000000000 : ℝ)) (Y := (78346288625339/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936124161/1000000000 : ℝ)) (n' := (864446657/1000000000 : ℝ)) (Ab := (408571449/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (37582031/40000000 : ℝ) ^ p + (31017767/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (37582031/40000000 : ℝ)) (y := (31017767/31250000 : ℝ)) (X := (18355635965807/100000000000000 : ℝ)) (Y := (3265775243539/4000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (31017767/31250000 : ℝ) ^ p + (37582031/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (31017767/31250000 : ℝ)) (y := (37582031/40000000 : ℝ)) (X := (3265775243539/4000000000000 : ℝ)) (Y := (18355635965807/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1932119319/1000000000 : ℝ)) (τ := (37582031/40000000 : ℝ)) (σ := (31017767/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (4856521/5138425 : ℝ) ^ p + (860669379/868393825 : ℝ) ^ p := by
    exact cert_lt (x := (4856521/5138425 : ℝ)) (y := (860669379/868393825 : ℝ)) (X := (2695796440961/12500000000000 : ℝ)) (Y := (78433629385503/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (37582031/40000000 : ℝ)) (n' := (34735753/40000000 : ℝ)) (Ab := (820752049/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (23491367/25000000 : ℝ) ^ p + (496271911/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (23491367/25000000 : ℝ)) (y := (496271911/500000000 : ℝ)) (X := (18410905258381/100000000000000 : ℝ)) (Y := (40794556334751/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496271911/500000000 : ℝ) ^ p + (23491367/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (496271911/500000000 : ℝ)) (y := (23491367/25000000 : ℝ)) (X := (40794556334751/50000000000000 : ℝ)) (Y := (18410905258381/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (966099251/500000000 : ℝ)) (τ := (23491367/25000000 : ℝ)) (σ := (496271911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (205215319/217128323 : ℝ) ^ p + (430394423/434256646 : ℝ) ^ p := by
    exact cert_lt (x := (205215319/217128323 : ℝ)) (y := (430394423/434256646 : ℝ)) (X := (1347733684151/6250000000000 : ℝ)) (Y := (78436261962513/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (23491367/25000000 : ℝ)) (n' := (217128323/250000000 : ℝ)) (Ab := (205215319/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939657811/1000000000 : ℝ) ^ p + (248135769/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (939657811/1000000000 : ℝ)) (y := (248135769/250000000 : ℝ)) (X := (2301571648707/12500000000000 : ℝ)) (Y := (81587445474701/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248135769/250000000 : ℝ) ^ p + (939657811/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248135769/250000000 : ℝ)) (y := (939657811/1000000000 : ℝ)) (X := (81587445474701/100000000000000 : ℝ)) (Y := (2301571648707/12500000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1932200887/1000000000 : ℝ)) (τ := (939657811/1000000000 : ℝ)) (σ := (248135769/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820864567/868516891 : ℝ) ^ p + (860792445/868516891 : ℝ) ^ p := by
    exact cert_lt (x := (820864567/868516891 : ℝ)) (y := (860792445/868516891 : ℝ)) (X := (1078183000049/5000000000000 : ℝ)) (Y := (39218170630113/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939657811/1000000000 : ℝ)) (n' := (868516891/1000000000 : ℝ)) (Ab := (820864567/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (469828953/500000000 : ℝ) ^ p + (992543053/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469828953/500000000 : ℝ)) (y := (992543053/1000000000 : ℝ)) (X := (147300990399/800000000000 : ℝ)) (Y := (3263495762951/4000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992543053/1000000000 : ℝ) ^ p + (469828953/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992543053/1000000000 : ℝ)) (y := (469828953/500000000 : ℝ)) (X := (3263495762951/4000000000000 : ℝ)) (Y := (147300990399/800000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1932200959/1000000000 : ℝ)) (τ := (469828953/500000000 : ℝ)) (σ := (992543053/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (820864667/868517001 : ℝ) ^ p + (860792555/868517001 : ℝ) ^ p := by
    exact cert_lt (x := (820864667/868517001 : ℝ)) (y := (860792555/868517001 : ℝ)) (X := (10781828584693/50000000000000 : ℝ)) (Y := (19609085920969/25000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (469828953/500000000 : ℝ)) (n' := (868517001/1000000000 : ℝ)) (Ab := (820864667/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (939657909/1000000000 : ℝ) ^ p + (248135763/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (939657909/1000000000 : ℝ)) (y := (248135763/250000000 : ℝ)) (X := (9206312699047/50000000000000 : ℝ)) (Y := (10198423979869/12500000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248135763/250000000 : ℝ) ^ p + (939657909/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248135763/250000000 : ℝ)) (y := (939657909/1000000000 : ℝ)) (X := (10198423979869/12500000000000 : ℝ)) (Y := (9206312699047/50000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (410432335/434258502 : ℝ) ^ p + (430396279/434258502 : ℝ) ^ p := by
    exact cert_lt (x := (410432335/434258502 : ℝ)) (y := (430396279/434258502 : ℝ)) (X := (21563657286943/100000000000000 : ℝ)) (Y := (9804542968747/12500000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (n' := (217129251/250000000 : ℝ)) (Ab := (82086467/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932200961/1000000000 : ℝ)) (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1698901951/1843916807 : ℝ) ^ p + (1836192361/1843916807 : ℝ) ^ p := by
    exact cert_lt (x := (1698901951/1843916807 : ℝ)) (y := (1836192361/1843916807 : ℝ)) (X := (10785961137491/100000000000000 : ℝ)) (Y := (89214039202541/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082337953/1156083193 : ℝ) ^ p + (1148358747/1156083193 : ℝ) ^ p := by
    exact cert_lt (x := (1082337953/1156083193 : ℝ)) (y := (1148358747/1156083193 : ℝ)) (X := (16661925540583/100000000000000 : ℝ)) (Y := (83338074952761/100000000000000 : ℝ)) 435 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248135763/250000000 : ℝ)) (U := (1156083193/1000000000 : ℝ)) (Ab := (1698901951/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (939657909/1000000000 : ℝ)) (σ := (248135763/250000000 : ℝ)) (Ab := (1082337953/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab018
