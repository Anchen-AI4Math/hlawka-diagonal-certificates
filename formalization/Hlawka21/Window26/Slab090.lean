import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 90, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab090 (p : ℝ) (hpa : (253/8 : ℝ) ≤ p) (hpb : p ≤ (507/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (177659008793/14009875000000 : ℝ) (1620249/250000000 : ℝ) (1600000336237/11207900000000 : ℝ) (591/500 : ℝ) (244590761/125000000 : ℝ) (3913283/4000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289681137/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10943/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(353/625 : ℝ)
      else (8307/10000 : ℝ) ≤ X j i ∧ X j i ≤ (1439/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (177659008793/14009875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1620249/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (472795697/500000000 : ℝ) ^ p + (497071063/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (472795697/500000000 : ℝ)) (y := (497071063/500000000 : ℝ)) (X := (4246635757469/25000000000000 : ℝ)) (Y := (83013479458609/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497071063/500000000 : ℝ) ^ p + (472795697/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (497071063/500000000 : ℝ)) (y := (472795697/500000000 : ℝ)) (X := (83013479458609/100000000000000 : ℝ)) (Y := (4246635757469/25000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (24246669/12500000 : ℝ)) (τ := (472795697/500000000 : ℝ)) (σ := (497071063/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (830188455/872031562 : ℝ) ^ p + (432775283/436015781 : ℝ) ^ p := by
    exact cert_lt (x := (830188455/872031562 : ℝ)) (y := (432775283/436015781 : ℝ)) (X := (21052183135287/100000000000000 : ℝ)) (Y := (78947817766677/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (472795697/500000000 : ℝ)) (n' := (436015781/500000000 : ℝ)) (Ab := (166037691/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (118582357/125000000 : ℝ) ^ p + (248360189/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (118582357/125000000 : ℝ)) (y := (248360189/250000000 : ℝ)) (X := (18822408526871/100000000000000 : ℝ)) (Y := (81177611586367/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248360189/250000000 : ℝ) ^ p + (118582357/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248360189/250000000 : ℝ)) (y := (118582357/125000000 : ℝ)) (X := (81177611586367/100000000000000 : ℝ)) (Y := (18822408526871/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (485524903/250000000 : ℝ)) (τ := (118582357/125000000 : ℝ)) (σ := (248360189/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (833411374/875514947 : ℝ) ^ p + (869033951/875514947 : ℝ) ^ p := by
    exact cert_lt (x := (833411374/875514947 : ℝ)) (y := (869033951/875514947 : ℝ)) (X := (20977622277803/100000000000000 : ℝ)) (Y := (79022379133459/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (118582357/125000000 : ℝ)) (n' := (875514947/1000000000 : ℝ)) (Ab := (416705687/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (189747061/200000000 : ℝ) ^ p + (198684433/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (189747061/200000000 : ℝ)) (y := (198684433/200000000 : ℝ)) (X := (18870532559859/100000000000000 : ℝ)) (Y := (8112948774061/10000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198684433/200000000 : ℝ) ^ p + (189747061/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198684433/200000000 : ℝ)) (y := (189747061/200000000 : ℝ)) (X := (8112948774061/10000000000000 : ℝ)) (Y := (18870532559859/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (194215747/100000000 : ℝ)) (τ := (189747061/200000000 : ℝ)) (σ := (198684433/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (833491560/875601619 : ℝ) ^ p + (869120623/875601619 : ℝ) ^ p := by
    exact cert_lt (x := (833491560/875601619 : ℝ)) (y := (869120623/875601619 : ℝ)) (X := (655492929813/3125000000000 : ℝ)) (Y := (19756056909231/25000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (189747061/200000000 : ℝ)) (n' := (875601619/1000000000 : ℝ)) (Ab := (20837289/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (948737199/1000000000 : ℝ) ^ p + (124177713/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (948737199/1000000000 : ℝ)) (y := (124177713/125000000 : ℝ)) (X := (18871726329003/100000000000000 : ℝ)) (Y := (81128294767381/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124177713/125000000 : ℝ) ^ p + (948737199/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124177713/125000000 : ℝ)) (y := (948737199/1000000000 : ℝ)) (X := (81128294767381/100000000000000 : ℝ)) (Y := (18871726329003/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1942158903/1000000000 : ℝ)) (τ := (948737199/1000000000 : ℝ)) (σ := (124177713/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (138915591/145933961 : ℝ) ^ p + (144853795/145933961 : ℝ) ^ p := by
    exact cert_lt (x := (138915591/145933961 : ℝ)) (y := (144853795/145933961 : ℝ)) (X := (20975727705337/100000000000000 : ℝ)) (Y := (79024273423111/100000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (948737199/1000000000 : ℝ)) (n' := (437801883/500000000 : ℝ)) (Ab := (416746773/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (948737247/1000000000 : ℝ) ^ p + (248355423/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (948737247/1000000000 : ℝ)) (y := (248355423/250000000 : ℝ)) (X := (1887175658387/10000000000000 : ℝ)) (Y := (3245130548563/4000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248355423/250000000 : ℝ) ^ p + (948737247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248355423/250000000 : ℝ)) (y := (948737247/1000000000 : ℝ)) (X := (3245130548563/4000000000000 : ℝ)) (Y := (1887175658387/10000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1942158939/1000000000 : ℝ)) (τ := (948737247/1000000000 : ℝ)) (σ := (248355423/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (16028723/16838535 : ℝ) ^ p + (72426902/72966985 : ℝ) ^ p := by
    exact cert_lt (x := (16028723/16838535 : ℝ)) (y := (72426902/72966985 : ℝ)) (X := (5243931646631/25000000000000 : ℝ)) (Y := (39512137287347/50000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (948737247/1000000000 : ℝ)) (n' := (43780191/50000000 : ℝ)) (Ab := (208373399/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (29648039/31250000 : ℝ) ^ p + (248355423/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (29648039/31250000 : ℝ)) (y := (248355423/250000000 : ℝ)) (X := (943587860709/5000000000000 : ℝ)) (Y := (3245130548563/4000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248355423/250000000 : ℝ) ^ p + (29648039/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (248355423/250000000 : ℝ)) (y := (29648039/31250000 : ℝ)) (X := (3245130548563/4000000000000 : ℝ)) (Y := (943587860709/5000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (97107947/50000000 : ℝ)) (τ := (29648039/31250000 : ℝ)) (σ := (248355423/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (833493597/875603821 : ℝ) ^ p + (869122825/875603821 : ℝ) ^ p := by
    exact cert_lt (x := (833493597/875603821 : ℝ)) (y := (869122825/875603821 : ℝ)) (X := (5243931656219/25000000000000 : ℝ)) (Y := (3951213729801/5000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (29648039/31250000 : ℝ)) (n' := (875603821/1000000000 : ℝ)) (Ab := (833493597/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (97107947/50000000 : ℝ)) (τ := (29648039/31250000 : ℝ)) (σ := (248355423/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (29648039/31250000 : ℝ)) (n' := (875603821/1000000000 : ℝ)) (Ab := (833493597/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (97107947/50000000 : ℝ)) (τ := (29648039/31250000 : ℝ)) (σ := (248355423/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (29648039/31250000 : ℝ)) (n' := (875603821/1000000000 : ℝ)) (Ab := (833493597/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (97107947/50000000 : ℝ)) (τ := (29648039/31250000 : ℝ)) (σ := (248355423/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (29648039/31250000 : ℝ)) (n' := (875603821/1000000000 : ℝ)) (Ab := (833493597/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (97107947/50000000 : ℝ)) (τ := (29648039/31250000 : ℝ)) (σ := (248355423/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (29648039/31250000 : ℝ)) (n' := (875603821/1000000000 : ℝ)) (Ab := (833493597/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (97107947/50000000 : ℝ)) (τ := (29648039/31250000 : ℝ)) (σ := (248355423/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1715230121/1841275452 : ℝ) ^ p + (152899538/153439621 : ℝ) ^ p := by
    exact cert_lt (x := (1715230121/1841275452 : ℝ)) (y := (152899538/153439621 : ℝ)) (X := (10571584221609/100000000000000 : ℝ)) (Y := (11178552000927/12500000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (547109545/579362274 : ℝ) ^ p + (96020296/96560379 : ℝ) ^ p := by
    exact cert_lt (x := (547109545/579362274 : ℝ)) (y := (96020296/96560379 : ℝ)) (X := (4070842310907/25000000000000 : ℝ)) (Y := (41858315681421/50000000000000 : ℝ)) 507 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248355423/250000000 : ℝ)) (U := (289681137/250000000 : ℝ)) (Ab := (1715230121/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (29648039/31250000 : ℝ)) (σ := (248355423/250000000 : ℝ)) (Ab := (109421909/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab090
