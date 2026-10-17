import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 8, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab008 (p : ℝ) (hpa : (85/4 : ℝ) ≤ p) (hpb : p ≤ (681/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (53177055341/2320500000000 : ℝ) (5919007/500000000 : ℝ) (100000013923/464100000000 : ℝ) (3033/2500 : ℝ) (241988481/125000000 : ℝ) (967907561/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192491431/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5517/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(553/1250 : ℝ)
      else (947/1250 : ℝ) ≤ X j i ∧ X j i ≤ (1479/1250 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (53177055341/2320500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5919007/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (454844949/500000000 : ℝ) ^ p + (993293983/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (454844949/500000000 : ℝ)) (y := (993293983/1000000000 : ℝ)) (X := (104229247453/781250000000 : ℝ)) (Y := (86658672319603/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993293983/1000000000 : ℝ) ^ p + (454844949/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993293983/1000000000 : ℝ)) (y := (454844949/500000000 : ℝ)) (X := (86658672319603/100000000000000 : ℝ)) (Y := (104229247453/781250000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1902983881/1000000000 : ℝ)) (τ := (454844949/500000000 : ℝ)) (σ := (993293983/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (154047809/163930691 : ℝ) ^ p + (807815441/819653455 : ℝ) ^ p := by
    exact cert_lt (x := (154047809/163930691 : ℝ)) (y := (807815441/819653455 : ℝ)) (X := (26625961362679/100000000000000 : ℝ)) (Y := (14674807989451/20000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (454844949/500000000 : ℝ)) (n' := (163930691/200000000 : ℝ)) (Ab := (154047809/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (183129001/200000000 : ℝ) ^ p + (992211709/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183129001/200000000 : ℝ)) (y := (992211709/1000000000 : ℝ)) (X := (15328706119231/100000000000000 : ℝ)) (Y := (84671309525951/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992211709/1000000000 : ℝ) ^ p + (183129001/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992211709/1000000000 : ℝ)) (y := (183129001/200000000 : ℝ)) (X := (84671309525951/100000000000000 : ℝ)) (Y := (15328706119231/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (953928357/500000000 : ℝ)) (τ := (183129001/200000000 : ℝ)) (σ := (992211709/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (776680896/826798523 : ℝ) ^ p + (814960509/826798523 : ℝ) ^ p := by
    exact cert_lt (x := (776680896/826798523 : ℝ)) (y := (814960509/826798523 : ℝ)) (X := (26427958834969/100000000000000 : ℝ)) (Y := (73572042487679/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (183129001/200000000 : ℝ)) (n' := (826798523/1000000000 : ℝ)) (Ab := (12135639/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (915945873/1000000000 : ℝ) ^ p + (992152453/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915945873/1000000000 : ℝ)) (y := (992152453/1000000000 : ℝ)) (X := (15436253352641/100000000000000 : ℝ)) (Y := (5285235156291/6250000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992152453/1000000000 : ℝ) ^ p + (915945873/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992152453/1000000000 : ℝ)) (y := (915945873/1000000000 : ℝ)) (X := (5285235156291/6250000000000 : ℝ)) (Y := (15436253352641/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (954049163/500000000 : ℝ)) (τ := (915945873/1000000000 : ℝ)) (σ := (992152453/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (777005200/827158307 : ℝ) ^ p + (815320293/827158307 : ℝ) ^ p := by
    exact cert_lt (x := (777005200/827158307 : ℝ)) (y := (815320293/827158307 : ℝ)) (X := (26418065176097/100000000000000 : ℝ)) (Y := (9197741950933/12500000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (915945873/1000000000 : ℝ)) (n' := (827158307/1000000000 : ℝ)) (Ab := (1942513/2500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (915960901/1000000000 : ℝ) ^ p + (992149481/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (915960901/1000000000 : ℝ)) (y := (992149481/1000000000 : ℝ)) (X := (15441644021647/100000000000000 : ℝ)) (Y := (10569796485213/12500000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992149481/1000000000 : ℝ) ^ p + (915960901/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992149481/1000000000 : ℝ)) (y := (915960901/1000000000 : ℝ)) (X := (10569796485213/12500000000000 : ℝ)) (Y := (15441644021647/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (954055191/500000000 : ℝ)) (τ := (915960901/1000000000 : ℝ)) (σ := (992149481/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (259007132/275725425 : ℝ) ^ p + (815338261/827176275 : ℝ) ^ p := by
    exact cert_lt (x := (259007132/275725425 : ℝ)) (y := (815338261/827176275 : ℝ)) (X := (6604392832177/25000000000000 : ℝ)) (Y := (36791214744049/50000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (915960901/1000000000 : ℝ)) (n' := (33087051/40000000 : ℝ)) (Ab := (194255349/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (915961651/1000000000 : ℝ) ^ p + (248037333/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (915961651/1000000000 : ℝ)) (y := (248037333/250000000 : ℝ)) (X := (15441913099903/100000000000000 : ℝ)) (Y := (84558101633857/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248037333/250000000 : ℝ) ^ p + (915961651/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248037333/250000000 : ℝ)) (y := (915961651/1000000000 : ℝ)) (X := (84558101633857/100000000000000 : ℝ)) (Y := (15441913099903/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1908110983/1000000000 : ℝ)) (τ := (915961651/1000000000 : ℝ)) (σ := (248037333/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (777022204/827177171 : ℝ) ^ p + (815339157/827177171 : ℝ) ^ p := by
    exact cert_lt (x := (777022204/827177171 : ℝ)) (y := (815339157/827177171 : ℝ)) (X := (13208773482981/50000000000000 : ℝ)) (Y := (73582454115683/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (915961651/1000000000 : ℝ)) (n' := (827177171/1000000000 : ℝ)) (Ab := (194255551/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (114495211/125000000 : ℝ) ^ p + (39685973/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (114495211/125000000 : ℝ)) (y := (39685973/40000000 : ℝ)) (X := (7720963187273/50000000000000 : ℝ)) (Y := (8455808893767/10000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (39685973/40000000 : ℝ) ^ p + (114495211/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (39685973/40000000 : ℝ)) (y := (114495211/125000000 : ℝ)) (X := (8455808893767/10000000000000 : ℝ)) (Y := (7720963187273/50000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1908111013/1000000000 : ℝ)) (τ := (114495211/125000000 : ℝ)) (σ := (39685973/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (777022245/827177216 : ℝ) ^ p + (407669601/413588608 : ℝ) ^ p := by
    exact cert_lt (x := (777022245/827177216 : ℝ)) (y := (407669601/413588608 : ℝ)) (X := (6604386511503/25000000000000 : ℝ)) (Y := (36791227676279/50000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (114495211/125000000 : ℝ)) (n' := (3231161/3906250 : ℝ)) (Ab := (155404449/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (915961691/1000000000 : ℝ) ^ p + (248037331/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (915961691/1000000000 : ℝ)) (y := (248037331/250000000 : ℝ)) (X := (15441927450869/100000000000000 : ℝ)) (Y := (84558087123929/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248037331/250000000 : ℝ) ^ p + (915961691/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248037331/250000000 : ℝ)) (y := (915961691/1000000000 : ℝ)) (X := (84558087123929/100000000000000 : ℝ)) (Y := (15441927450869/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (381622203/200000000 : ℝ)) (τ := (915961691/1000000000 : ℝ)) (σ := (248037331/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (777022247/827177219 : ℝ) ^ p + (815339205/827177219 : ℝ) ^ p := by
    exact cert_lt (x := (777022247/827177219 : ℝ)) (y := (815339205/827177219 : ℝ)) (X := (13208772727047/50000000000000 : ℝ)) (Y := (73582455435017/100000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (915961691/1000000000 : ℝ)) (n' := (827177219/1000000000 : ℝ)) (Ab := (777022247/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (381622203/200000000 : ℝ)) (τ := (915961691/1000000000 : ℝ)) (σ := (248037331/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (915961691/1000000000 : ℝ)) (n' := (827177219/1000000000 : ℝ)) (Ab := (777022247/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (381622203/200000000 : ℝ)) (τ := (915961691/1000000000 : ℝ)) (σ := (248037331/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (915961691/1000000000 : ℝ)) (n' := (827177219/1000000000 : ℝ)) (Ab := (777022247/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (381622203/200000000 : ℝ)) (τ := (915961691/1000000000 : ℝ)) (σ := (248037331/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (915961691/1000000000 : ℝ)) (n' := (827177219/1000000000 : ℝ)) (Ab := (777022247/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (381622203/200000000 : ℝ)) (τ := (915961691/1000000000 : ℝ)) (σ := (248037331/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1642567174/1807508569 : ℝ) ^ p + (1795670555/1807508569 : ℝ) ^ p := by
    exact cert_lt (x := (1642567174/1807508569 : ℝ)) (y := (1795670555/1807508569 : ℝ)) (X := (3262498374731/25000000000000 : ℝ)) (Y := (21737501676479/25000000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1103322293/1192491431 : ℝ) ^ p + (1180653417/1192491431 : ℝ) ^ p := by
    exact cert_lt (x := (1103322293/1192491431 : ℝ)) (y := (1180653417/1192491431 : ℝ)) (X := (4782298349003/25000000000000 : ℝ)) (Y := (64696645843/80000000000 : ℝ)) 681 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248037331/250000000 : ℝ)) (U := (1192491431/1000000000 : ℝ)) (Ab := (821283587/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (915961691/1000000000 : ℝ)) (σ := (248037331/250000000 : ℝ)) (Ab := (1103322293/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab008
