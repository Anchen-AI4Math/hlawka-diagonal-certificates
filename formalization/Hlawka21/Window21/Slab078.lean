import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 78, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab078 (p : ℝ) (hpa : (375/16 : ℝ) ≤ p) (hpb : p ≤ (751/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1679997121/81900000000 : ℝ) (1320531/125000000 : ℝ) (16000002457/81900000000 : ℝ) (3033/2500 : ℝ) (970896993/500000000 : ℝ) (970858759/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298341043/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2223/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(4569/10000 : ℝ)
      else (7719/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1679997121/81900000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1320531/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (57409161/62500000 : ℝ) ^ p + (993782997/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (57409161/62500000 : ℝ)) (y := (993782997/1000000000 : ℝ)) (X := (13615414886223/100000000000000 : ℝ)) (Y := (86384603647937/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993782997/1000000000 : ℝ) ^ p + (57409161/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (993782997/1000000000 : ℝ)) (y := (57409161/62500000 : ℝ)) (X := (86384603647937/100000000000000 : ℝ)) (Y := (13615414886223/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1912329573/1000000000 : ℝ)) (τ := (57409161/62500000 : ℝ)) (σ := (993782997/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (390929741/414012791 : ℝ) ^ p + (408730667/414012791 : ℝ) ^ p := by
    exact cert_lt (x := (390929741/414012791 : ℝ)) (y := (408730667/414012791 : ℝ)) (X := (13009032279321/50000000000000 : ℝ)) (Y := (36990968287327/50000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (57409161/62500000 : ℝ)) (n' := (414012791/500000000 : ℝ)) (Ab := (390929741/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (115526157/125000000 : ℝ) ^ p + (248183783/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115526157/125000000 : ℝ)) (y := (248183783/250000000 : ℝ)) (X := (15727947444633/100000000000000 : ℝ)) (Y := (16854413752613/20000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248183783/250000000 : ℝ) ^ p + (115526157/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248183783/250000000 : ℝ)) (y := (115526157/125000000 : ℝ)) (X := (16854413752613/20000000000000 : ℝ)) (Y := (15727947444633/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (479236097/250000000 : ℝ)) (τ := (115526157/125000000 : ℝ)) (σ := (248183783/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (393979691/417366629 : ℝ) ^ p + (412084505/417366629 : ℝ) ^ p := by
    exact cert_lt (x := (393979691/417366629 : ℝ)) (y := (412084505/417366629 : ℝ)) (X := (12918773845687/50000000000000 : ℝ)) (Y := (18540613396753/25000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (115526157/125000000 : ℝ)) (n' := (417366629/500000000 : ℝ)) (Ab := (393979691/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (28889327/31250000 : ℝ) ^ p + (992684993/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28889327/31250000 : ℝ)) (y := (992684993/1000000000 : ℝ)) (X := (15827779456427/100000000000000 : ℝ)) (Y := (21043059206959/25000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992684993/1000000000 : ℝ) ^ p + (28889327/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (992684993/1000000000 : ℝ)) (y := (28889327/31250000 : ℝ)) (X := (21043059206959/25000000000000 : ℝ)) (Y := (15827779456427/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1917143457/1000000000 : ℝ)) (τ := (28889327/31250000 : ℝ)) (σ := (992684993/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (131371157/139171255 : ℝ) ^ p + (137410547/139171255 : ℝ) ^ p := by
    exact cert_lt (x := (131371157/139171255 : ℝ)) (y := (137410547/139171255 : ℝ)) (X := (12914842394619/50000000000000 : ℝ)) (Y := (74170316193537/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (28889327/31250000 : ℝ)) (n' := (83502753/100000000 : ℝ)) (Ab := (394113471/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (184893863/200000000 : ℝ) ^ p + (496341401/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (184893863/200000000 : ℝ)) (y := (496341401/500000000 : ℝ)) (X := (7916070044923/50000000000000 : ℝ)) (Y := (84167876903227/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496341401/500000000 : ℝ) ^ p + (184893863/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496341401/500000000 : ℝ)) (y := (184893863/200000000 : ℝ)) (X := (84167876903227/100000000000000 : ℝ)) (Y := (7916070044923/50000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1917152117/1000000000 : ℝ)) (τ := (184893863/200000000 : ℝ)) (σ := (496341401/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (788238590/835040341 : ℝ) ^ p + (824476093/835040341 : ℝ) ^ p := by
    exact cert_lt (x := (788238590/835040341 : ℝ)) (y := (824476093/835040341 : ℝ)) (X := (516586851569/2000000000000 : ℝ)) (Y := (74170658380841/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (184893863/200000000 : ℝ)) (n' := (835040341/1000000000 : ℝ)) (Ab := (78823859/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231117447/250000000 : ℝ) ^ p + (496341353/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (231117447/250000000 : ℝ)) (y := (496341353/500000000 : ℝ)) (X := (3958082549497/25000000000000 : ℝ)) (Y := (42083842937709/50000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496341353/500000000 : ℝ) ^ p + (231117447/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496341353/500000000 : ℝ)) (y := (231117447/250000000 : ℝ)) (X := (42083842937709/50000000000000 : ℝ)) (Y := (3958082549497/25000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (958576247/500000000 : ℝ)) (τ := (231117447/250000000 : ℝ)) (σ := (496341353/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (788239098/835040899 : ℝ) ^ p + (824476651/835040899 : ℝ) ^ p := by
    exact cert_lt (x := (788239098/835040899 : ℝ)) (y := (824476651/835040899 : ℝ)) (X := (2582932817783/10000000000000 : ℝ)) (Y := (1158916770079/1562500000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231117447/250000000 : ℝ)) (n' := (835040899/1000000000 : ℝ)) (Ab := (394119549/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (924469809/1000000000 : ℝ) ^ p + (496341351/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924469809/1000000000 : ℝ)) (y := (496341351/500000000 : ℝ)) (X := (7916169319179/50000000000000 : ℝ)) (Y := (16833535583187/20000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496341351/500000000 : ℝ) ^ p + (924469809/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496341351/500000000 : ℝ)) (y := (924469809/1000000000 : ℝ)) (X := (16833535583187/20000000000000 : ℝ)) (Y := (7916169319179/50000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1917152511/1000000000 : ℝ)) (τ := (924469809/1000000000 : ℝ)) (σ := (496341351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (197059780/208760231 : ℝ) ^ p + (206119169/208760231 : ℝ) ^ p := by
    exact cert_lt (x := (197059780/208760231 : ℝ)) (y := (206119169/208760231 : ℝ)) (X := (12914663474143/50000000000000 : ℝ)) (Y := (74170673952807/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (924469809/1000000000 : ℝ)) (n' := (208760231/250000000 : ℝ)) (Ab := (9852989/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1917152511/1000000000 : ℝ)) (τ := (924469809/1000000000 : ℝ)) (σ := (496341351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (924469809/1000000000 : ℝ)) (n' := (208760231/250000000 : ℝ)) (Ab := (9852989/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1917152511/1000000000 : ℝ)) (τ := (924469809/1000000000 : ℝ)) (σ := (496341351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (924469809/1000000000 : ℝ)) (n' := (208760231/250000000 : ℝ)) (Ab := (9852989/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1917152511/1000000000 : ℝ)) (τ := (924469809/1000000000 : ℝ)) (σ := (496341351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (924469809/1000000000 : ℝ)) (n' := (208760231/250000000 : ℝ)) (Ab := (9852989/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1917152511/1000000000 : ℝ)) (τ := (924469809/1000000000 : ℝ)) (σ := (496341351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (924469809/1000000000 : ℝ)) (n' := (208760231/250000000 : ℝ)) (Ab := (9852989/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1917152511/1000000000 : ℝ)) (τ := (924469809/1000000000 : ℝ)) (σ := (496341351/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1655438989/1806635828 : ℝ) ^ p + (449017895/451658957 : ℝ) ^ p := by
    exact cert_lt (x := (1655438989/1806635828 : ℝ)) (y := (449017895/451658957 : ℝ)) (X := (12858382805213/100000000000000 : ℝ)) (Y := (87141617408463/100000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1111422187/1193364172 : ℝ) ^ p + (295699981/298341043 : ℝ) ^ p := by
    exact cert_lt (x := (1111422187/1193364172 : ℝ)) (y := (295699981/298341043 : ℝ)) (X := (3766933996253/20000000000000 : ℝ)) (Y := (16233066131839/20000000000000 : ℝ)) 751 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496341351/500000000 : ℝ)) (U := (298341043/250000000 : ℝ)) (Ab := (1655438989/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (924469809/1000000000 : ℝ)) (σ := (496341351/500000000 : ℝ)) (Ab := (1111422187/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab078
