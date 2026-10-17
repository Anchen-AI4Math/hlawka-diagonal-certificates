import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 158, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab158 (p : ℝ) (hpa : (415/16 : ℝ) ≤ p) (hpb : p ≤ (831/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (103729304953/5664750000000 : ℝ) (1175457/125000000 : ℝ) (400000067977/2265900000000 : ℝ) (3033/2500 : ℝ) (243415371/125000000 : ℝ) (243407543/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (18662153/15625000 : ℝ)) ∧
    (∀ j i, if j = i then -(5597/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4701/10000 : ℝ)
      else (157/200 : ℝ) ≤ X j i ∧ X j i ≤ (11863/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (103729304953/5664750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1175457/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (463380591/500000000 : ℝ) ^ p + (497132557/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (463380591/500000000 : ℝ)) (y := (497132557/500000000 : ℝ)) (X := (3468454233811/25000000000000 : ℝ)) (Y := (2691443806301/3125000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497132557/500000000 : ℝ) ^ p + (463380591/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (497132557/500000000 : ℝ)) (y := (463380591/500000000 : ℝ)) (X := (2691443806301/3125000000000 : ℝ)) (Y := (3468454233811/25000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (240128287/125000000 : ℝ)) (τ := (463380591/500000000 : ℝ)) (σ := (497132557/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (792703621/835576366 : ℝ) ^ p + (413086355/417788183 : ℝ) ^ p := by
    exact cert_lt (x := (792703621/835576366 : ℝ)) (y := (413086355/417788183 : ℝ)) (X := (25465775607381/100000000000000 : ℝ)) (Y := (37267112846371/50000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (463380591/500000000 : ℝ)) (n' := (417788183/500000000 : ℝ)) (Ab := (792703621/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (18641631/20000000 : ℝ) ^ p + (496632071/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (18641631/20000000 : ℝ)) (y := (496632071/500000000 : ℝ)) (X := (16097419546121/100000000000000 : ℝ)) (Y := (10487824875171/12500000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496632071/500000000 : ℝ) ^ p + (18641631/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (496632071/500000000 : ℝ)) (y := (18641631/20000000 : ℝ)) (X := (10487824875171/12500000000000 : ℝ)) (Y := (16097419546121/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (481336423/250000000 : ℝ)) (τ := (18641631/20000000 : ℝ)) (σ := (496632071/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (199603571/210451055 : ℝ) ^ p + (208100141/210451055 : ℝ) ^ p := by
    exact cert_lt (x := (199603571/210451055 : ℝ)) (y := (208100141/210451055 : ℝ)) (X := (1265130728823/5000000000000 : ℝ)) (Y := (74697386797059/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (18641631/20000000 : ℝ)) (n' := (42090211/50000000 : ℝ)) (Ab := (199603571/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (932285517/1000000000 : ℝ) ^ p + (31038197/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (932285517/1000000000 : ℝ)) (y := (31038197/31250000 : ℝ)) (X := (1618914718823/10000000000000 : ℝ)) (Y := (83810870509127/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31038197/31250000 : ℝ) ^ p + (932285517/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31038197/31250000 : ℝ)) (y := (932285517/1000000000 : ℝ)) (X := (83810870509127/100000000000000 : ℝ)) (Y := (1618914718823/10000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1925507821/1000000000 : ℝ)) (τ := (932285517/1000000000 : ℝ)) (σ := (31038197/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (798632543/842042281 : ℝ) ^ p + (832638625/842042281 : ℝ) ^ p := by
    exact cert_lt (x := (798632543/842042281 : ℝ)) (y := (832638625/842042281 : ℝ)) (X := (25296418891357/100000000000000 : ℝ)) (Y := (74703582527201/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (932285517/1000000000 : ℝ)) (n' := (842042281/1000000000 : ℝ)) (Ab := (798632543/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (46614663/50000000 : ℝ) ^ p + (993220711/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46614663/50000000 : ℝ)) (y := (993220711/1000000000 : ℝ)) (X := (16192639237563/100000000000000 : ℝ)) (Y := (654745154791/781250000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993220711/1000000000 : ℝ) ^ p + (46614663/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (993220711/1000000000 : ℝ)) (y := (46614663/50000000 : ℝ)) (X := (654745154791/781250000000 : ℝ)) (Y := (16192639237563/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1925513971/1000000000 : ℝ)) (τ := (46614663/50000000 : ℝ)) (σ := (993220711/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (399320414/421025659 : ℝ) ^ p + (416323831/421025659 : ℝ) ^ p := by
    exact cert_lt (x := (399320414/421025659 : ℝ)) (y := (416323831/421025659 : ℝ)) (X := (12648091774789/50000000000000 : ℝ)) (Y := (74703817663151/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (46614663/50000000 : ℝ)) (n' := (421025659/500000000 : ℝ)) (Ab := (199660207/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (466146777/500000000 : ℝ) ^ p + (19864413/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (466146777/500000000 : ℝ)) (y := (19864413/20000000 : ℝ)) (X := (1012048240261/6250000000000 : ℝ)) (Y := (83807246148451/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (19864413/20000000 : ℝ) ^ p + (466146777/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (19864413/20000000 : ℝ)) (y := (466146777/500000000 : ℝ)) (X := (83807246148451/100000000000000 : ℝ)) (Y := (1012048240261/6250000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481378551/250000000 : ℝ)) (τ := (466146777/500000000 : ℝ)) (σ := (19864413/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (266213714/280683887 : ℝ) ^ p + (277549335/280683887 : ℝ) ^ p := by
    exact cert_lt (x := (266213714/280683887 : ℝ)) (y := (277549335/280683887 : ℝ)) (X := (25296174240761/100000000000000 : ℝ)) (Y := (18675956646917/25000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (466146777/500000000 : ℝ)) (n' := (842051661/1000000000 : ℝ)) (Ab := (399320571/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186458713/200000000 : ℝ) ^ p + (124152581/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (186458713/200000000 : ℝ)) (y := (124152581/125000000 : ℝ)) (X := (4048194201417/25000000000000 : ℝ)) (Y := (41903620883001/50000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124152581/125000000 : ℝ) ^ p + (186458713/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (124152581/125000000 : ℝ)) (y := (186458713/200000000 : ℝ)) (X := (41903620883001/50000000000000 : ℝ)) (Y := (4048194201417/25000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1925514213/1000000000 : ℝ)) (τ := (186458713/200000000 : ℝ)) (σ := (124152581/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (399320577/421025837 : ℝ) ^ p + (416324009/421025837 : ℝ) ^ p := by
    exact cert_lt (x := (399320577/421025837 : ℝ)) (y := (416324009/421025837 : ℝ)) (X := (25296173969483/100000000000000 : ℝ)) (Y := (14940765385183/20000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186458713/200000000 : ℝ)) (n' := (421025837/500000000 : ℝ)) (Ab := (399320577/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (466146783/500000000 : ℝ) ^ p + (124152581/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (466146783/500000000 : ℝ)) (y := (124152581/125000000 : ℝ)) (X := (16192777256713/100000000000000 : ℝ)) (Y := (41903620883001/50000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124152581/125000000 : ℝ) ^ p + (466146783/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124152581/125000000 : ℝ)) (y := (466146783/500000000 : ℝ)) (X := (41903620883001/50000000000000 : ℝ)) (Y := (16192777256713/100000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962757107/500000000 : ℝ)) (τ := (466146783/500000000 : ℝ)) (σ := (124152581/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (159728231/168410335 : ℝ) ^ p + (832648019/842051675 : ℝ) ^ p := by
    exact cert_lt (x := (159728231/168410335 : ℝ)) (y := (832648019/842051675 : ℝ)) (X := (25296174011887/100000000000000 : ℝ)) (Y := (37351913475967/50000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (466146783/500000000 : ℝ)) (n' := (33682067/40000000 : ℝ)) (Ab := (159728231/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962757107/500000000 : ℝ)) (τ := (466146783/500000000 : ℝ)) (σ := (124152581/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (466146783/500000000 : ℝ)) (n' := (33682067/40000000 : ℝ)) (Ab := (159728231/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962757107/500000000 : ℝ)) (τ := (466146783/500000000 : ℝ)) (σ := (124152581/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (466146783/500000000 : ℝ)) (n' := (33682067/40000000 : ℝ)) (Ab := (159728231/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962757107/500000000 : ℝ)) (τ := (466146783/500000000 : ℝ)) (σ := (124152581/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (466146783/500000000 : ℝ)) (n' := (33682067/40000000 : ℝ)) (Ab := (159728231/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962757107/500000000 : ℝ)) (τ := (466146783/500000000 : ℝ)) (σ := (124152581/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (52112375/56425694 : ℝ) ^ p + (224527319/225702776 : ℝ) ^ p := by
    exact cert_lt (x := (52112375/56425694 : ℝ)) (y := (224527319/225702776 : ℝ)) (X := (2536133619281/20000000000000 : ℝ)) (Y := (43659666077973/50000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1119369939/1194377792 : ℝ) ^ p + (148121767/149297224 : ℝ) ^ p := by
    exact cert_lt (x := (1119369939/1194377792 : ℝ)) (y := (148121767/149297224 : ℝ)) (X := (9278551381843/50000000000000 : ℝ)) (Y := (40721449042951/50000000000000 : ℝ)) 831 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124152581/125000000 : ℝ)) (U := (18662153/15625000 : ℝ)) (Ab := (416899/250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (466146783/500000000 : ℝ)) (σ := (124152581/125000000 : ℝ)) (Ab := (1119369939/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab158
