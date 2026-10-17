import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 155, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab155 (p : ℝ) (hpa : (827/32 : ℝ) ≤ p) (hpb : p ≤ (207/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2075451273461/112885500000000 : ℝ) (9442619/1000000000 : ℝ) (4000000677313/22577100000000 : ℝ) (3033/2500 : ℝ) (973567327/500000000 : ℝ) (973535791/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194340197/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11191/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4697/10000 : ℝ)
      else (1569/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11863/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2075451273461/112885500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9442619/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (926483059/1000000000 : ℝ) ^ p + (994248329/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926483059/1000000000 : ℝ)) (y := (994248329/1000000000 : ℝ)) (X := (6932499786259/50000000000000 : ℝ)) (Y := (86135019206899/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994248329/1000000000 : ℝ) ^ p + (926483059/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994248329/1000000000 : ℝ)) (y := (926483059/1000000000 : ℝ)) (X := (86135019206899/100000000000000 : ℝ)) (Y := (6932499786259/50000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (480182847/250000000 : ℝ)) (τ := (926483059/1000000000 : ℝ)) (σ := (994248329/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (792335355/835324111 : ℝ) ^ p + (825881492/835324111 : ℝ) ^ p := by
    exact cert_lt (x := (792335355/835324111 : ℝ)) (y := (825881492/835324111 : ℝ)) (X := (5096860066533/20000000000000 : ℝ)) (Y := (74515700733839/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (926483059/1000000000 : ℝ)) (n' := (835324111/1000000000 : ℝ)) (Ab := (158467071/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931816079/1000000000 : ℝ) ^ p + (993245537/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931816079/1000000000 : ℝ)) (y := (993245537/1000000000 : ℝ)) (X := (16084920892547/100000000000000 : ℝ)) (Y := (8391509718339/10000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993245537/1000000000 : ℝ) ^ p + (931816079/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993245537/1000000000 : ℝ)) (y := (931816079/1000000000 : ℝ)) (X := (8391509718339/10000000000000 : ℝ)) (Y := (16084920892547/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (120316351/62500000 : ℝ)) (τ := (931816079/1000000000 : ℝ)) (σ := (993245537/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (798060265/841569281 : ℝ) ^ p + (832126662/841569281 : ℝ) ^ p := by
    exact cert_lt (x := (798060265/841569281 : ℝ)) (y := (832126662/841569281 : ℝ)) (X := (25320537855757/100000000000000 : ℝ)) (Y := (74679463677341/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931816079/1000000000 : ℝ)) (n' := (841569281/1000000000 : ℝ)) (Ab := (159612053/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (466010763/500000000 : ℝ) ^ p + (993203423/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (466010763/500000000 : ℝ)) (y := (993203423/1000000000 : ℝ)) (X := (4044234060529/25000000000000 : ℝ)) (Y := (83823081613459/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993203423/1000000000 : ℝ) ^ p + (466010763/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993203423/1000000000 : ℝ)) (y := (466010763/500000000 : ℝ)) (X := (83823081613459/100000000000000 : ℝ)) (Y := (4044234060529/25000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1925224949/1000000000 : ℝ)) (τ := (466010763/500000000 : ℝ)) (σ := (993203423/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (798280132/841809165 : ℝ) ^ p + (832366546/841809165 : ℝ) ^ p := by
    exact cert_lt (x := (798280132/841809165 : ℝ)) (y := (832366546/841809165 : ℝ)) (X := (12657144403399/50000000000000 : ℝ)) (Y := (597485699019/800000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (466010763/500000000 : ℝ)) (n' := (168361833/200000000 : ℝ)) (Ab := (199570033/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (932029363/1000000000 : ℝ) ^ p + (993201811/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (932029363/1000000000 : ℝ)) (y := (993201811/1000000000 : ℝ)) (X := (4045114067201/25000000000000 : ℝ)) (Y := (20954890364093/25000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993201811/1000000000 : ℝ) ^ p + (932029363/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993201811/1000000000 : ℝ)) (y := (932029363/1000000000 : ℝ)) (X := (20954890364093/25000000000000 : ℝ)) (Y := (4045114067201/25000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (962615587/500000000 : ℝ)) (τ := (932029363/1000000000 : ℝ)) (σ := (993201811/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (399144259/420909157 : ℝ) ^ p + (832375695/841818314 : ℝ) ^ p := by
    exact cert_lt (x := (399144259/420909157 : ℝ)) (y := (832375695/841818314 : ℝ)) (X := (12657025464183/50000000000000 : ℝ)) (Y := (37342975318831/50000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (932029363/1000000000 : ℝ)) (n' := (420909157/500000000 : ℝ)) (Ab := (399144259/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (466014831/500000000 : ℝ) ^ p + (3972807/4000000 : ℝ) ^ p := by
    exact cert_lt (x := (466014831/500000000 : ℝ)) (y := (3972807/4000000 : ℝ)) (X := (1618059058069/10000000000000 : ℝ)) (Y := (41909714126113/50000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (3972807/4000000 : ℝ) ^ p + (466014831/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (3972807/4000000 : ℝ)) (y := (466014831/500000000 : ℝ)) (X := (41909714126113/50000000000000 : ℝ)) (Y := (1618059058069/10000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481307853/250000000 : ℝ)) (τ := (466014831/500000000 : ℝ)) (σ := (3972807/4000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (266096279/280606221 : ℝ) ^ p + (832376044/841818663 : ℝ) ^ p := by
    exact cert_lt (x := (266096279/280606221 : ℝ)) (y := (832376044/841818663 : ℝ)) (X := (25314041120469/100000000000000 : ℝ)) (Y := (74685959726309/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (466014831/500000000 : ℝ)) (n' := (841818663/1000000000 : ℝ)) (Ab := (798288837/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (466014837/500000000 : ℝ) ^ p + (993201747/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (466014837/500000000 : ℝ)) (y := (993201747/1000000000 : ℝ)) (X := (4045148992789/25000000000000 : ℝ)) (Y := (83819421701207/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993201747/1000000000 : ℝ) ^ p + (466014837/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993201747/1000000000 : ℝ)) (y := (466014837/500000000 : ℝ)) (X := (83819421701207/100000000000000 : ℝ)) (Y := (4045148992789/25000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1925231421/1000000000 : ℝ)) (τ := (466014837/500000000 : ℝ)) (σ := (993201747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (798288850/841818677 : ℝ) ^ p + (832376058/841818677 : ℝ) ^ p := by
    exact cert_lt (x := (798288850/841818677 : ℝ)) (y := (832376058/841818677 : ℝ)) (X := (25314040893951/100000000000000 : ℝ)) (Y := (4667872505681/6250000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (466014837/500000000 : ℝ)) (n' := (841818677/1000000000 : ℝ)) (Ab := (15965777/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1925231421/1000000000 : ℝ)) (τ := (466014837/500000000 : ℝ)) (σ := (993201747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (466014837/500000000 : ℝ)) (n' := (841818677/1000000000 : ℝ)) (Ab := (15965777/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1925231421/1000000000 : ℝ)) (τ := (466014837/500000000 : ℝ)) (σ := (993201747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (466014837/500000000 : ℝ)) (n' := (841818677/1000000000 : ℝ)) (Ab := (15965777/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1925231421/1000000000 : ℝ)) (τ := (466014837/500000000 : ℝ)) (σ := (993201747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (466014837/500000000 : ℝ)) (n' := (841818677/1000000000 : ℝ)) (Ab := (15965777/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1925231421/1000000000 : ℝ)) (τ := (466014837/500000000 : ℝ)) (σ := (993201747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (466014837/500000000 : ℝ)) (n' := (841818677/1000000000 : ℝ)) (Ab := (15965777/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1925231421/1000000000 : ℝ)) (τ := (466014837/500000000 : ℝ)) (σ := (993201747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (555726959/601886601 : ℝ) ^ p + (1796217184/1805659803 : ℝ) ^ p := by
    exact cert_lt (x := (555726959/601886601 : ℝ)) (y := (1796217184/1805659803 : ℝ)) (X := (12686686114969/100000000000000 : ℝ)) (Y := (87313314173367/100000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1119093754/1194340197 : ℝ) ^ p + (1184897578/1194340197 : ℝ) ^ p := by
    exact cert_lt (x := (1119093754/1194340197 : ℝ)) (y := (1184897578/1194340197 : ℝ)) (X := (18566570177417/100000000000000 : ℝ)) (Y := (8143343028273/10000000000000 : ℝ)) 207 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993201747/1000000000 : ℝ)) (U := (1194340197/1000000000 : ℝ)) (Ab := (1667180877/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (466014837/500000000 : ℝ)) (σ := (993201747/1000000000 : ℝ)) (Ab := (559546877/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab155
