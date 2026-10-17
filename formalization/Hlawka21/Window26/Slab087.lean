import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 87, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab087 (p : ℝ) (hpa : (503/16 : ℝ) ≤ p) (hpb : p ≤ (63/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (355555274653/27853625000000 : ℝ) (815607/125000000 : ℝ) (3200000668487/22282900000000 : ℝ) (591/500 : ℝ) (195647133/100000000 : ℝ) (97819287/100000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (289655913/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5469/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(5643/10000 : ℝ)
      else (4151/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1151/1000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (355555274653/27853625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (815607/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (59078323/62500000 : ℝ) ^ p + (124264049/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (59078323/62500000 : ℝ)) (y := (124264049/125000000 : ℝ)) (X := (16973306722757/100000000000000 : ℝ)) (Y := (16605343020211/20000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124264049/125000000 : ℝ) ^ p + (59078323/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (124264049/125000000 : ℝ)) (y := (59078323/62500000 : ℝ)) (X := (16605343020211/20000000000000 : ℝ)) (Y := (16973306722757/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (48484139/25000000 : ℝ)) (τ := (59078323/62500000 : ℝ)) (σ := (124264049/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (414859783/435883094 : ℝ) ^ p + (216310333/217941547 : ℝ) ^ p := by
    exact cert_lt (x := (414859783/435883094 : ℝ)) (y := (216310333/217941547 : ℝ)) (X := (21073481628267/100000000000000 : ℝ)) (Y := (9865814961481/12500000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (59078323/62500000 : ℝ)) (n' := (217941547/250000000 : ℝ)) (Ab := (414859783/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (94833457/100000000 : ℝ) ^ p + (993408327/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (94833457/100000000 : ℝ)) (y := (993408327/1000000000 : ℝ)) (X := (940285736797/5000000000000 : ℝ)) (Y := (20298576556437/25000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993408327/1000000000 : ℝ) ^ p + (94833457/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993408327/1000000000 : ℝ)) (y := (94833457/100000000 : ℝ)) (X := (20298576556437/25000000000000 : ℝ)) (Y := (940285736797/5000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1941742897/1000000000 : ℝ)) (τ := (94833457/100000000 : ℝ)) (σ := (993408327/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (832957390/875267189 : ℝ) ^ p + (868742333/875267189 : ℝ) ^ p := by
    exact cert_lt (x := (832957390/875267189 : ℝ)) (y := (868742333/875267189 : ℝ)) (X := (20998453970059/100000000000000 : ℝ)) (Y := (39500773430007/50000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (94833457/100000000 : ℝ)) (n' := (875267189/1000000000 : ℝ)) (Ab := (83295739/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (474205971/500000000 : ℝ) ^ p + (496694763/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (474205971/500000000 : ℝ)) (y := (496694763/500000000 : ℝ)) (X := (3770821113551/20000000000000 : ℝ)) (Y := (20286478824663/25000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496694763/500000000 : ℝ) ^ p + (474205971/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496694763/500000000 : ℝ)) (y := (474205971/500000000 : ℝ)) (X := (20286478824663/25000000000000 : ℝ)) (Y := (3770821113551/20000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (485450367/250000000 : ℝ)) (τ := (474205971/500000000 : ℝ)) (σ := (496694763/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (833038550/875354951 : ℝ) ^ p + (868830095/875354951 : ℝ) ^ p := by
    exact cert_lt (x := (833038550/875354951 : ℝ)) (y := (868830095/875354951 : ℝ)) (X := (20996580443811/100000000000000 : ℝ)) (Y := (39501710395089/50000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (474205971/500000000 : ℝ)) (n' := (875354951/1000000000 : ℝ)) (Ab := (16660771/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (474206937/500000000 : ℝ) ^ p + (1940213/1953125 : ℝ) ^ p := by
    exact cert_lt (x := (474206937/500000000 : ℝ)) (y := (1940213/1953125 : ℝ)) (X := (11784572151/62500000000 : ℝ)) (Y := (81144705947661/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (1940213/1953125 : ℝ) ^ p + (474206937/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (1940213/1953125 : ℝ)) (y := (474206937/500000000 : ℝ)) (X := (81144705947661/100000000000000 : ℝ)) (Y := (11784572151/62500000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (194180293/100000000 : ℝ)) (τ := (474206937/500000000 : ℝ)) (σ := (1940213/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (833040577/875357143 : ℝ) ^ p + (868832287/875357143 : ℝ) ^ p := by
    exact cert_lt (x := (833040577/875357143 : ℝ)) (y := (868832287/875357143 : ℝ)) (X := (10498266786779/50000000000000 : ℝ)) (Y := (79003467590401/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (474206937/500000000 : ℝ)) (n' := (875357143/1000000000 : ℝ)) (Ab := (833040577/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (474206961/500000000 : ℝ) ^ p + (248347261/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (474206961/500000000 : ℝ)) (y := (248347261/250000000 : ℝ)) (X := (9427672750767/50000000000000 : ℝ)) (Y := (81144675070843/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248347261/250000000 : ℝ) ^ p + (474206961/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248347261/250000000 : ℝ)) (y := (474206961/500000000 : ℝ)) (X := (81144675070843/100000000000000 : ℝ)) (Y := (9427672750767/50000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (970901483/500000000 : ℝ)) (τ := (474206961/500000000 : ℝ)) (σ := (248347261/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (833040627/875357197 : ℝ) ^ p + (66833257/67335169 : ℝ) ^ p := by
    exact cert_lt (x := (833040627/875357197 : ℝ)) (y := (66833257/67335169 : ℝ)) (X := (4199306494069/20000000000000 : ℝ)) (Y := (79003468743323/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (474206961/500000000 : ℝ)) (n' := (875357197/1000000000 : ℝ)) (Ab := (833040627/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (948413923/1000000000 : ℝ) ^ p + (248347261/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (948413923/1000000000 : ℝ)) (y := (248347261/250000000 : ℝ)) (X := (18855346127783/100000000000000 : ℝ)) (Y := (81144675070843/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248347261/250000000 : ℝ) ^ p + (948413923/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248347261/250000000 : ℝ)) (y := (948413923/1000000000 : ℝ)) (X := (81144675070843/100000000000000 : ℝ)) (Y := (18855346127783/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1941802967/1000000000 : ℝ)) (τ := (948413923/1000000000 : ℝ)) (σ := (248347261/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (416520314/437678599 : ℝ) ^ p + (434416171/437678599 : ℝ) ^ p := by
    exact cert_lt (x := (416520314/437678599 : ℝ)) (y := (434416171/437678599 : ℝ)) (X := (10498266254363/50000000000000 : ℝ)) (Y := (39501734382337/50000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (948413923/1000000000 : ℝ)) (n' := (437678599/500000000 : ℝ)) (Ab := (208260157/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1941802967/1000000000 : ℝ)) (τ := (948413923/1000000000 : ℝ)) (σ := (248347261/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (948413923/1000000000 : ℝ)) (n' := (437678599/500000000 : ℝ)) (Ab := (208260157/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1941802967/1000000000 : ℝ)) (τ := (948413923/1000000000 : ℝ)) (σ := (248347261/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (948413923/1000000000 : ℝ)) (n' := (437678599/500000000 : ℝ)) (Ab := (208260157/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1941802967/1000000000 : ℝ)) (τ := (948413923/1000000000 : ℝ)) (σ := (248347261/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (948413923/1000000000 : ℝ)) (n' := (437678599/500000000 : ℝ)) (Ab := (208260157/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1941802967/1000000000 : ℝ)) (τ := (948413923/1000000000 : ℝ)) (σ := (248347261/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (948413923/1000000000 : ℝ)) (n' := (437678599/500000000 : ℝ)) (Ab := (208260157/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1941802967/1000000000 : ℝ)) (τ := (948413923/1000000000 : ℝ)) (σ := (248347261/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (428659925/460344087 : ℝ) ^ p + (50968097/51149343 : ℝ) ^ p := by
    exact cert_lt (x := (428659925/460344087 : ℝ)) (y := (50968097/51149343 : ℝ)) (X := (10579250660131/100000000000000 : ℝ)) (Y := (89420749551149/100000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (364593303/386207884 : ℝ) ^ p + (96008233/96551971 : ℝ) ^ p := by
    exact cert_lt (x := (364593303/386207884 : ℝ)) (y := (96008233/96551971 : ℝ)) (X := (8148504129177/50000000000000 : ℝ)) (Y := (41851496323503/50000000000000 : ℝ)) 63 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248347261/250000000 : ℝ)) (U := (289655913/250000000 : ℝ)) (Ab := (17146397/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (948413923/1000000000 : ℝ)) (σ := (248347261/250000000 : ℝ)) (Ab := (1093779909/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab087
