import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 35, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab035 (p : ℝ) (hpa : (451/16 : ℝ) ≤ p) (hpb : p ≤ (113/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (180083365277/12487062500000 : ℝ) (3695157/500000000 : ℝ) (3200000599379/19979300000000 : ℝ) (591/500 : ℝ) (487881191/250000000 : ℝ) (487854649/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (18074213/15625000 : ℝ)) ∧
    (∀ j i, if j = i then -(2171/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(693/1250 : ℝ)
      else (41/50 : ℝ) ≤ X j i ∧ X j i ≤ (2871/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (180083365277/12487062500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3695157/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (187728799/200000000 : ℝ) ^ p + (496772903/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (187728799/200000000 : ℝ)) (y := (496772903/500000000 : ℝ)) (X := (8358350929443/50000000000000 : ℝ)) (Y := (41641658859799/50000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496772903/500000000 : ℝ) ^ p + (187728799/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496772903/500000000 : ℝ)) (y := (187728799/200000000 : ℝ)) (X := (41641658859799/50000000000000 : ℝ)) (Y := (8358350929443/50000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1932189801/1000000000 : ℝ)) (τ := (187728799/200000000 : ℝ)) (σ := (496772903/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (273533174/288832359 : ℝ) ^ p + (95456307/96277453 : ℝ) ^ p := by
    exact cert_lt (x := (273533174/288832359 : ℝ)) (y := (95456307/96277453 : ℝ)) (X := (10746262808467/50000000000000 : ℝ)) (Y := (15701495112857/20000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (187728799/200000000 : ℝ)) (n' := (866497077/1000000000 : ℝ)) (Ab := (410299761/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (235495367/250000000 : ℝ) ^ p + (31024799/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (235495367/250000000 : ℝ)) (y := (31024799/31250000 : ℝ)) (X := (1154985824281/6250000000000 : ℝ)) (Y := (16304048926461/20000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (31024799/31250000 : ℝ) ^ p + (235495367/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (31024799/31250000 : ℝ)) (y := (235495367/250000000 : ℝ)) (X := (16304048926461/20000000000000 : ℝ)) (Y := (1154985824281/6250000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (483693759/250000000 : ℝ)) (τ := (235495367/250000000 : ℝ)) (σ := (31024799/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (824112323/870326990 : ℝ) ^ p + (431468338/435163495 : ℝ) ^ p := by
    exact cert_lt (x := (824112323/870326990 : ℝ)) (y := (431468338/435163495 : ℝ)) (X := (21408526132353/100000000000000 : ℝ)) (Y := (19647868717131/25000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (235495367/250000000 : ℝ)) (n' := (87032699/100000000 : ℝ)) (Ab := (824112323/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (117759719/125000000 : ℝ) ^ p + (39710821/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (117759719/125000000 : ℝ)) (y := (39710821/40000000 : ℝ)) (X := (92666044627/500000000000 : ℝ)) (Y := (81466809528627/100000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (39710821/40000000 : ℝ) ^ p + (117759719/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (39710821/40000000 : ℝ)) (y := (117759719/125000000 : ℝ)) (X := (81466809528627/100000000000000 : ℝ)) (Y := (92666044627/500000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1934848277/1000000000 : ℝ)) (τ := (117759719/125000000 : ℝ)) (σ := (39710821/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (117744782/124348183 : ℝ) ^ p + (863046967/870437281 : ℝ) ^ p := by
    exact cert_lt (x := (117744782/124348183 : ℝ)) (y := (863046967/870437281 : ℝ)) (X := (2140611690119/10000000000000 : ℝ)) (Y := (4912117759141/6250000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (117759719/125000000 : ℝ)) (n' := (870437281/1000000000 : ℝ)) (Ab := (412106737/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (942080513/1000000000 : ℝ) ^ p + (992769863/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (942080513/1000000000 : ℝ)) (y := (992769863/1000000000 : ℝ)) (X := (1853474342251/10000000000000 : ℝ)) (Y := (16293054979269/20000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992769863/1000000000 : ℝ) ^ p + (942080513/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992769863/1000000000 : ℝ)) (y := (942080513/1000000000 : ℝ)) (X := (16293054979269/20000000000000 : ℝ)) (Y := (1853474342251/10000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (241856297/125000000 : ℝ)) (τ := (942080513/1000000000 : ℝ)) (σ := (992769863/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (824216374/870440443 : ℝ) ^ p + (863050129/870440443 : ℝ) ^ p := by
    exact cert_lt (x := (824216374/870440443 : ℝ)) (y := (863050129/870440443 : ℝ)) (X := (21406047871853/100000000000000 : ℝ)) (Y := (78593953211357/100000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (942080513/1000000000 : ℝ)) (n' := (870440443/1000000000 : ℝ)) (Ab := (412108187/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (942080593/1000000000 : ℝ) ^ p + (248192461/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (942080593/1000000000 : ℝ)) (y := (248192461/250000000 : ℝ)) (X := (3706957577281/20000000000000 : ℝ)) (Y := (81465230851419/100000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248192461/250000000 : ℝ) ^ p + (942080593/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248192461/250000000 : ℝ)) (y := (942080593/1000000000 : ℝ)) (X := (81465230851419/100000000000000 : ℝ)) (Y := (3706957577281/20000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1934850437/1000000000 : ℝ)) (τ := (942080593/1000000000 : ℝ)) (σ := (248192461/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (824216458/870440535 : ℝ) ^ p + (95894469/96715615 : ℝ) ^ p := by
    exact cert_lt (x := (824216458/870440535 : ℝ)) (y := (95894469/96715615 : ℝ)) (X := (4281209117367/20000000000000 : ℝ)) (Y := (39296977610417/50000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (942080593/1000000000 : ℝ)) (n' := (174088107/200000000 : ℝ)) (Ab := (412108229/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (471040297/500000000 : ℝ) ^ p + (248192461/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (471040297/500000000 : ℝ)) (y := (248192461/250000000 : ℝ)) (X := (4633697110551/25000000000000 : ℝ)) (Y := (81465230851419/100000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248192461/250000000 : ℝ) ^ p + (471040297/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248192461/250000000 : ℝ)) (y := (471040297/500000000 : ℝ)) (X := (81465230851419/100000000000000 : ℝ)) (Y := (4633697110551/25000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (967425219/500000000 : ℝ)) (τ := (471040297/500000000 : ℝ)) (σ := (248192461/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (824216459/870440536 : ℝ) ^ p + (431525111/435220268 : ℝ) ^ p := by
    exact cert_lt (x := (824216459/870440536 : ℝ)) (y := (431525111/435220268 : ℝ)) (X := (10703022812899/50000000000000 : ℝ)) (Y := (78593955242677/100000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (471040297/500000000 : ℝ)) (n' := (108805067/125000000 : ℝ)) (Ab := (824216459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (967425219/500000000 : ℝ)) (τ := (471040297/500000000 : ℝ)) (σ := (248192461/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (471040297/500000000 : ℝ)) (n' := (108805067/125000000 : ℝ)) (Ab := (824216459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (967425219/500000000 : ℝ)) (τ := (471040297/500000000 : ℝ)) (σ := (248192461/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (471040297/500000000 : ℝ)) (n' := (108805067/125000000 : ℝ)) (Ab := (824216459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (967425219/500000000 : ℝ)) (τ := (471040297/500000000 : ℝ)) (σ := (248192461/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (471040297/500000000 : ℝ)) (n' := (108805067/125000000 : ℝ)) (Ab := (824216459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (967425219/500000000 : ℝ)) (τ := (471040297/500000000 : ℝ)) (σ := (248192461/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (471040297/500000000 : ℝ)) (n' := (108805067/125000000 : ℝ)) (Ab := (824216459/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (967425219/500000000 : ℝ)) (τ := (471040297/500000000 : ℝ)) (σ := (248192461/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1703208359/1843250368 : ℝ) ^ p + (917930027/921625184 : ℝ) ^ p := by
    exact cert_lt (x := (1703208359/1843250368 : ℝ)) (y := (917930027/921625184 : ℝ)) (X := (5364478182251/50000000000000 : ℝ)) (Y := (22317760991621/25000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (16959663/18074213 : ℝ) ^ p + (574679659/578374816 : ℝ) ^ p := by
    exact cert_lt (x := (16959663/18074213 : ℝ)) (y := (574679659/578374816 : ℝ)) (X := (8280917979217/50000000000000 : ℝ)) (Y := (83438164556499/100000000000000 : ℝ)) 113 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248192461/250000000 : ℝ)) (U := (18074213/15625000 : ℝ)) (Ab := (1703208359/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (471040297/500000000 : ℝ)) (σ := (248192461/250000000 : ℝ)) (Ab := (16959663/15625000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab035
