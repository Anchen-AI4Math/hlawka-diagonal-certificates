import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 78, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab078 (p : ℝ) (hpa : (247/8 : ℝ) ≤ p) (hpb : p ≤ (495/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (712568950049/54710500000000 : ℝ) (666003/100000000 : ℝ) (1600000328263/10942100000000 : ℝ) (591/500 : ℝ) (488922183/250000000 : ℝ) (977800017/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1158316407/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(437/400 : ℝ) ≤ X j i ∧ X j i ≤ -(1407/2500 : ℝ)
      else (4143/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5753/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (712568950049/54710500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (666003/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (29506651/31250000 : ℝ) ^ p + (198804279/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (29506651/31250000 : ℝ)) (y := (198804279/200000000 : ℝ)) (X := (4233162948699/25000000000000 : ℝ)) (Y := (162240957709/195312500000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198804279/200000000 : ℝ) ^ p + (29506651/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (198804279/200000000 : ℝ)) (y := (29506651/31250000 : ℝ)) (X := (162240957709/195312500000 : ℝ)) (Y := (4233162948699/25000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1938234227/1000000000 : ℝ)) (τ := (29506651/31250000 : ℝ)) (σ := (198804279/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (828278690/870947303 : ℝ) ^ p + (864287273/870947303 : ℝ) ^ p := by
    exact cert_lt (x := (828278690/870947303 : ℝ)) (y := (864287273/870947303 : ℝ)) (X := (10569546520869/50000000000000 : ℝ)) (Y := (19715227129707/25000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (29506651/31250000 : ℝ)) (n' := (870947303/1000000000 : ℝ)) (Ab := (82827869/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (947336617/1000000000 : ℝ) ^ p + (993309177/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (947336617/1000000000 : ℝ)) (y := (993309177/1000000000 : ℝ)) (X := (937718610167/5000000000000 : ℝ)) (Y := (20311411938703/25000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993309177/1000000000 : ℝ) ^ p + (947336617/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993309177/1000000000 : ℝ)) (y := (947336617/1000000000 : ℝ)) (X := (20311411938703/25000000000000 : ℝ)) (Y := (937718610167/5000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (970322897/500000000 : ℝ)) (τ := (947336617/1000000000 : ℝ)) (σ := (993309177/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (11712139/12316930 : ℝ) ^ p + (86784200/87450203 : ℝ) ^ p := by
    exact cert_lt (x := (11712139/12316930 : ℝ)) (y := (86784200/87450203 : ℝ)) (X := (21062636250499/100000000000000 : ℝ)) (Y := (4933585310569/6250000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (947336617/1000000000 : ℝ)) (n' := (87450203/100000000 : ℝ)) (Ab := (831561869/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (189483371/200000000 : ℝ) ^ p + (496644863/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (189483371/200000000 : ℝ)) (y := (496644863/500000000 : ℝ)) (X := (18803577769211/100000000000000 : ℝ)) (Y := (40598221021793/50000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496644863/500000000 : ℝ) ^ p + (189483371/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496644863/500000000 : ℝ)) (y := (189483371/200000000 : ℝ)) (X := (40598221021793/50000000000000 : ℝ)) (Y := (18803577769211/100000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1940706581/1000000000 : ℝ)) (τ := (189483371/200000000 : ℝ)) (σ := (496644863/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (415823027/437296592 : ℝ) ^ p + (433966577/437296592 : ℝ) ^ p := by
    exact cert_lt (x := (415823027/437296592 : ℝ)) (y := (433966577/437296592 : ℝ)) (X := (5265170723459/25000000000000 : ℝ)) (Y := (9867414788841/12500000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (189483371/200000000 : ℝ)) (n' := (27331037/31250000 : ℝ)) (Ab := (415823027/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (189483781/200000000 : ℝ) ^ p + (248322307/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (189483781/200000000 : ℝ)) (y := (248322307/250000000 : ℝ)) (X := (18804836557019/100000000000000 : ℝ)) (Y := (40597591309227/50000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248322307/250000000 : ℝ) ^ p + (189483781/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248322307/250000000 : ℝ)) (y := (189483781/200000000 : ℝ)) (X := (40597591309227/50000000000000 : ℝ)) (Y := (18804836557019/100000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1940708133/1000000000 : ℝ)) (τ := (189483781/200000000 : ℝ)) (σ := (248322307/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (831648205/874595513 : ℝ) ^ p + (867935483/874595513 : ℝ) ^ p := by
    exact cert_lt (x := (831648205/874595513 : ℝ)) (y := (867935483/874595513 : ℝ)) (X := (4212126607839/20000000000000 : ℝ)) (Y := (19734842053553/25000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (189483781/200000000 : ℝ)) (n' := (874595513/1000000000 : ℝ)) (Ab := (166329641/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (947418957/1000000000 : ℝ) ^ p + (1940018/1953125 : ℝ) ^ p := by
    exact cert_lt (x := (947418957/1000000000 : ℝ)) (y := (1940018/1953125 : ℝ)) (X := (9402434244153/50000000000000 : ℝ)) (Y := (81195152271093/100000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (1940018/1953125 : ℝ) ^ p + (947418957/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (1940018/1953125 : ℝ)) (y := (947418957/1000000000 : ℝ)) (X := (81195152271093/100000000000000 : ℝ)) (Y := (9402434244153/50000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1940708173/1000000000 : ℝ)) (τ := (947418957/1000000000 : ℝ)) (σ := (1940018/1953125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (831648259/874595572 : ℝ) ^ p + (433967771/437297786 : ℝ) ^ p := by
    exact cert_lt (x := (831648259/874595572 : ℝ)) (y := (433967771/437297786 : ℝ)) (X := (10530315695873/50000000000000 : ℝ)) (Y := (39469684739201/50000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (947418957/1000000000 : ℝ)) (n' := (218648893/250000000 : ℝ)) (Ab := (831648259/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (947418959/1000000000 : ℝ) ^ p + (198657843/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (947418959/1000000000 : ℝ)) (y := (198657843/200000000 : ℝ)) (X := (9402434858217/50000000000000 : ℝ)) (Y := (81195149742147/100000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198657843/200000000 : ℝ) ^ p + (947418959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198657843/200000000 : ℝ)) (y := (947418959/1000000000 : ℝ)) (X := (81195149742147/100000000000000 : ℝ)) (Y := (9402434858217/50000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (970354087/500000000 : ℝ)) (τ := (947418959/1000000000 : ℝ)) (σ := (198657843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (831648262/874595575 : ℝ) ^ p + (173587109/174919115 : ℝ) ^ p := by
    exact cert_lt (x := (831648262/874595575 : ℝ)) (y := (173587109/174919115 : ℝ)) (X := (10530315753581/50000000000000 : ℝ)) (Y := (78939369542683/100000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (947418959/1000000000 : ℝ)) (n' := (34983823/40000000 : ℝ)) (Ab := (415824131/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (970354087/500000000 : ℝ)) (τ := (947418959/1000000000 : ℝ)) (σ := (198657843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (947418959/1000000000 : ℝ)) (n' := (34983823/40000000 : ℝ)) (Ab := (415824131/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (970354087/500000000 : ℝ)) (τ := (947418959/1000000000 : ℝ)) (σ := (198657843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (947418959/1000000000 : ℝ)) (n' := (34983823/40000000 : ℝ)) (Ab := (415824131/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (970354087/500000000 : ℝ)) (τ := (947418959/1000000000 : ℝ)) (σ := (198657843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (947418959/1000000000 : ℝ)) (n' := (34983823/40000000 : ℝ)) (Ab := (415824131/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (970354087/500000000 : ℝ)) (τ := (947418959/1000000000 : ℝ)) (σ := (198657843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (947418959/1000000000 : ℝ)) (n' := (34983823/40000000 : ℝ)) (Ab := (415824131/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (970354087/500000000 : ℝ)) (τ := (947418959/1000000000 : ℝ)) (σ := (198657843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (570942344/613894531 : ℝ) ^ p + (611674521/613894531 : ℝ) ^ p := by
    exact cert_lt (x := (570942344/613894531 : ℝ)) (y := (611674521/613894531 : ℝ)) (X := (10602835235201/100000000000000 : ℝ)) (Y := (11174645627813/12500000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (121381788/128701823 : ℝ) ^ p + (383885459/386105469 : ℝ) ^ p := by
    exact cert_lt (x := (121381788/128701823 : ℝ)) (y := (383885459/386105469 : ℝ)) (X := (16338916001803/100000000000000 : ℝ)) (Y := (41830542250739/50000000000000 : ℝ)) 495 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198657843/200000000 : ℝ)) (U := (1158316407/1000000000 : ℝ)) (Ab := (214103379/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (947418959/1000000000 : ℝ)) (σ := (198657843/200000000 : ℝ)) (Ab := (273109023/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab078
