import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 4, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab004 (p : ℝ) (hpa : (105/4 : ℝ) ≤ p) (hpb : p ≤ (421/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (36345423001/2325750000000 : ℝ) (4011387/500000000 : ℝ) (160000027909/930300000000 : ℝ) (591/500 : ℝ) (487000531/250000000 : ℝ) (243484993/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (46220551/40000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10797/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(342/625 : ℝ)
      else (4063/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11467/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (36345423001/2325750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4011387/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (233472179/250000000 : ℝ) ^ p + (124144337/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (233472179/250000000 : ℝ)) (y := (124144337/125000000 : ℝ)) (X := (16534480482359/100000000000000 : ℝ)) (Y := (20866384302237/25000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (124144337/125000000 : ℝ) ^ p + (233472179/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124144337/125000000 : ℝ)) (y := (233472179/250000000 : ℝ)) (X := (20866384302237/25000000000000 : ℝ)) (Y := (16534480482359/100000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (481760853/250000000 : ℝ)) (τ := (233472179/250000000 : ℝ)) (σ := (124144337/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (814085500/862608627 : ℝ) ^ p + (284861951/287536209 : ℝ) ^ p := by
    exact cert_lt (x := (814085500/862608627 : ℝ)) (y := (284861951/287536209 : ℝ)) (X := (2179738254791/10000000000000 : ℝ)) (Y := (1221915910399/1562500000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (233472179/250000000 : ℝ)) (n' := (862608627/1000000000 : ℝ)) (Ab := (1628171/2000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (937390321/1000000000 : ℝ) ^ p + (992373181/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (937390321/1000000000 : ℝ)) (y := (992373181/1000000000 : ℝ)) (X := (4561390373041/25000000000000 : ℝ)) (Y := (81754456330117/100000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992373181/1000000000 : ℝ) ^ p + (937390321/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992373181/1000000000 : ℝ)) (y := (937390321/1000000000 : ℝ)) (X := (81754456330117/100000000000000 : ℝ)) (Y := (4561390373041/25000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (964881751/500000000 : ℝ)) (τ := (937390321/1000000000 : ℝ)) (σ := (992373181/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (272592010/288885263 : ℝ) ^ p + (286211005/288885263 : ℝ) ^ p := by
    exact cert_lt (x := (272592010/288885263 : ℝ)) (y := (286211005/288885263 : ℝ)) (X := (10853561350903/50000000000000 : ℝ)) (Y := (19573219663631/25000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (937390321/1000000000 : ℝ)) (n' := (866655789/1000000000 : ℝ)) (Ab := (81777603/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (937501157/1000000000 : ℝ) ^ p + (496173473/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (937501157/1000000000 : ℝ)) (y := (496173473/500000000 : ℝ)) (X := (9151205700099/50000000000000 : ℝ)) (Y := (16339521165871/20000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496173473/500000000 : ℝ) ^ p + (937501157/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496173473/500000000 : ℝ)) (y := (937501157/1000000000 : ℝ)) (X := (16339521165871/20000000000000 : ℝ)) (Y := (9151205700099/50000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1929848103/1000000000 : ℝ)) (τ := (937501157/1000000000 : ℝ)) (σ := (496173473/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (817892612/866783649 : ℝ) ^ p + (286253625/288927883 : ℝ) ^ p := by
    exact cert_lt (x := (817892612/866783649 : ℝ)) (y := (286253625/288927883 : ℝ)) (X := (10852141494433/50000000000000 : ℝ)) (Y := (39147859047979/50000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (937501157/1000000000 : ℝ)) (n' := (866783649/1000000000 : ℝ)) (Ab := (204473153/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (234376161/250000000 : ℝ) ^ p + (992346119/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (234376161/250000000 : ℝ)) (y := (992346119/1000000000 : ℝ)) (X := (18304202711251/100000000000000 : ℝ)) (Y := (40847907181133/50000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992346119/1000000000 : ℝ) ^ p + (234376161/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992346119/1000000000 : ℝ)) (y := (234376161/250000000 : ℝ)) (X := (40847907181133/50000000000000 : ℝ)) (Y := (18304202711251/100000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1929850763/1000000000 : ℝ)) (τ := (234376161/250000000 : ℝ)) (σ := (992346119/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (102237035/108348459 : ℝ) ^ p + (143127483/144464612 : ℝ) ^ p := by
    exact cert_lt (x := (102237035/108348459 : ℝ)) (y := (143127483/144464612 : ℝ)) (X := (10852096777999/50000000000000 : ℝ)) (Y := (15659161484889/20000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (234376161/250000000 : ℝ)) (n' := (108348459/125000000 : ℝ)) (Ab := (20447407/25000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (468752377/500000000 : ℝ) ^ p + (992346093/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468752377/500000000 : ℝ)) (y := (992346093/1000000000 : ℝ)) (X := (1830425922223/10000000000000 : ℝ)) (Y := (4084787902053/5000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992346093/1000000000 : ℝ) ^ p + (468752377/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992346093/1000000000 : ℝ)) (y := (468752377/500000000 : ℝ)) (X := (4084787902053/5000000000000 : ℝ)) (Y := (1830425922223/10000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1929850847/1000000000 : ℝ)) (τ := (468752377/500000000 : ℝ)) (σ := (992346093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (817896396/866787799 : ℝ) ^ p + (858765025/866787799 : ℝ) ^ p := by
    exact cert_lt (x := (817896396/866787799 : ℝ)) (y := (858765025/866787799 : ℝ)) (X := (10852095438581/50000000000000 : ℝ)) (Y := (39147905122199/50000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (468752377/500000000 : ℝ)) (n' := (866787799/1000000000 : ℝ)) (Ab := (204474099/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (937504757/1000000000 : ℝ) ^ p + (248086523/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (937504757/1000000000 : ℝ)) (y := (248086523/250000000 : ℝ)) (X := (18304260763441/100000000000000 : ℝ)) (Y := (4084787793743/5000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248086523/250000000 : ℝ) ^ p + (937504757/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248086523/250000000 : ℝ)) (y := (937504757/1000000000 : ℝ)) (X := (4084787793743/5000000000000 : ℝ)) (Y := (18304260763441/100000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1929850849/1000000000 : ℝ)) (τ := (937504757/1000000000 : ℝ)) (σ := (248086523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (817896399/866787802 : ℝ) ^ p + (429382514/433393901 : ℝ) ^ p := by
    exact cert_lt (x := (817896399/866787802 : ℝ)) (y := (429382514/433393901 : ℝ)) (X := (5426047748829/25000000000000 : ℝ)) (Y := (78295810311011/100000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (937504757/1000000000 : ℝ)) (n' := (433393901/500000000 : ℝ)) (Ab := (817896399/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1929850849/1000000000 : ℝ)) (τ := (937504757/1000000000 : ℝ)) (σ := (248086523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (937504757/1000000000 : ℝ)) (n' := (433393901/500000000 : ℝ)) (Ab := (817896399/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1929850849/1000000000 : ℝ)) (τ := (937504757/1000000000 : ℝ)) (σ := (248086523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (937504757/1000000000 : ℝ)) (n' := (433393901/500000000 : ℝ)) (Ab := (817896399/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1929850849/1000000000 : ℝ)) (τ := (937504757/1000000000 : ℝ)) (σ := (248086523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (937504757/1000000000 : ℝ)) (n' := (433393901/500000000 : ℝ)) (Ab := (817896399/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1929850849/1000000000 : ℝ)) (τ := (937504757/1000000000 : ℝ)) (σ := (248086523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (937504757/1000000000 : ℝ)) (n' := (433393901/500000000 : ℝ)) (Ab := (817896399/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1929850849/1000000000 : ℝ)) (τ := (937504757/1000000000 : ℝ)) (σ := (248086523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1695105044/1844486225 : ℝ) ^ p + (1836463451/1844486225 : ℝ) ^ p := by
    exact cert_lt (x := (1695105044/1844486225 : ℝ)) (y := (1836463451/1844486225 : ℝ)) (X := (10836500991147/100000000000000 : ℝ)) (Y := (89163499335789/100000000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1079653286/1155513775 : ℝ) ^ p + (1147491001/1155513775 : ℝ) ^ p := by
    exact cert_lt (x := (1079653286/1155513775 : ℝ)) (y := (1147491001/1155513775 : ℝ)) (X := (3350062380933/20000000000000 : ℝ)) (Y := (133199501643/160000000000 : ℝ)) 421 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248086523/250000000 : ℝ)) (U := (46220551/40000000 : ℝ)) (Ab := (423776261/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (937504757/1000000000 : ℝ)) (σ := (248086523/250000000 : ℝ)) (Ab := (539826643/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab004
