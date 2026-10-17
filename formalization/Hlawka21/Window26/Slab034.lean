import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 34, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab034 (p : ℝ) (hpa : (225/8 : ℝ) ≤ p) (hpb : p ≤ (451/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (28821260507/1993500000000 : ℝ) (3704589/500000000 : ℝ) (64000011961/398700000000 : ℝ) (591/500 : ℝ) (975709299/500000000 : ℝ) (975655981/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1156711181/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10853/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2771/5000 : ℝ)
      else (4099/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2871/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (28821260507/1993500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (3704589/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (93850127/100000000 : ℝ) ^ p + (248383467/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (93850127/100000000 : ℝ)) (y := (248383467/250000000 : ℝ)) (X := (1044450265883/6250000000000 : ℝ)) (Y := (83288814945851/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248383467/250000000 : ℝ) ^ p + (93850127/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248383467/250000000 : ℝ)) (y := (93850127/100000000 : ℝ)) (X := (83288814945851/100000000000000 : ℝ)) (Y := (1044450265883/6250000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (966017569/500000000 : ℝ)) (τ := (93850127/100000000 : ℝ)) (σ := (248383467/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (273467813/288793850 : ℝ) ^ p + (143162062/144396925 : ℝ) ^ p := by
    exact cert_lt (x := (273467813/288793850 : ℝ)) (y := (143162062/144396925 : ℝ)) (X := (21501632384521/100000000000000 : ℝ)) (Y := (78498368470571/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (93850127/100000000 : ℝ)) (n' := (17327631/20000000 : ℝ)) (Ab := (820403439/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (941843919/1000000000 : ℝ) ^ p + (496390343/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (941843919/1000000000 : ℝ)) (y := (496390343/500000000 : ℝ)) (X := (9236370005133/50000000000000 : ℝ)) (Y := (81527278767851/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496390343/500000000 : ℝ) ^ p + (941843919/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496390343/500000000 : ℝ)) (y := (941843919/1000000000 : ℝ)) (X := (81527278767851/100000000000000 : ℝ)) (Y := (9236370005133/50000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (386924921/200000000 : ℝ)) (τ := (941843919/1000000000 : ℝ)) (σ := (496390343/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (823921825/870218228 : ℝ) ^ p + (431404525/435109114 : ℝ) ^ p := by
    exact cert_lt (x := (823921825/870218228 : ℝ)) (y := (431404525/435109114 : ℝ)) (X := (21417442749733/100000000000000 : ℝ)) (Y := (78582558319079/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (941843919/1000000000 : ℝ)) (n' := (217554557/250000000 : ℝ)) (Ab := (32956873/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (94194063/100000000 : ℝ) ^ p + (248189387/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (94194063/100000000 : ℝ)) (y := (248189387/250000000 : ℝ)) (X := (9263140792463/50000000000000 : ℝ)) (Y := (81473736789241/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248189387/250000000 : ℝ) ^ p + (94194063/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248189387/250000000 : ℝ)) (y := (94194063/100000000 : ℝ)) (X := (81473736789241/100000000000000 : ℝ)) (Y := (9263140792463/50000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (967349089/500000000 : ℝ)) (τ := (94194063/100000000 : ℝ)) (σ := (248189387/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (824023429/870329032 : ℝ) ^ p + (431459927/435164516 : ℝ) ^ p := by
    exact cert_lt (x := (824023429/870329032 : ℝ)) (y := (431459927/435164516 : ℝ)) (X := (21415021457333/100000000000000 : ℝ)) (Y := (39292489998777/50000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (94194063/100000000 : ℝ)) (n' := (108791129/125000000 : ℝ)) (Ab := (824023429/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (235485853/250000000 : ℝ) ^ p + (992756881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (235485853/250000000 : ℝ)) (y := (992756881/1000000000 : ℝ)) (X := (18527823980789/100000000000000 : ℝ)) (Y := (40736096917823/50000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992756881/1000000000 : ℝ) ^ p + (235485853/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992756881/1000000000 : ℝ)) (y := (235485853/250000000 : ℝ)) (X := (40736096917823/50000000000000 : ℝ)) (Y := (18527823980789/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1934700293/1000000000 : ℝ)) (τ := (235485853/250000000 : ℝ)) (σ := (992756881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (824026351/870332219 : ℝ) ^ p + (862923041/870332219 : ℝ) ^ p := by
    exact cert_lt (x := (824026351/870332219 : ℝ)) (y := (862923041/870332219 : ℝ)) (X := (21414951545907/100000000000000 : ℝ)) (Y := (39292524821511/50000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (235485853/250000000 : ℝ)) (n' := (870332219/1000000000 : ℝ)) (Ab := (824026351/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (235485873/250000000 : ℝ) ^ p + (496378431/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (235485873/250000000 : ℝ)) (y := (496378431/500000000 : ℝ)) (X := (3705573667241/20000000000000 : ℝ)) (Y := (81472149883857/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496378431/500000000 : ℝ) ^ p + (235485873/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496378431/500000000 : ℝ)) (y := (235485873/250000000 : ℝ)) (X := (81472149883857/100000000000000 : ℝ)) (Y := (3705573667241/20000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (967350177/500000000 : ℝ)) (τ := (235485873/250000000 : ℝ)) (σ := (496378431/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (824026435/870332311 : ℝ) ^ p + (862923133/870332311 : ℝ) ^ p := by
    exact cert_lt (x := (824026435/870332311 : ℝ)) (y := (862923133/870332311 : ℝ)) (X := (21414949271249/100000000000000 : ℝ)) (Y := (7858505165349/10000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (235485873/250000000 : ℝ)) (n' := (870332311/1000000000 : ℝ)) (Ab := (164805287/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (941943493/1000000000 : ℝ) ^ p + (496378431/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (941943493/1000000000 : ℝ)) (y := (496378431/500000000 : ℝ)) (X := (2315983611331/12500000000000 : ℝ)) (Y := (81472149883857/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496378431/500000000 : ℝ) ^ p + (941943493/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496378431/500000000 : ℝ)) (y := (941943493/1000000000 : ℝ)) (X := (81472149883857/100000000000000 : ℝ)) (Y := (2315983611331/12500000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (386940071/200000000 : ℝ)) (τ := (941943493/1000000000 : ℝ)) (σ := (496378431/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (206006609/217583078 : ℝ) ^ p + (431461567/435166156 : ℝ) ^ p := by
    exact cert_lt (x := (206006609/217583078 : ℝ)) (y := (431461567/435166156 : ℝ)) (X := (1338434331889/6250000000000 : ℝ)) (Y := (78585051675343/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (941943493/1000000000 : ℝ)) (n' := (108791539/125000000 : ℝ)) (Ab := (206006609/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (386940071/200000000 : ℝ)) (τ := (941943493/1000000000 : ℝ)) (σ := (496378431/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (941943493/1000000000 : ℝ)) (n' := (108791539/125000000 : ℝ)) (Ab := (206006609/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (386940071/200000000 : ℝ)) (τ := (941943493/1000000000 : ℝ)) (σ := (496378431/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (941943493/1000000000 : ℝ)) (n' := (108791539/125000000 : ℝ)) (Ab := (206006609/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (386940071/200000000 : ℝ)) (τ := (941943493/1000000000 : ℝ)) (σ := (496378431/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (941943493/1000000000 : ℝ)) (n' := (108791539/125000000 : ℝ)) (Ab := (206006609/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (386940071/200000000 : ℝ)) (τ := (941943493/1000000000 : ℝ)) (σ := (496378431/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (941943493/1000000000 : ℝ)) (n' := (108791539/125000000 : ℝ)) (Ab := (206006609/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (386940071/200000000 : ℝ)) (τ := (941943493/1000000000 : ℝ)) (σ := (496378431/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1702963681/1843288819 : ℝ) ^ p + (1835879641/1843288819 : ℝ) ^ p := by
    exact cert_lt (x := (1702963681/1843288819 : ℝ)) (y := (1835879641/1843288819 : ℝ)) (X := (2683046366203/25000000000000 : ℝ)) (Y := (89267814864083/100000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1085242390/1156711181 : ℝ) ^ p + (1149302003/1156711181 : ℝ) ^ p := by
    exact cert_lt (x := (1085242390/1156711181 : ℝ)) (y := (1149302003/1156711181 : ℝ)) (X := (16567517042993/100000000000000 : ℝ)) (Y := (4171624172211/5000000000000 : ℝ)) 451 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496378431/500000000 : ℝ)) (U := (1156711181/1000000000 : ℝ)) (Ab := (1702963681/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (941943493/1000000000 : ℝ)) (σ := (496378431/500000000 : ℝ)) (Ab := (108524239/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab034
