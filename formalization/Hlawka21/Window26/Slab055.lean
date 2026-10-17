import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 55, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab055 (p : ℝ) (hpa : (471/16 : ℝ) ≤ p) (hpb : p ≤ (59/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (716547016511/52163250000000 : ℝ) (1757989/250000000 : ℝ) (3200000625959/20865300000000 : ℝ) (591/500 : ℝ) (48838869/25000000 : ℝ) (244182163/250000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1157499143/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10889/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1117/2000 : ℝ)
      else (4121/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2299/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (716547016511/52163250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1757989/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (941365943/1000000000 : ℝ) ^ p + (49688793/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (941365943/1000000000 : ℝ)) (y := (49688793/50000000 : ℝ)) (X := (16821906925289/100000000000000 : ℝ)) (Y := (41589056986911/50000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (49688793/50000000 : ℝ) ^ p + (941365943/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49688793/50000000 : ℝ)) (y := (941365943/1000000000 : ℝ)) (X := (41589056986911/50000000000000 : ℝ)) (Y := (16821906925289/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1935141803/1000000000 : ℝ)) (τ := (941365943/1000000000 : ℝ)) (σ := (49688793/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (412172975/434343147 : ℝ) ^ p + (430827169/434343147 : ℝ) ^ p := by
    exact cert_lt (x := (412172975/434343147 : ℝ)) (y := (430827169/434343147 : ℝ)) (X := (10659649197601/50000000000000 : ℝ)) (Y := (78680702622431/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (941365943/1000000000 : ℝ)) (n' := (434343147/500000000 : ℝ)) (Ab := (16486919/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (944601783/1000000000 : ℝ) ^ p + (496521209/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (944601783/1000000000 : ℝ)) (y := (496521209/500000000 : ℝ)) (X := (4653486498757/25000000000000 : ℝ)) (Y := (1271657397611/1562500000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496521209/500000000 : ℝ) ^ p + (944601783/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496521209/500000000 : ℝ)) (y := (944601783/1000000000 : ℝ)) (X := (1271657397611/1562500000000 : ℝ)) (Y := (4653486498757/25000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1937644201/1000000000 : ℝ)) (τ := (944601783/1000000000 : ℝ)) (σ := (496521209/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (827749327/872384374 : ℝ) ^ p + (432676209/436192187 : ℝ) ^ p := by
    exact cert_lt (x := (827749327/872384374 : ℝ)) (y := (432676209/436192187 : ℝ)) (X := (10619480597897/50000000000000 : ℝ)) (Y := (39380519833183/50000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (944601783/1000000000 : ℝ)) (n' := (436192187/500000000 : ℝ)) (Ab := (827749327/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (944690081/1000000000 : ℝ) ^ p + (993021153/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944690081/1000000000 : ℝ)) (y := (993021153/1000000000 : ℝ)) (X := (18665343398411/100000000000000 : ℝ)) (Y := (81334676516933/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993021153/1000000000 : ℝ) ^ p + (944690081/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993021153/1000000000 : ℝ)) (y := (944690081/1000000000 : ℝ)) (X := (81334676516933/100000000000000 : ℝ)) (Y := (18665343398411/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (968855617/500000000 : ℝ)) (τ := (944690081/1000000000 : ℝ)) (σ := (993021153/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (827842028/872485109 : ℝ) ^ p + (865453153/872485109 : ℝ) ^ p := by
    exact cert_lt (x := (827842028/872485109 : ℝ)) (y := (865453153/872485109 : ℝ)) (X := (21236781630241/100000000000000 : ℝ)) (Y := (78763219607483/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (944690081/1000000000 : ℝ)) (n' := (872485109/1000000000 : ℝ)) (Ab := (206960507/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (944692477/1000000000 : ℝ) ^ p + (39720823/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (944692477/1000000000 : ℝ)) (y := (39720823/40000000 : ℝ)) (X := (18666739995573/100000000000000 : ℝ)) (Y := (203333199861/250000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (39720823/40000000 : ℝ) ^ p + (944692477/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39720823/40000000 : ℝ)) (y := (944692477/1000000000 : ℝ)) (X := (203333199861/250000000000 : ℝ)) (Y := (18666739995573/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (484428263/250000000 : ℝ)) (τ := (944692477/1000000000 : ℝ)) (σ := (39720823/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (827844544/872487843 : ℝ) ^ p + (865455887/872487843 : ℝ) ^ p := by
    exact cert_lt (x := (827844544/872487843 : ℝ)) (y := (865455887/872487843 : ℝ)) (X := (4247344504247/20000000000000 : ℝ)) (Y := (78763278766009/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (944692477/1000000000 : ℝ)) (n' := (872487843/1000000000 : ℝ)) (Ab := (12935071/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (472346271/500000000 : ℝ) ^ p + (993020559/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (472346271/500000000 : ℝ)) (y := (993020559/1000000000 : ℝ)) (X := (2333347235579/12500000000000 : ℝ)) (Y := (81333241285283/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993020559/1000000000 : ℝ) ^ p + (472346271/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993020559/1000000000 : ℝ)) (y := (472346271/500000000 : ℝ)) (X := (81333241285283/100000000000000 : ℝ)) (Y := (2333347235579/12500000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1937713101/1000000000 : ℝ)) (τ := (472346271/500000000 : ℝ)) (σ := (993020559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (118263516/124641131 : ℝ) ^ p + (865455961/872487917 : ℝ) ^ p := by
    exact cert_lt (x := (118263516/124641131 : ℝ)) (y := (865455961/872487917 : ℝ)) (X := (5309180211519/25000000000000 : ℝ)) (Y := (78763280367223/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (472346271/500000000 : ℝ)) (n' := (872487917/1000000000 : ℝ)) (Ab := (206961153/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (944692543/1000000000 : ℝ) ^ p + (993020559/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (944692543/1000000000 : ℝ)) (y := (993020559/1000000000 : ℝ)) (X := (18666778467541/100000000000000 : ℝ)) (Y := (81333241285283/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993020559/1000000000 : ℝ) ^ p + (944692543/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993020559/1000000000 : ℝ)) (y := (944692543/1000000000 : ℝ)) (X := (81333241285283/100000000000000 : ℝ)) (Y := (18666778467541/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (968856551/500000000 : ℝ)) (τ := (944692543/1000000000 : ℝ)) (σ := (993020559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (827844613/872487918 : ℝ) ^ p + (432727981/436243959 : ℝ) ^ p := by
    exact cert_lt (x := (827844613/872487918 : ℝ)) (y := (432727981/436243959 : ℝ)) (X := (10618360442399/50000000000000 : ℝ)) (Y := (78763280388861/100000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (944692543/1000000000 : ℝ)) (n' := (436243959/500000000 : ℝ)) (Ab := (827844613/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (968856551/500000000 : ℝ)) (τ := (944692543/1000000000 : ℝ)) (σ := (993020559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (944692543/1000000000 : ℝ)) (n' := (436243959/500000000 : ℝ)) (Ab := (827844613/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (968856551/500000000 : ℝ)) (τ := (944692543/1000000000 : ℝ)) (σ := (993020559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (944692543/1000000000 : ℝ)) (n' := (436243959/500000000 : ℝ)) (Ab := (827844613/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (968856551/500000000 : ℝ)) (τ := (944692543/1000000000 : ℝ)) (σ := (993020559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (944692543/1000000000 : ℝ)) (n' := (436243959/500000000 : ℝ)) (Ab := (827844613/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (968856551/500000000 : ℝ)) (τ := (944692543/1000000000 : ℝ)) (σ := (993020559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (944692543/1000000000 : ℝ)) (n' := (436243959/500000000 : ℝ)) (Ab := (827844613/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (968856551/500000000 : ℝ)) (τ := (944692543/1000000000 : ℝ)) (σ := (993020559/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1707892147/1842500857 : ℝ) ^ p + (1835468901/1842500857 : ℝ) ^ p := by
    exact cert_lt (x := (1707892147/1842500857 : ℝ)) (y := (1835468901/1842500857 : ℝ)) (X := (10667334682301/100000000000000 : ℝ)) (Y := (44666332779757/50000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1088811926/1157499143 : ℝ) ^ p + (1150467187/1157499143 : ℝ) ^ p := by
    exact cert_lt (x := (1088811926/1157499143 : ℝ)) (y := (1150467187/1157499143 : ℝ)) (X := (8226585938833/50000000000000 : ℝ)) (Y := (4177341446599/5000000000000 : ℝ)) 59 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993020559/1000000000 : ℝ)) (U := (1157499143/1000000000 : ℝ)) (Ab := (1707892147/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (944692543/1000000000 : ℝ)) (σ := (993020559/1000000000 : ℝ)) (Ab := (544405963/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab055
