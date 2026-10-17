import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 75, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab075 (p : ℝ) (hpa : (491/16 : ℝ) ≤ p) (hpb : p ≤ (123/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1426133287873/108756500000000 : ℝ) (6706323/1000000000 : ℝ) (3200000652539/21751300000000 : ℝ) (591/500 : ℝ) (977710787/500000000 : ℝ) (977665901/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (579106219/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(273/250 : ℝ) ≤ X j i ∧ X j i ≤ -(5623/10000 : ℝ)
      else (207/250 : ℝ) ≤ X j i ∧ X j i ≤ (2301/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1426133287873/108756500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (6706323/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (23596431/25000000 : ℝ) ^ p + (993990447/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23596431/25000000 : ℝ)) (y := (993990447/1000000000 : ℝ)) (X := (676751254831/4000000000000 : ℝ)) (Y := (10385155086921/12500000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993990447/1000000000 : ℝ) ^ p + (23596431/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (993990447/1000000000 : ℝ)) (y := (23596431/25000000 : ℝ)) (X := (10385155086921/12500000000000 : ℝ)) (Y := (676751254831/4000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1937847687/1000000000 : ℝ)) (τ := (23596431/25000000 : ℝ)) (σ := (993990447/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (827786649/870666505 : ℝ) ^ p + (863960182/870666505 : ℝ) ^ p := by
    exact cert_lt (x := (827786649/870666505 : ℝ)) (y := (863960182/870666505 : ℝ)) (X := (21161543689141/100000000000000 : ℝ)) (Y := (9854807185413/12500000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (23596431/25000000 : ℝ)) (n' := (174133301/200000000 : ℝ)) (Ab := (827786649/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (946995337/1000000000 : ℝ) ^ p + (993275491/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (946995337/1000000000 : ℝ)) (y := (993275491/1000000000 : ℝ)) (X := (4684207287701/25000000000000 : ℝ)) (Y := (40631595516411/50000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993275491/1000000000 : ℝ) ^ p + (946995337/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993275491/1000000000 : ℝ)) (y := (946995337/1000000000 : ℝ)) (X := (40631595516411/50000000000000 : ℝ)) (Y := (4684207287701/25000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (485067707/250000000 : ℝ)) (τ := (946995337/1000000000 : ℝ)) (σ := (993275491/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (7767151/8170462 : ℝ) ^ p + (867533111/874239434 : ℝ) ^ p := by
    exact cert_lt (x := (7767151/8170462 : ℝ)) (y := (867533111/874239434 : ℝ)) (X := (5271149981799/25000000000000 : ℝ)) (Y := (39457700579181/50000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (946995337/1000000000 : ℝ)) (n' := (437119717/500000000 : ℝ)) (Ab := (831085157/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (236769141/250000000 : ℝ) ^ p + (124156977/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (236769141/250000000 : ℝ)) (y := (124156977/125000000 : ℝ)) (X := (18786311236727/100000000000000 : ℝ)) (Y := (4060685401447/5000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124156977/125000000 : ℝ) ^ p + (236769141/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124156977/125000000 : ℝ)) (y := (236769141/250000000 : ℝ)) (X := (4060685401447/5000000000000 : ℝ)) (Y := (18786311236727/100000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (97016619/50000000 : ℝ)) (τ := (236769141/250000000 : ℝ)) (σ := (124156977/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (415585193/437165880 : ℝ) ^ p + (289208479/291443920 : ℝ) ^ p := by
    exact cert_lt (x := (415585193/437165880 : ℝ)) (y := (289208479/291443920 : ℝ)) (X := (4216523804033/20000000000000 : ℝ)) (Y := (9864672754891/12500000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (236769141/250000000 : ℝ)) (n' := (10929147/12500000 : ℝ)) (Ab := (415585193/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (189415731/200000000 : ℝ) ^ p + (993255309/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (189415731/200000000 : ℝ)) (y := (993255309/1000000000 : ℝ)) (X := (9393793352763/50000000000000 : ℝ)) (Y := (20303108324883/25000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993255309/1000000000 : ℝ) ^ p + (189415731/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993255309/1000000000 : ℝ)) (y := (189415731/200000000 : ℝ)) (X := (20303108324883/25000000000000 : ℝ)) (Y := (9393793352763/50000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (485083491/250000000 : ℝ)) (τ := (189415731/200000000 : ℝ)) (σ := (993255309/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (831172580/874334137 : ℝ) ^ p + (27987994/28204327 : ℝ) ^ p := by
    exact cert_lt (x := (831172580/874334137 : ℝ)) (y := (27987994/28204327 : ℝ)) (X := (843302712311/4000000000000 : ℝ)) (Y := (15783486606691/20000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (189415731/200000000 : ℝ)) (n' := (874334137/1000000000 : ℝ)) (Ab := (41558629/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (947078709/1000000000 : ℝ) ^ p + (7759807/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (947078709/1000000000 : ℝ)) (y := (7759807/7812500 : ℝ)) (X := (4696904911393/25000000000000 : ℝ)) (Y := (81212400614417/100000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (7759807/7812500 : ℝ) ^ p + (947078709/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7759807/7812500 : ℝ)) (y := (947078709/1000000000 : ℝ)) (X := (81212400614417/100000000000000 : ℝ)) (Y := (4696904911393/25000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (388066801/200000000 : ℝ)) (τ := (947078709/1000000000 : ℝ)) (σ := (7759807/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (831172637/874334198 : ℝ) ^ p + (867627875/874334198 : ℝ) ^ p := by
    exact cert_lt (x := (831172637/874334198 : ℝ)) (y := (867627875/874334198 : ℝ)) (X := (4216513407319/20000000000000 : ℝ)) (Y := (78917434342099/100000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (947078709/1000000000 : ℝ)) (n' := (437167099/500000000 : ℝ)) (Ab := (831172637/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (94707871/100000000 : ℝ) ^ p + (7759807/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (94707871/100000000 : ℝ)) (y := (7759807/7812500 : ℝ)) (X := (9393810127787/50000000000000 : ℝ)) (Y := (81212400614417/100000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (7759807/7812500 : ℝ) ^ p + (94707871/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (7759807/7812500 : ℝ)) (y := (94707871/100000000 : ℝ)) (X := (81212400614417/100000000000000 : ℝ)) (Y := (9393810127787/50000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (970167003/500000000 : ℝ)) (τ := (94707871/100000000 : ℝ)) (σ := (7759807/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (277057546/291444733 : ℝ) ^ p + (9329332/9401443 : ℝ) ^ p := by
    exact cert_lt (x := (277057546/291444733 : ℝ)) (y := (9329332/9401443 : ℝ)) (X := (10541283537549/50000000000000 : ℝ)) (Y := (2466169823861/3125000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (94707871/100000000 : ℝ)) (n' := (874334199/1000000000 : ℝ)) (Ab := (415586319/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (970167003/500000000 : ℝ)) (τ := (94707871/100000000 : ℝ)) (σ := (7759807/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (94707871/100000000 : ℝ)) (n' := (874334199/1000000000 : ℝ)) (Ab := (415586319/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (970167003/500000000 : ℝ)) (τ := (94707871/100000000 : ℝ)) (σ := (7759807/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (94707871/100000000 : ℝ)) (n' := (874334199/1000000000 : ℝ)) (Ab := (415586319/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (970167003/500000000 : ℝ)) (τ := (94707871/100000000 : ℝ)) (σ := (7759807/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (94707871/100000000 : ℝ)) (n' := (874334199/1000000000 : ℝ)) (Ab := (415586319/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (970167003/500000000 : ℝ)) (τ := (94707871/100000000 : ℝ)) (σ := (7759807/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (94707871/100000000 : ℝ)) (n' := (874334199/1000000000 : ℝ)) (Ab := (415586319/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (970167003/500000000 : ℝ)) (τ := (94707871/100000000 : ℝ)) (σ := (7759807/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (856104294/920893781 : ℝ) ^ p + (59196169/59412502 : ℝ) ^ p := by
    exact cert_lt (x := (856104294/920893781 : ℝ)) (y := (59196169/59412502 : ℝ)) (X := (10610892377229/100000000000000 : ℝ)) (Y := (89389107986737/100000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1091979149/1158212438 : ℝ) ^ p + (1151506115/1158212438 : ℝ) ^ p := by
    exact cert_lt (x := (1091979149/1158212438 : ℝ)) (y := (1151506115/1158212438 : ℝ)) (X := (3270643613343/20000000000000 : ℝ)) (Y := (83646782670413/100000000000000 : ℝ)) 123 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (7759807/7812500 : ℝ)) (U := (579106219/500000000 : ℝ)) (Ab := (428052147/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (94707871/100000000 : ℝ)) (σ := (7759807/7812500 : ℝ)) (Ab := (1091979149/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab075
