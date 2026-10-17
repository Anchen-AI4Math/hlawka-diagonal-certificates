import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 14, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab014 (p : ℝ) (hpa : (215/8 : ℝ) ≤ p) (hpb : p ≤ (431/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (144936972721/9524500000000 : ℝ) (7807431/1000000000 : ℝ) (320000057147/1904900000000 : ℝ) (591/500 : ℝ) (974596557/500000000 : ℝ) (974538237/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (231184481/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(676/625 : ℝ) ≤ X j i ∧ X j i ≤ -(687/1250 : ℝ)
      else (8151/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11473/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (144936972721/9524500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (7807431/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (935500987/1000000000 : ℝ) ^ p + (993285781/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (935500987/1000000000 : ℝ)) (y := (993285781/1000000000 : ℝ)) (X := (16596040478127/100000000000000 : ℝ)) (Y := (41701988701479/50000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993285781/1000000000 : ℝ) ^ p + (935500987/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993285781/1000000000 : ℝ)) (y := (935500987/1000000000 : ℝ)) (X := (41701988701479/50000000000000 : ℝ)) (Y := (16596040478127/100000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (120549173/62500000 : ℝ)) (τ := (935500987/1000000000 : ℝ)) (σ := (993285781/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (272096579/287978688 : ℝ) ^ p + (285376211/287978688 : ℝ) ^ p := by
    exact cert_lt (x := (272096579/287978688 : ℝ)) (y := (285376211/287978688 : ℝ)) (X := (21693699189027/100000000000000 : ℝ)) (Y := (78306302039481/100000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (935500987/1000000000 : ℝ)) (n' := (13499001/15625000 : ℝ)) (Ab := (816289737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (938948897/1000000000 : ℝ) ^ p + (496256841/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (938948897/1000000000 : ℝ)) (y := (496256841/500000000 : ℝ)) (X := (9162472769107/50000000000000 : ℝ)) (Y := (81675072950999/100000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496256841/500000000 : ℝ) ^ p + (938948897/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496256841/500000000 : ℝ)) (y := (938948897/1000000000 : ℝ)) (X := (81675072950999/100000000000000 : ℝ)) (Y := (9162472769107/50000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1931462579/1000000000 : ℝ)) (τ := (938948897/1000000000 : ℝ)) (σ := (496256841/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (819921966/867911495 : ℝ) ^ p + (860104064/867911495 : ℝ) ^ p := by
    exact cert_lt (x := (819921966/867911495 : ℝ)) (y := (860104064/867911495 : ℝ)) (X := (5401384952847/25000000000000 : ℝ)) (Y := (1567889222999/2000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (938948897/1000000000 : ℝ)) (n' := (173582299/200000000 : ℝ)) (Ab := (409960983/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (469527359/500000000 : ℝ) ^ p + (49624427/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (469527359/500000000 : ℝ)) (y := (49624427/50000000 : ℝ)) (X := (1838065959469/10000000000000 : ℝ)) (Y := (40809679274683/50000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (49624427/50000000 : ℝ) ^ p + (469527359/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (49624427/50000000 : ℝ)) (y := (469527359/500000000 : ℝ)) (X := (40809679274683/50000000000000 : ℝ)) (Y := (1838065959469/10000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (965771629/500000000 : ℝ)) (τ := (469527359/500000000 : ℝ)) (σ := (49624427/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (820033225/868033277 : ℝ) ^ p + (860225846/868033277 : ℝ) ^ p := by
    exact cert_lt (x := (820033225/868033277 : ℝ)) (y := (860225846/868033277 : ℝ)) (X := (2700356327871/12500000000000 : ℝ)) (Y := (19599287634889/25000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (469527359/500000000 : ℝ)) (n' := (868033277/1000000000 : ℝ)) (Ab := (32801329/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939057947/1000000000 : ℝ) ^ p + (992487771/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939057947/1000000000 : ℝ)) (y := (992487771/1000000000 : ℝ)) (X := (4595590550891/25000000000000 : ℝ)) (Y := (8161765503053/10000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992487771/1000000000 : ℝ) ^ p + (939057947/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992487771/1000000000 : ℝ)) (y := (939057947/1000000000 : ℝ)) (X := (8161765503053/10000000000000 : ℝ)) (Y := (4595590550891/25000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (965772859/500000000 : ℝ)) (τ := (939057947/1000000000 : ℝ)) (σ := (992487771/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (820036620/868036993 : ℝ) ^ p + (860229562/868036993 : ℝ) ^ p := by
    exact cert_lt (x := (820036620/868036993 : ℝ)) (y := (860229562/868036993 : ℝ)) (X := (4320553729987/20000000000000 : ℝ)) (Y := (78397232591887/100000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939057947/1000000000 : ℝ)) (n' := (868036993/1000000000 : ℝ)) (Ab := (41001831/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (187811609/200000000 : ℝ) ^ p + (248121937/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (187811609/200000000 : ℝ)) (y := (248121937/250000000 : ℝ)) (X := (9191206940019/50000000000000 : ℝ)) (Y := (81617604080559/100000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248121937/250000000 : ℝ) ^ p + (187811609/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248121937/250000000 : ℝ)) (y := (187811609/200000000 : ℝ)) (X := (81617604080559/100000000000000 : ℝ)) (Y := (9191206940019/50000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1931545793/1000000000 : ℝ)) (τ := (187811609/200000000 : ℝ)) (σ := (248121937/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (820036723/868037106 : ℝ) ^ p + (286743225/289345702 : ℝ) ^ p := by
    exact cert_lt (x := (820036723/868037106 : ℝ)) (y := (286743225/289345702 : ℝ)) (X := (21602765987841/100000000000000 : ℝ)) (Y := (7839723508701/10000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (187811609/200000000 : ℝ)) (n' := (434018553/500000000 : ℝ)) (Ab := (820036723/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (939058049/1000000000 : ℝ) ^ p + (992487747/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939058049/1000000000 : ℝ)) (y := (992487747/1000000000 : ℝ)) (X := (3676483197857/20000000000000 : ℝ)) (Y := (81617601865343/100000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992487747/1000000000 : ℝ) ^ p + (939058049/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992487747/1000000000 : ℝ)) (y := (939058049/1000000000 : ℝ)) (X := (81617601865343/100000000000000 : ℝ)) (Y := (3676483197857/20000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (482886449/250000000 : ℝ)) (τ := (939058049/1000000000 : ℝ)) (σ := (992487747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (820036727/868037110 : ℝ) ^ p + (860229679/868037110 : ℝ) ^ p := by
    exact cert_lt (x := (820036727/868037110 : ℝ)) (y := (860229679/868037110 : ℝ)) (X := (4320553228961/20000000000000 : ℝ)) (Y := (78397235175333/100000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (939058049/1000000000 : ℝ)) (n' := (86803711/100000000 : ℝ)) (Ab := (820036727/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (482886449/250000000 : ℝ)) (τ := (939058049/1000000000 : ℝ)) (σ := (992487747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (939058049/1000000000 : ℝ)) (n' := (86803711/100000000 : ℝ)) (Ab := (820036727/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (482886449/250000000 : ℝ)) (τ := (939058049/1000000000 : ℝ)) (σ := (992487747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (939058049/1000000000 : ℝ)) (n' := (86803711/100000000 : ℝ)) (Ab := (820036727/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (482886449/250000000 : ℝ)) (τ := (939058049/1000000000 : ℝ)) (σ := (992487747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (939058049/1000000000 : ℝ)) (n' := (86803711/100000000 : ℝ)) (Ab := (820036727/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (482886449/250000000 : ℝ)) (τ := (939058049/1000000000 : ℝ)) (σ := (992487747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (939058049/1000000000 : ℝ)) (n' := (86803711/100000000 : ℝ)) (Ab := (820036727/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (482886449/250000000 : ℝ)) (τ := (939058049/1000000000 : ℝ)) (σ := (992487747/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1697841284/1844077595 : ℝ) ^ p + (1836270164/1844077595 : ℝ) ^ p := by
    exact cert_lt (x := (1697841284/1844077595 : ℝ)) (y := (1836270164/1844077595 : ℝ)) (X := (10800052884423/100000000000000 : ℝ)) (Y := (22299986837803/25000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1081585037/1155922405 : ℝ) ^ p + (1148114974/1155922405 : ℝ) ^ p := by
    exact cert_lt (x := (1081585037/1155922405 : ℝ)) (y := (1148114974/1155922405 : ℝ)) (X := (16686603583071/100000000000000 : ℝ)) (Y := (41656698525303/50000000000000 : ℝ)) 431 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992487747/1000000000 : ℝ)) (U := (231184481/200000000 : ℝ)) (Ab := (424460321/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (939058049/1000000000 : ℝ)) (σ := (992487747/1000000000 : ℝ)) (Ab := (1081585037/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab014
