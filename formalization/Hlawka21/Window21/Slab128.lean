import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 128, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab128 (p : ℝ) (hpa : (25 : ℝ) ≤ p) (hpb : p ≤ (801/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2604406507/136500000000 : ℝ) (2452039/250000000 : ℝ) (5000000819/27300000000 : ℝ) (3033/2500 : ℝ) (121586077/62500000 : ℝ) (972654947/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193999777/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5583/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(931/2000 : ℝ)
      else (1951/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11857/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2604406507/136500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2452039/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (923881869/1000000000 : ℝ) ^ p + (994092923/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (923881869/1000000000 : ℝ)) (y := (994092923/1000000000 : ℝ)) (X := (6891386764309/50000000000000 : ℝ)) (Y := (86217245604447/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994092923/1000000000 : ℝ) ^ p + (923881869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994092923/1000000000 : ℝ)) (y := (923881869/1000000000 : ℝ)) (X := (86217245604447/100000000000000 : ℝ)) (Y := (6891386764309/50000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (239746849/125000000 : ℝ)) (τ := (923881869/1000000000 : ℝ)) (σ := (994092923/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (788894949/832953326 : ℝ) ^ p + (411572585/416476663 : ℝ) ^ p := by
    exact cert_lt (x := (788894949/832953326 : ℝ)) (y := (411572585/416476663 : ℝ)) (X := (2565814012141/10000000000000 : ℝ)) (Y := (74341861389901/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (923881869/1000000000 : ℝ)) (n' := (416476663/500000000 : ℝ)) (Ab := (788894949/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (116166209/125000000 : ℝ) ^ p + (198614779/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (116166209/125000000 : ℝ)) (y := (198614779/200000000 : ℝ)) (X := (997999712277/6250000000000 : ℝ)) (Y := (84032022574687/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198614779/200000000 : ℝ) ^ p + (116166209/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (198614779/200000000 : ℝ)) (y := (116166209/125000000 : ℝ)) (X := (84032022574687/100000000000000 : ℝ)) (Y := (997999712277/6250000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1922403567/1000000000 : ℝ)) (τ := (116166209/125000000 : ℝ)) (σ := (198614779/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (794749546/839356915 : ℝ) ^ p + (829548759/839356915 : ℝ) ^ p := by
    exact cert_lt (x := (794749546/839356915 : ℝ)) (y := (829548759/839356915 : ℝ)) (X := (25488792282241/100000000000000 : ℝ)) (Y := (74511208628611/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (116166209/125000000 : ℝ)) (n' := (167871383/200000000 : ℝ)) (Ab := (397374773/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (116193643/125000000 : ℝ) ^ p + (993029179/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116193643/125000000 : ℝ)) (y := (993029179/1000000000 : ℝ)) (X := (8031328636171/50000000000000 : ℝ)) (Y := (83937360987033/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993029179/1000000000 : ℝ) ^ p + (116193643/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993029179/1000000000 : ℝ)) (y := (116193643/125000000 : ℝ)) (X := (83937360987033/100000000000000 : ℝ)) (Y := (8031328636171/50000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1922578323/1000000000 : ℝ)) (τ := (116193643/125000000 : ℝ)) (σ := (993029179/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (794984662/839614119 : ℝ) ^ p + (829805963/839614119 : ℝ) ^ p := by
    exact cert_lt (x := (794984662/839614119 : ℝ)) (y := (829805963/839614119 : ℝ)) (X := (5096407310659/20000000000000 : ℝ)) (Y := (74517964268301/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (116193643/125000000 : ℝ)) (n' := (839614119/1000000000 : ℝ)) (Ab := (397492331/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (929557897/1000000000 : ℝ) ^ p + (993027389/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (929557897/1000000000 : ℝ)) (y := (993027389/1000000000 : ℝ)) (X := (502076366709/3125000000000 : ℝ)) (Y := (83933573776371/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993027389/1000000000 : ℝ) ^ p + (929557897/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993027389/1000000000 : ℝ)) (y := (929557897/1000000000 : ℝ)) (X := (83933573776371/100000000000000 : ℝ)) (Y := (502076366709/3125000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (961292643/500000000 : ℝ)) (τ := (929557897/1000000000 : ℝ)) (σ := (993027389/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (264998013/279874792 : ℝ) ^ p + (207454055/209906094 : ℝ) ^ p := by
    exact cert_lt (x := (264998013/279874792 : ℝ)) (y := (207454055/209906094 : ℝ)) (X := (20385414353/80000000000 : ℝ)) (Y := (74518233601819/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (929557897/1000000000 : ℝ)) (n' := (104953047/125000000 : ℝ)) (Ab := (794994039/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (464779123/500000000 : ℝ) ^ p + (496513659/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (464779123/500000000 : ℝ)) (y := (496513659/500000000 : ℝ)) (X := (4016648681611/25000000000000 : ℝ)) (Y := (5245838972549/6250000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496513659/500000000 : ℝ) ^ p + (464779123/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496513659/500000000 : ℝ)) (y := (464779123/500000000 : ℝ)) (X := (5245838972549/6250000000000 : ℝ)) (Y := (4016648681611/25000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (480646391/250000000 : ℝ)) (τ := (464779123/500000000 : ℝ)) (σ := (496513659/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (794994412/839624785 : ℝ) ^ p + (829816629/839624785 : ℝ) ^ p := by
    exact cert_lt (x := (794994412/839624785 : ℝ)) (y := (829816629/839624785 : ℝ)) (X := (6370439125129/25000000000000 : ℝ)) (Y := (9314780542679/12500000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (464779123/500000000 : ℝ)) (n' := (167924957/200000000 : ℝ)) (Ab := (198748603/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (46477913/50000000 : ℝ) ^ p + (198605463/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (46477913/50000000 : ℝ)) (y := (198605463/200000000 : ℝ)) (X := (2008325097931/12500000000000 : ℝ)) (Y := (20983354303413/25000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (198605463/200000000 : ℝ) ^ p + (46477913/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (198605463/200000000 : ℝ)) (y := (46477913/50000000 : ℝ)) (X := (20983354303413/25000000000000 : ℝ)) (Y := (2008325097931/12500000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (76903423/40000000 : ℝ)) (τ := (46477913/50000000 : ℝ)) (σ := (198605463/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (794994427/839624801 : ℝ) ^ p + (829816645/839624801 : ℝ) ^ p := by
    exact cert_lt (x := (794994427/839624801 : ℝ)) (y := (829816645/839624801 : ℝ)) (X := (5096351276111/20000000000000 : ℝ)) (Y := (74518244761563/100000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (46477913/50000000 : ℝ)) (n' := (839624801/1000000000 : ℝ)) (Ab := (794994427/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (76903423/40000000 : ℝ)) (τ := (46477913/50000000 : ℝ)) (σ := (198605463/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (46477913/50000000 : ℝ)) (n' := (839624801/1000000000 : ℝ)) (Ab := (794994427/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (76903423/40000000 : ℝ)) (τ := (46477913/50000000 : ℝ)) (σ := (198605463/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (46477913/50000000 : ℝ)) (n' := (839624801/1000000000 : ℝ)) (Ab := (794994427/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (76903423/40000000 : ℝ)) (τ := (46477913/50000000 : ℝ)) (σ := (198605463/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (46477913/50000000 : ℝ)) (n' := (839624801/1000000000 : ℝ)) (Ab := (794994427/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (76903423/40000000 : ℝ)) (τ := (46477913/50000000 : ℝ)) (σ := (198605463/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (46477913/50000000 : ℝ)) (n' := (839624801/1000000000 : ℝ)) (Ab := (794994427/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (76903423/40000000 : ℝ)) (τ := (46477913/50000000 : ℝ)) (σ := (198605463/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1663310389/1806000223 : ℝ) ^ p + (1796192067/1806000223 : ℝ) ^ p := by
    exact cert_lt (x := (1663310389/1806000223 : ℝ)) (y := (1796192067/1806000223 : ℝ)) (X := (12742965208617/100000000000000 : ℝ)) (Y := (4362851755149/5000000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1116535045/1193999777 : ℝ) ^ p + (1184191621/1193999777 : ℝ) ^ p := by
    exact cert_lt (x := (1116535045/1193999777 : ℝ)) (y := (1184191621/1193999777 : ℝ)) (X := (18654880016831/100000000000000 : ℝ)) (Y := (10168140081119/12500000000000 : ℝ)) 801 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198605463/200000000 : ℝ)) (U := (1193999777/1000000000 : ℝ)) (Ab := (1663310389/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (46477913/50000000 : ℝ)) (σ := (198605463/200000000 : ℝ)) (Ab := (223307009/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab128
