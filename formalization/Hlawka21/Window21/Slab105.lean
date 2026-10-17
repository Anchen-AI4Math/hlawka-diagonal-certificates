import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 105, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab105 (p : ℝ) (hpa : (777/32 : ℝ) ≤ p) (hpb : p ≤ (389/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (130677573869/6628781250000 : ℝ) (10142267/1000000000 : ℝ) (4000000636363/21212100000000 : ℝ) (3033/2500 : ℝ) (971892663/500000000 : ℝ) (485928501/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238741539/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11143/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4617/10000 : ℝ)
      else (7767/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2963/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (130677573869/6628781250000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10142267/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (921516843/1000000000 : ℝ) ^ p + (993954087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921516843/1000000000 : ℝ)) (y := (993954087/1000000000 : ℝ)) (X := (2741674724287/20000000000000 : ℝ)) (Y := (17258328980599/20000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993954087/1000000000 : ℝ) ^ p + (921516843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993954087/1000000000 : ℝ)) (y := (921516843/1000000000 : ℝ)) (X := (17258328980599/20000000000000 : ℝ)) (Y := (2741674724287/20000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (191547093/100000000 : ℝ)) (τ := (921516843/1000000000 : ℝ)) (σ := (993954087/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (785772833/830779729 : ℝ) ^ p + (820637462/830779729 : ℝ) ^ p := by
    exact cert_lt (x := (785772833/830779729 : ℝ)) (y := (820637462/830779729 : ℝ)) (X := (3227140166713/12500000000000 : ℝ)) (Y := (18545719951033/25000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (921516843/1000000000 : ℝ)) (n' := (830779729/1000000000 : ℝ)) (Ab := (785772833/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (2897073/3125000 : ℝ) ^ p + (248230383/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (2897073/3125000 : ℝ)) (y := (248230383/250000000 : ℝ)) (X := (15861625783021/100000000000000 : ℝ)) (Y := (84138391224701/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248230383/250000000 : ℝ) ^ p + (2897073/3125000 : ℝ) ^ p := by
    exact cert_lt (x := (248230383/250000000 : ℝ)) (y := (2897073/3125000 : ℝ)) (X := (84138391224701/100000000000000 : ℝ)) (Y := (15861625783021/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (479996223/250000000 : ℝ)) (τ := (2897073/3125000 : ℝ)) (σ := (248230383/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (791739664/837321661 : ℝ) ^ p + (827179394/837321661 : ℝ) ^ p := by
    exact cert_lt (x := (791739664/837321661 : ℝ)) (y := (827179394/837321661 : ℝ)) (X := (25642772351209/100000000000000 : ℝ)) (Y := (74357228857617/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (2897073/3125000 : ℝ)) (n' := (837321661/1000000000 : ℝ)) (Ab := (49483729/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (927295861/1000000000 : ℝ) ^ p + (124109303/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (927295861/1000000000 : ℝ)) (y := (124109303/125000000 : ℝ)) (X := (7979311895381/50000000000000 : ℝ)) (Y := (84041393084763/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124109303/125000000 : ℝ) ^ p + (927295861/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124109303/125000000 : ℝ)) (y := (927295861/1000000000 : ℝ)) (X := (84041393084763/100000000000000 : ℝ)) (Y := (7979311895381/50000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (384034057/200000000 : ℝ)) (τ := (927295861/1000000000 : ℝ)) (σ := (124109303/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (791988977/837595049 : ℝ) ^ p + (827452782/837595049 : ℝ) ^ p := by
    exact cert_lt (x := (791988977/837595049 : ℝ)) (y := (827452782/837595049 : ℝ)) (X := (1602221085123/6250000000000 : ℝ)) (Y := (7436446411113/10000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (927295861/1000000000 : ℝ)) (n' := (837595049/1000000000 : ℝ)) (Ab := (791988977/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (927305507/1000000000 : ℝ) ^ p + (992872463/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927305507/1000000000 : ℝ)) (y := (992872463/1000000000 : ℝ)) (X := (15962660306513/100000000000000 : ℝ)) (Y := (16807471519217/20000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992872463/1000000000 : ℝ) ^ p + (927305507/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992872463/1000000000 : ℝ)) (y := (927305507/1000000000 : ℝ)) (X := (16807471519217/20000000000000 : ℝ)) (Y := (15962660306513/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (192017797/100000000 : ℝ)) (τ := (927305507/1000000000 : ℝ)) (σ := (992872463/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (263999773/279202130 : ℝ) ^ p + (827464123/837606390 : ℝ) ^ p := by
    exact cert_lt (x := (263999773/279202130 : ℝ)) (y := (827464123/837606390 : ℝ)) (X := (25635237145613/100000000000000 : ℝ)) (Y := (18591191041227/25000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (927305507/1000000000 : ℝ)) (n' := (83760639/100000000 : ℝ)) (Ab := (791999319/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231826477/250000000 : ℝ) ^ p + (992872381/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (231826477/250000000 : ℝ)) (y := (992872381/1000000000 : ℝ)) (X := (1596282813227/10000000000000 : ℝ)) (Y := (84037188854557/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992872381/1000000000 : ℝ) ^ p + (231826477/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992872381/1000000000 : ℝ)) (y := (231826477/250000000 : ℝ)) (X := (84037188854557/100000000000000 : ℝ)) (Y := (1596282813227/10000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1920178289/1000000000 : ℝ)) (τ := (231826477/250000000 : ℝ)) (σ := (992872381/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (791999749/837606862 : ℝ) ^ p + (827464595/837606862 : ℝ) ^ p := by
    exact cert_lt (x := (791999749/837606862 : ℝ)) (y := (827464595/837606862 : ℝ)) (X := (3204403039817/12500000000000 : ℝ)) (Y := (37182388326333/50000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231826477/250000000 : ℝ)) (n' := (418803431/500000000 : ℝ)) (Ab := (791999749/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (231826481/250000000 : ℝ) ^ p + (496436189/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (231826481/250000000 : ℝ)) (y := (496436189/500000000 : ℝ)) (X := (7981417414297/50000000000000 : ℝ)) (Y := (84037182681093/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496436189/500000000 : ℝ) ^ p + (231826481/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496436189/500000000 : ℝ)) (y := (231826481/250000000 : ℝ)) (X := (84037182681093/100000000000000 : ℝ)) (Y := (7981417414297/50000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (960089151/500000000 : ℝ)) (τ := (231826481/250000000 : ℝ)) (σ := (496436189/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (791999767/837606881 : ℝ) ^ p + (827464614/837606881 : ℝ) ^ p := by
    exact cert_lt (x := (791999767/837606881 : ℝ)) (y := (827464614/837606881 : ℝ)) (X := (5127044869143/20000000000000 : ℝ)) (Y := (74364777155351/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (231826481/250000000 : ℝ)) (n' := (837606881/1000000000 : ℝ)) (Ab := (791999767/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (960089151/500000000 : ℝ)) (τ := (231826481/250000000 : ℝ)) (σ := (496436189/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (231826481/250000000 : ℝ)) (n' := (837606881/1000000000 : ℝ)) (Ab := (791999767/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (960089151/500000000 : ℝ)) (τ := (231826481/250000000 : ℝ)) (σ := (496436189/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (231826481/250000000 : ℝ)) (n' := (837606881/1000000000 : ℝ)) (Ab := (791999767/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (960089151/500000000 : ℝ)) (τ := (231826481/250000000 : ℝ)) (σ := (496436189/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (231826481/250000000 : ℝ)) (n' := (837606881/1000000000 : ℝ)) (Ab := (791999767/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (960089151/500000000 : ℝ)) (τ := (231826481/250000000 : ℝ)) (σ := (496436189/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (231826481/250000000 : ℝ)) (n' := (837606881/1000000000 : ℝ)) (Ab := (791999767/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (960089151/500000000 : ℝ)) (τ := (231826481/250000000 : ℝ)) (σ := (496436189/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1659810071/1806292305 : ℝ) ^ p + (1796150038/1806292305 : ℝ) ^ p := by
    exact cert_lt (x := (1659810071/1806292305 : ℝ)) (y := (1796150038/1806292305 : ℝ)) (X := (1279412868229/10000000000000 : ℝ)) (Y := (87205871555737/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1114246411/1193707695 : ℝ) ^ p + (1183565428/1193707695 : ℝ) ^ p := by
    exact cert_lt (x := (1114246411/1193707695 : ℝ)) (y := (1183565428/1193707695 : ℝ)) (X := (2341849809819/12500000000000 : ℝ)) (Y := (81265202213299/100000000000000 : ℝ)) 389 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496436189/500000000 : ℝ)) (U := (238741539/200000000 : ℝ)) (Ab := (1659810071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (231826481/250000000 : ℝ)) (σ := (496436189/500000000 : ℝ)) (Ab := (1114246411/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab105
