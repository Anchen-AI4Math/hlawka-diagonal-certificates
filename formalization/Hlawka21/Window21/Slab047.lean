import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 47, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab047 (p : ℝ) (hpa : (719/32 : ℝ) ≤ p) (hpb : p ≤ (45/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527836838261/24535875000000 : ℝ) (11093431/1000000000 : ℝ) (4000000588861/19628700000000 : ℝ) (3033/2500 : ℝ) (193932629/100000000 : ℝ) (484810799/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596486137/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(277/250 : ℝ) ≤ X j i ∧ X j i ≤ -(4509/10000 : ℝ)
      else (383/500 : ℝ) ≤ X j i ∧ X j i ≤ (148/125 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527836838261/24535875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11093431/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (914847529/1000000000 : ℝ) ^ p + (19871499/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (914847529/1000000000 : ℝ)) (y := (19871499/20000000 : ℝ)) (X := (13500386008909/100000000000000 : ℝ)) (Y := (43249815491523/50000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (19871499/20000000 : ℝ) ^ p + (914847529/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19871499/20000000 : ℝ)) (y := (914847529/1000000000 : ℝ)) (X := (43249815491523/50000000000000 : ℝ)) (Y := (13500386008909/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908422479/1000000000 : ℝ)) (τ := (914847529/1000000000 : ℝ)) (σ := (19871499/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (776997587/824557967 : ℝ) ^ p + (813464536/824557967 : ℝ) ^ p := by
    exact cert_lt (x := (776997587/824557967 : ℝ)) (y := (813464536/824557967 : ℝ)) (X := (5254068694683/20000000000000 : ℝ)) (Y := (36864828702781/50000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (914847529/1000000000 : ℝ)) (n' := (824557967/1000000000 : ℝ)) (Ab := (776997587/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (14385037/15625000 : ℝ) ^ p + (198502131/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (14385037/15625000 : ℝ)) (y := (198502131/200000000 : ℝ)) (X := (7780661880697/50000000000000 : ℝ)) (Y := (84438692571727/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198502131/200000000 : ℝ) ^ p + (14385037/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (198502131/200000000 : ℝ)) (y := (14385037/15625000 : ℝ)) (X := (84438692571727/100000000000000 : ℝ)) (Y := (7780661880697/50000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1913153023/1000000000 : ℝ)) (τ := (14385037/15625000 : ℝ)) (σ := (198502131/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (783250527/831459013 : ℝ) ^ p + (820365582/831459013 : ℝ) ^ p := by
    exact cert_lt (x := (783250527/831459013 : ℝ)) (y := (820365582/831459013 : ℝ)) (X := (26082344856117/100000000000000 : ℝ)) (Y := (36958827999189/50000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (14385037/15625000 : ℝ)) (n' := (831459013/1000000000 : ℝ)) (Ab := (783250527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115114107/125000000 : ℝ) ^ p + (992456713/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115114107/125000000 : ℝ)) (y := (992456713/1000000000 : ℝ)) (X := (15664518691249/100000000000000 : ℝ)) (Y := (21083874184279/25000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992456713/1000000000 : ℝ) ^ p + (115114107/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992456713/1000000000 : ℝ)) (y := (115114107/125000000 : ℝ)) (X := (21083874184279/25000000000000 : ℝ)) (Y := (15664518691249/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1913369569/1000000000 : ℝ)) (τ := (115114107/125000000 : ℝ)) (σ := (992456713/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (783541401/831780097 : ℝ) ^ p + (820686666/831780097 : ℝ) ^ p := by
    exact cert_lt (x := (783541401/831780097 : ℝ)) (y := (820686666/831780097 : ℝ)) (X := (13036831615739/50000000000000 : ℝ)) (Y := (18481584519031/25000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115114107/125000000 : ℝ)) (n' := (831780097/1000000000 : ℝ)) (Ab := (783541401/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (28778917/31250000 : ℝ) ^ p + (992454213/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28778917/31250000 : ℝ)) (y := (992454213/1000000000 : ℝ)) (X := (7834649397033/50000000000000 : ℝ)) (Y := (8433071693849/10000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992454213/1000000000 : ℝ) ^ p + (28778917/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (992454213/1000000000 : ℝ)) (y := (28778917/31250000 : ℝ)) (X := (8433071693849/10000000000000 : ℝ)) (Y := (7834649397033/50000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1913379557/1000000000 : ℝ)) (τ := (28778917/31250000 : ℝ)) (σ := (992454213/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (783554828/831794919 : ℝ) ^ p + (820701488/831794919 : ℝ) ^ p := by
    exact cert_lt (x := (783554828/831794919 : ℝ)) (y := (820701488/831794919 : ℝ)) (X := (13036631185069/50000000000000 : ℝ)) (Y := (73926738723121/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (28778917/31250000 : ℝ)) (n' := (831794919/1000000000 : ℝ)) (Ab := (195888707/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (5755787/6250000 : ℝ) ^ p + (496227049/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (5755787/6250000 : ℝ)) (y := (496227049/500000000 : ℝ)) (X := (1958689913311/12500000000000 : ℝ)) (Y := (84330497073981/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496227049/500000000 : ℝ) ^ p + (5755787/6250000 : ℝ) ^ p := by
    exact cert_lt (x := (496227049/500000000 : ℝ)) (y := (5755787/6250000 : ℝ)) (X := (84330497073981/100000000000000 : ℝ)) (Y := (1958689913311/12500000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (956690009/500000000 : ℝ)) (τ := (5755787/6250000 : ℝ)) (σ := (496227049/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (783555448/831795603 : ℝ) ^ p + (820702172/831795603 : ℝ) ^ p := by
    exact cert_lt (x := (783555448/831795603 : ℝ)) (y := (820702172/831795603 : ℝ)) (X := (13036622076643/50000000000000 : ℝ)) (Y := (73926757211731/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (5755787/6250000 : ℝ)) (n' := (831795603/1000000000 : ℝ)) (Ab := (97944431/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (460462973/500000000 : ℝ) ^ p + (992454093/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460462973/500000000 : ℝ)) (y := (992454093/1000000000 : ℝ)) (X := (3917382315061/25000000000000 : ℝ)) (Y := (84330487514667/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992454093/1000000000 : ℝ) ^ p + (460462973/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992454093/1000000000 : ℝ)) (y := (460462973/500000000 : ℝ)) (X := (84330487514667/100000000000000 : ℝ)) (Y := (3917382315061/25000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1913380039/1000000000 : ℝ)) (τ := (460462973/500000000 : ℝ)) (σ := (992454093/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (783555475/831795633 : ℝ) ^ p + (820702202/831795633 : ℝ) ^ p := by
    exact cert_lt (x := (783555475/831795633 : ℝ)) (y := (820702202/831795633 : ℝ)) (X := (3259155401227/12500000000000 : ℝ)) (Y := (36963379011317/50000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (460462973/500000000 : ℝ)) (n' := (831795633/1000000000 : ℝ)) (Ab := (31342219/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (230231487/250000000 : ℝ) ^ p + (248113523/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (230231487/250000000 : ℝ)) (y := (248113523/250000000 : ℝ)) (X := (15669530025917/100000000000000 : ℝ)) (Y := (21082621400701/25000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248113523/250000000 : ℝ) ^ p + (230231487/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248113523/250000000 : ℝ)) (y := (230231487/250000000 : ℝ)) (X := (21082621400701/25000000000000 : ℝ)) (Y := (15669530025917/100000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (47834501/25000000 : ℝ)) (τ := (230231487/250000000 : ℝ)) (σ := (248113523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (391777739/415897818 : ℝ) ^ p + (820702205/831795636 : ℝ) ^ p := by
    exact cert_lt (x := (391777739/415897818 : ℝ)) (y := (820702205/831795636 : ℝ)) (X := (26073243340079/100000000000000 : ℝ)) (Y := (18481689525931/25000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (230231487/250000000 : ℝ)) (n' := (207948909/250000000 : ℝ)) (Ab := (391777739/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (47834501/25000000 : ℝ)) (τ := (230231487/250000000 : ℝ)) (σ := (248113523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (230231487/250000000 : ℝ)) (n' := (207948909/250000000 : ℝ)) (Ab := (391777739/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (47834501/25000000 : ℝ)) (τ := (230231487/250000000 : ℝ)) (σ := (248113523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (230231487/250000000 : ℝ)) (n' := (207948909/250000000 : ℝ)) (Ab := (391777739/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (47834501/25000000 : ℝ)) (τ := (230231487/250000000 : ℝ)) (σ := (248113523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (230231487/250000000 : ℝ)) (n' := (207948909/250000000 : ℝ)) (Ab := (391777739/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (47834501/25000000 : ℝ)) (τ := (230231487/250000000 : ℝ)) (σ := (248113523/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (825016916/903513863 : ℝ) ^ p + (1795934295/1807027726 : ℝ) ^ p := by
    exact cert_lt (x := (825016916/903513863 : ℝ)) (y := (1795934295/1807027726 : ℝ)) (X := (12938404915461/100000000000000 : ℝ)) (Y := (1741231906729/2000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1107981527/1192972274 : ℝ) ^ p + (1181878843/1192972274 : ℝ) ^ p := by
    exact cert_lt (x := (1107981527/1192972274 : ℝ)) (y := (1181878843/1192972274 : ℝ)) (X := (18958274595931/100000000000000 : ℝ)) (Y := (16208345164437/20000000000000 : ℝ)) 45 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248113523/250000000 : ℝ)) (U := (596486137/500000000 : ℝ)) (Ab := (206254229/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (230231487/250000000 : ℝ)) (σ := (248113523/250000000 : ℝ)) (Ab := (1107981527/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab047
