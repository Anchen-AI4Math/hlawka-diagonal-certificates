import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 50, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab050 (p : ℝ) (hpa : (361/16 : ℝ) ≤ p) (hpb : p ≤ (723/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527551819709/24638250000000 : ℝ) (2759989/250000000 : ℝ) (2000000295659/9855300000000 : ℝ) (3033/2500 : ℝ) (969787103/500000000 : ℝ) (121218237/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (238601993/200000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2771/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(903/2000 : ℝ)
      else (3833/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527551819709/24638250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2759989/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (915220059/1000000000 : ℝ) ^ p + (496797827/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (915220059/1000000000 : ℝ)) (y := (496797827/500000000 : ℝ)) (X := (540477271877/4000000000000 : ℝ)) (Y := (10811010606323/12500000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496797827/500000000 : ℝ) ^ p + (915220059/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496797827/500000000 : ℝ)) (y := (915220059/1000000000 : ℝ)) (X := (10811010606323/12500000000000 : ℝ)) (Y := (540477271877/4000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1908815713/1000000000 : ℝ)) (τ := (915220059/1000000000 : ℝ)) (σ := (496797827/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (777486665/824909074 : ℝ) ^ p + (406934559/412454537 : ℝ) ^ p := by
    exact cert_lt (x := (777486665/824909074 : ℝ)) (y := (406934559/412454537 : ℝ)) (X := (6561209958691/25000000000000 : ℝ)) (Y := (14751032287461/20000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (915220059/1000000000 : ℝ)) (n' := (412454537/500000000 : ℝ)) (Ab := (155497333/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (230250557/250000000 : ℝ) ^ p + (992532881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230250557/250000000 : ℝ)) (y := (992532881/1000000000 : ℝ)) (X := (7789054833381/50000000000000 : ℝ)) (Y := (21105476614877/25000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992532881/1000000000 : ℝ) ^ p + (230250557/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992532881/1000000000 : ℝ)) (y := (230250557/250000000 : ℝ)) (X := (21105476614877/25000000000000 : ℝ)) (Y := (7789054833381/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1913535109/1000000000 : ℝ)) (τ := (230250557/250000000 : ℝ)) (σ := (992532881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (391862421/415895660 : ℝ) ^ p + (205187841/207947830 : ℝ) ^ p := by
    exact cert_lt (x := (391862421/415895660 : ℝ)) (y := (205187841/207947830 : ℝ)) (X := (26057583660901/100000000000000 : ℝ)) (Y := (1848560435233/2500000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (230250557/250000000 : ℝ)) (n' := (20794783/25000000 : ℝ)) (Ab := (391862421/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115158819/125000000 : ℝ) ^ p + (992479323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115158819/125000000 : ℝ)) (y := (992479323/1000000000 : ℝ)) (X := (15680974894959/100000000000000 : ℝ)) (Y := (84319040917659/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992479323/1000000000 : ℝ) ^ p + (115158819/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992479323/1000000000 : ℝ)) (y := (115158819/125000000 : ℝ)) (X := (84319040917659/100000000000000 : ℝ)) (Y := (15680974894959/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (15309999/8000000 : ℝ)) (τ := (115158819/125000000 : ℝ)) (σ := (992479323/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784013341/832109667 : ℝ) ^ p + (821069711/832109667 : ℝ) ^ p := by
    exact cert_lt (x := (784013341/832109667 : ℝ)) (y := (821069711/832109667 : ℝ)) (X := (26048985668903/100000000000000 : ℝ)) (Y := (73951015103983/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115158819/125000000 : ℝ)) (n' := (832109667/1000000000 : ℝ)) (Ab := (784013341/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (230320717/250000000 : ℝ) ^ p + (198495371/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (230320717/250000000 : ℝ)) (y := (198495371/200000000 : ℝ)) (X := (15685711929547/100000000000000 : ℝ)) (Y := (8431430367093/10000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198495371/200000000 : ℝ) ^ p + (230320717/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (198495371/200000000 : ℝ)) (y := (230320717/250000000 : ℝ)) (X := (8431430367093/10000000000000 : ℝ)) (Y := (15685711929547/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1913759723/1000000000 : ℝ)) (τ := (230320717/250000000 : ℝ)) (σ := (198495371/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (261342194/277374759 : ℝ) ^ p + (821084321/832124277 : ℝ) ^ p := by
    exact cert_lt (x := (261342194/277374759 : ℝ)) (y := (821084321/832124277 : ℝ)) (X := (3256073989977/12500000000000 : ℝ)) (Y := (36975704772877/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (230320717/250000000 : ℝ)) (n' := (832124277/1000000000 : ℝ)) (Ab := (392013291/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921283433/1000000000 : ℝ) ^ p + (496238371/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (921283433/1000000000 : ℝ)) (y := (496238371/500000000 : ℝ)) (X := (7842964637581/50000000000000 : ℝ)) (Y := (84314086777149/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496238371/500000000 : ℝ) ^ p + (921283433/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496238371/500000000 : ℝ)) (y := (921283433/1000000000 : ℝ)) (X := (84314086777149/100000000000000 : ℝ)) (Y := (7842964637581/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (76550407/40000000 : ℝ)) (τ := (921283433/1000000000 : ℝ)) (σ := (496238371/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784027189/832124947 : ℝ) ^ p + (821084991/832124947 : ℝ) ^ p := by
    exact cert_lt (x := (784027189/832124947 : ℝ)) (y := (821084991/832124947 : ℝ)) (X := (2604857369893/10000000000000 : ℝ)) (Y := (72218191049/97656250000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921283433/1000000000 : ℝ)) (n' := (832124947/1000000000 : ℝ)) (Ab := (784027189/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (460641729/500000000 : ℝ) ^ p + (992476737/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460641729/500000000 : ℝ)) (y := (992476737/1000000000 : ℝ)) (X := (15685938892291/100000000000000 : ℝ)) (Y := (21078519295023/25000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992476737/1000000000 : ℝ) ^ p + (460641729/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992476737/1000000000 : ℝ)) (y := (460641729/500000000 : ℝ)) (X := (21078519295023/25000000000000 : ℝ)) (Y := (15685938892291/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (382752039/200000000 : ℝ)) (τ := (460641729/500000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784027216/832124977 : ℝ) ^ p + (821085021/832124977 : ℝ) ^ p := by
    exact cert_lt (x := (784027216/832124977 : ℝ)) (y := (821085021/832124977 : ℝ)) (X := (1628035796789/6250000000000 : ℝ)) (Y := (14790285688821/20000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (460641729/500000000 : ℝ)) (n' := (832124977/1000000000 : ℝ)) (Ab := (49001701/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (921283459/1000000000 : ℝ) ^ p + (992476737/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921283459/1000000000 : ℝ)) (y := (992476737/1000000000 : ℝ)) (X := (980371204811/6250000000000 : ℝ)) (Y := (21078519295023/25000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992476737/1000000000 : ℝ) ^ p + (921283459/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992476737/1000000000 : ℝ)) (y := (921283459/1000000000 : ℝ)) (X := (21078519295023/25000000000000 : ℝ)) (Y := (980371204811/6250000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (784027217/832124978 : ℝ) ^ p + (410542511/416062489 : ℝ) ^ p := by
    exact cert_lt (x := (784027217/832124978 : ℝ)) (y := (410542511/416062489 : ℝ)) (X := (26048572792013/100000000000000 : ℝ)) (Y := (36975714235551/50000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (n' := (416062489/500000000 : ℝ)) (Ab := (784027217/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (478440049/250000000 : ℝ)) (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1650576292/1806990035 : ℝ) ^ p + (1795950079/1806990035 : ℝ) ^ p := by
    exact cert_lt (x := (1650576292/1806990035 : ℝ)) (y := (1795950079/1806990035 : ℝ)) (X := (6465174608077/50000000000000 : ℝ)) (Y := (87069651134273/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108324274/1193009965 : ℝ) ^ p + (1181970009/1193009965 : ℝ) ^ p := by
    exact cert_lt (x := (1108324274/1193009965 : ℝ)) (y := (1181970009/1193009965 : ℝ)) (X := (4736467414643/25000000000000 : ℝ)) (Y := (81054130781519/100000000000000 : ℝ)) 723 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992476737/1000000000 : ℝ)) (U := (238601993/200000000 : ℝ)) (Ab := (412644073/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (921283459/1000000000 : ℝ)) (σ := (992476737/1000000000 : ℝ)) (Ab := (554162137/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab050
