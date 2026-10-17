import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 94, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab094 (p : ℝ) (hpa : (383/16 : ℝ) ≤ p) (hpb : p ≤ (767/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (8181616217/408433593750 : ℝ) (10310111/1000000000 : ℝ) (2000000313677/10455900000000 : ℝ) (3033/2500 : ℝ) (3035923/1562500 : ℝ) (485729341/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193567701/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2783/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2299/5000 : ℝ)
      else (1937/2500 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (8181616217/408433593750 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10310111/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (920333191/1000000000 : ℝ) ^ p + (31058921/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (920333191/1000000000 : ℝ)) (y := (31058921/31250000 : ℝ)) (X := (6835633264541/50000000000000 : ℝ)) (Y := (86328750865629/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (31058921/31250000 : ℝ) ^ p + (920333191/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31058921/31250000 : ℝ)) (y := (920333191/1000000000 : ℝ)) (X := (86328750865629/100000000000000 : ℝ)) (Y := (6835633264541/50000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1914218663/1000000000 : ℝ)) (τ := (920333191/1000000000 : ℝ)) (σ := (31058921/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (784212340/829685441 : ℝ) ^ p + (2043330/2069041 : ℝ) ^ p := by
    exact cert_lt (x := (784212340/829685441 : ℝ)) (y := (2043330/2069041 : ℝ)) (X := (25897023733963/100000000000000 : ℝ)) (Y := (741029771761/1000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (920333191/1000000000 : ℝ)) (n' := (829685441/1000000000 : ℝ)) (Ab := (39210617/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (231481763/250000000 : ℝ) ^ p + (3878307/3906250 : ℝ) ^ p := by
    exact cert_lt (x := (231481763/250000000 : ℝ)) (y := (3878307/3906250 : ℝ)) (X := (3952091845817/25000000000000 : ℝ)) (Y := (84191649540627/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (3878307/3906250 : ℝ) ^ p + (231481763/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (3878307/3906250 : ℝ)) (y := (231481763/250000000 : ℝ)) (X := (84191649540627/100000000000000 : ℝ)) (Y := (3952091845817/25000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (479693411/250000000 : ℝ)) (τ := (231481763/250000000 : ℝ)) (σ := (3878307/3906250 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (21950924/23230403 : ℝ) ^ p + (117997771/119470644 : ℝ) ^ p := by
    exact cert_lt (x := (21950924/23230403 : ℝ)) (y := (117997771/119470644 : ℝ)) (X := (1028808053799/4000000000000 : ℝ)) (Y := (74279800053873/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (231481763/250000000 : ℝ)) (n' := (209073627/250000000 : ℝ)) (Ab := (49389579/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115770771/125000000 : ℝ) ^ p + (992798279/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115770771/125000000 : ℝ)) (y := (992798279/1000000000 : ℝ)) (X := (15906508912023/100000000000000 : ℝ)) (Y := (10511688480057/12500000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992798279/1000000000 : ℝ) ^ p + (115770771/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992798279/1000000000 : ℝ)) (y := (115770771/125000000 : ℝ)) (X := (10511688480057/12500000000000 : ℝ)) (Y := (15906508912023/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918964447/1000000000 : ℝ)) (τ := (115770771/125000000 : ℝ)) (σ := (992798279/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (197622449/209144037 : ℝ) ^ p + (826266037/836576148 : ℝ) ^ p := by
    exact cert_lt (x := (197622449/209144037 : ℝ)) (y := (826266037/836576148 : ℝ)) (X := (12856359453513/50000000000000 : ℝ)) (Y := (14857456409817/20000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115770771/125000000 : ℝ)) (n' := (209144037/250000000 : ℝ)) (Ab := (197622449/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (926176283/1000000000 : ℝ) ^ p + (248199057/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (926176283/1000000000 : ℝ)) (y := (248199057/250000000 : ℝ)) (X := (15910673305003/100000000000000 : ℝ)) (Y := (21022335980549/25000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248199057/250000000 : ℝ) ^ p + (926176283/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248199057/250000000 : ℝ)) (y := (926176283/1000000000 : ℝ)) (X := (21022335980549/25000000000000 : ℝ)) (Y := (15910673305003/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1918972511/1000000000 : ℝ)) (τ := (926176283/1000000000 : ℝ)) (σ := (248199057/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (395250323/418294030 : ℝ) ^ p + (118039707/119512580 : ℝ) ^ p := by
    exact cert_lt (x := (395250323/418294030 : ℝ)) (y := (118039707/119512580 : ℝ)) (X := (25712402551333/100000000000000 : ℝ)) (Y := (37143799202953/50000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (926176283/1000000000 : ℝ)) (n' := (41829403/50000000 : ℝ)) (Ab := (395250323/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (926176711/1000000000 : ℝ) ^ p + (992796141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926176711/1000000000 : ℝ)) (y := (992796141/1000000000 : ℝ)) (X := (15910849537649/100000000000000 : ℝ)) (Y := (16817833460019/20000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992796141/1000000000 : ℝ) ^ p + (926176711/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992796141/1000000000 : ℝ)) (y := (926176711/1000000000 : ℝ)) (X := (16817833460019/20000000000000 : ℝ)) (Y := (15910849537649/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479743213/250000000 : ℝ)) (τ := (926176711/1000000000 : ℝ)) (σ := (992796141/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (46500065/49211092 : ℝ) ^ p + (118039779/119512652 : ℝ) ^ p := by
    exact cert_lt (x := (46500065/49211092 : ℝ)) (y := (118039779/119512652 : ℝ)) (X := (12856194557341/50000000000000 : ℝ)) (Y := (464297573693/625000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (926176711/1000000000 : ℝ)) (n' := (209147141/250000000 : ℝ)) (Ab := (158100221/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (115772091/125000000 : ℝ) ^ p + (496398069/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (115772091/125000000 : ℝ)) (y := (496398069/500000000 : ℝ)) (X := (7955428268791/50000000000000 : ℝ)) (Y := (21022290302421/25000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496398069/500000000 : ℝ) ^ p + (115772091/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496398069/500000000 : ℝ)) (y := (115772091/125000000 : ℝ)) (X := (21022290302421/25000000000000 : ℝ)) (Y := (7955428268791/50000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (959486433/500000000 : ℝ)) (τ := (115772091/125000000 : ℝ)) (σ := (496398069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (197625281/209147146 : ℝ) ^ p + (826278473/836588584 : ℝ) ^ p := by
    exact cert_lt (x := (197625281/209147146 : ℝ)) (y := (826278473/836588584 : ℝ)) (X := (6428097298511/25000000000000 : ℝ)) (Y := (74287612322029/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (115772091/125000000 : ℝ)) (n' := (104573573/125000000 : ℝ)) (Ab := (197625281/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (92617673/100000000 : ℝ) ^ p + (992796137/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (92617673/100000000 : ℝ)) (y := (992796137/1000000000 : ℝ)) (X := (994428585069/6250000000000 : ℝ)) (Y := (84089159179547/100000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992796137/1000000000 : ℝ) ^ p + (92617673/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (992796137/1000000000 : ℝ)) (y := (92617673/100000000 : ℝ)) (X := (84089159179547/100000000000000 : ℝ)) (Y := (994428585069/6250000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (263500375/278862862 : ℝ) ^ p + (826278475/836588586 : ℝ) ^ p := by
    exact cert_lt (x := (263500375/278862862 : ℝ)) (y := (826278475/836588586 : ℝ)) (X := (12856194250159/50000000000000 : ℝ)) (Y := (9285951546893/12500000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (n' := (418294293/500000000 : ℝ)) (Ab := (6324009/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918972867/1000000000 : ℝ)) (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1658064868/1806432299 : ℝ) ^ p + (256588884/258061757 : ℝ) ^ p := by
    exact cert_lt (x := (1658064868/1806432299 : ℝ)) (y := (256588884/258061757 : ℝ)) (X := (12819733298299/100000000000000 : ℝ)) (Y := (435901334493/500000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1113114315/1193567701 : ℝ) ^ p + (1183257590/1193567701 : ℝ) ^ p := by
    exact cert_lt (x := (1113114315/1193567701 : ℝ)) (y := (1183257590/1193567701 : ℝ)) (X := (3754932547137/20000000000000 : ℝ)) (Y := (16245067602591/20000000000000 : ℝ)) 767 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992796137/1000000000 : ℝ)) (U := (1193567701/1000000000 : ℝ)) (Ab := (414516217/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (92617673/100000000 : ℝ)) (σ := (992796137/1000000000 : ℝ)) (Ab := (222622863/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab094
