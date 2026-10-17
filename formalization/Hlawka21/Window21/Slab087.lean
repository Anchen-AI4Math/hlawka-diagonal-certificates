import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 87, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab087 (p : ℝ) (hpa : (759/32 : ℝ) ≤ p) (hpb : p ≤ (95/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2096873227469/103603500000000 : ℝ) (10419801/1000000000 : ℝ) (4000000621621/20720700000000 : ℝ) (3033/2500 : ℝ) (971236629/500000000 : ℝ) (971199283/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (9547829/8000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2781/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(2293/5000 : ℝ)
      else (1547/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11849/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2096873227469/103603500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10419801/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (919561247/1000000000 : ℝ) ^ p + (248460259/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (919561247/1000000000 : ℝ)) (y := (248460259/250000000 : ℝ)) (X := (1705888733473/12500000000000 : ℝ)) (Y := (86352907955739/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248460259/250000000 : ℝ) ^ p + (919561247/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248460259/250000000 : ℝ)) (y := (919561247/1000000000 : ℝ)) (X := (86352907955739/100000000000000 : ℝ)) (Y := (1705888733473/12500000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1913402283/1000000000 : ℝ)) (τ := (919561247/1000000000 : ℝ)) (σ := (248460259/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (71199579/75360860 : ℝ) ^ p + (818549659/828969460 : ℝ) ^ p := by
    exact cert_lt (x := (71199579/75360860 : ℝ)) (y := (818549659/828969460 : ℝ)) (X := (25949262558339/100000000000000 : ℝ)) (Y := (37025369408611/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (919561247/1000000000 : ℝ)) (n' := (41448473/50000000 : ℝ)) (Ab := (783195369/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (185037047/200000000 : ℝ) ^ p + (992798191/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (185037047/200000000 : ℝ)) (y := (992798191/1000000000 : ℝ)) (X := (3943405825401/25000000000000 : ℝ)) (Y := (4211319698427/5000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992798191/1000000000 : ℝ) ^ p + (185037047/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992798191/1000000000 : ℝ)) (y := (185037047/200000000 : ℝ)) (X := (4211319698427/5000000000000 : ℝ)) (Y := (3943405825401/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (958991713/500000000 : ℝ)) (τ := (185037047/200000000 : ℝ)) (σ := (992798191/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (263083604/278540513 : ℝ) ^ p + (275067246/278540513 : ℝ) ^ p := by
    exact cert_lt (x := (263083604/278540513 : ℝ)) (y := (275067246/278540513 : ℝ)) (X := (1610677312601/6250000000000 : ℝ)) (Y := (74229163881759/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (185037047/200000000 : ℝ)) (n' := (835621539/1000000000 : ℝ)) (Ab := (197312703/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115678587/125000000 : ℝ) ^ p + (99274909/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (115678587/125000000 : ℝ)) (y := (99274909/100000000 : ℝ)) (X := (7936250266881/50000000000000 : ℝ)) (Y := (84127516605247/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99274909/100000000 : ℝ) ^ p + (115678587/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (99274909/100000000 : ℝ)) (y := (115678587/125000000 : ℝ)) (X := (84127516605247/100000000000000 : ℝ)) (Y := (7936250266881/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (959088893/500000000 : ℝ)) (τ := (115678587/125000000 : ℝ)) (σ := (99274909/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (78951209/83590861 : ℝ) ^ p + (825488809/835908610 : ℝ) ^ p := by
    exact cert_lt (x := (78951209/83590861 : ℝ)) (y := (825488809/835908610 : ℝ)) (X := (25763192263521/100000000000000 : ℝ)) (Y := (18559202272941/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115678587/125000000 : ℝ)) (n' := (83590861/100000000 : ℝ)) (Ab := (78951209/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (7403513/8000000 : ℝ) ^ p + (992746979/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7403513/8000000 : ℝ)) (y := (992746979/1000000000 : ℝ)) (X := (3969187328681/25000000000000 : ℝ)) (Y := (42061634031633/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992746979/1000000000 : ℝ) ^ p + (7403513/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992746979/1000000000 : ℝ)) (y := (7403513/8000000 : ℝ)) (X := (42061634031633/50000000000000 : ℝ)) (Y := (3969187328681/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239773263/125000000 : ℝ)) (τ := (7403513/8000000 : ℝ)) (σ := (992746979/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (263174427/278640302 : ℝ) ^ p + (275167035/278640302 : ℝ) ^ p := by
    exact cert_lt (x := (263174427/278640302 : ℝ)) (y := (275167035/278640302 : ℝ)) (X := (2576286481587/10000000000000 : ℝ)) (Y := (37118568227811/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (7403513/8000000 : ℝ)) (n' := (417960453/500000000 : ℝ)) (Ab := (789523281/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231359893/250000000 : ℝ) ^ p + (124093361/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (231359893/250000000 : ℝ)) (y := (124093361/125000000 : ℝ)) (X := (7938465723571/50000000000000 : ℝ)) (Y := (5257692807733/6250000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (124093361/125000000 : ℝ) ^ p + (231359893/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124093361/125000000 : ℝ)) (y := (231359893/250000000 : ℝ)) (X := (5257692807733/6250000000000 : ℝ)) (Y := (7938465723571/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (95909323/50000000 : ℝ)) (τ := (231359893/250000000 : ℝ)) (σ := (124093361/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (789523761/835921433 : ℝ) ^ p + (825501632/835921433 : ℝ) ^ p := by
    exact cert_lt (x := (789523761/835921433 : ℝ)) (y := (825501632/835921433 : ℝ)) (X := (3220356382589/12500000000000 : ℝ)) (Y := (37118575243039/50000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231359893/250000000 : ℝ)) (n' := (835921433/1000000000 : ℝ)) (Ab := (789523761/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (925439591/1000000000 : ℝ) ^ p + (248186721/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925439591/1000000000 : ℝ)) (y := (248186721/250000000 : ℝ)) (X := (15876939188833/100000000000000 : ℝ)) (Y := (84123076873647/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248186721/250000000 : ℝ) ^ p + (925439591/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248186721/250000000 : ℝ)) (y := (925439591/1000000000 : ℝ)) (X := (84123076873647/100000000000000 : ℝ)) (Y := (15876939188833/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (76727459/40000000 : ℝ)) (τ := (925439591/1000000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (789523781/835921455 : ℝ) ^ p + (275167218/278640485 : ℝ) ^ p := by
    exact cert_lt (x := (789523781/835921455 : ℝ)) (y := (275167218/278640485 : ℝ)) (X := (12881425228541/50000000000000 : ℝ)) (Y := (74237151071789/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (925439591/1000000000 : ℝ)) (n' := (167184291/200000000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (115679949/125000000 : ℝ) ^ p + (248186721/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (115679949/125000000 : ℝ)) (y := (248186721/250000000 : ℝ)) (X := (15876939596291/100000000000000 : ℝ)) (Y := (84123076873647/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248186721/250000000 : ℝ) ^ p + (115679949/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (248186721/250000000 : ℝ)) (y := (115679949/125000000 : ℝ)) (X := (84123076873647/100000000000000 : ℝ)) (Y := (15876939596291/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (789523781/835921456 : ℝ) ^ p + (825501655/835921456 : ℝ) ^ p := by
    exact cert_lt (x := (789523781/835921456 : ℝ)) (y := (825501655/835921456 : ℝ)) (X := (12881424862557/50000000000000 : ℝ)) (Y := (18559287774603/25000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (n' := (52245091/62500000 : ℝ)) (Ab := (789523781/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (479546619/250000000 : ℝ)) (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1656929089/1806521375 : ℝ) ^ p + (1796101574/1806521375 : ℝ) ^ p := by
    exact cert_lt (x := (1656929089/1806521375 : ℝ)) (y := (1796101574/1806521375 : ℝ)) (X := (1604554372411/12500000000000 : ℝ)) (Y := (87163565311391/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112380767/1193478625 : ℝ) ^ p + (1183058824/1193478625 : ℝ) ^ p := by
    exact cert_lt (x := (1112380767/1193478625 : ℝ)) (y := (1183058824/1193478625 : ℝ)) (X := (18800617722157/100000000000000 : ℝ)) (Y := (81199383009411/100000000000000 : ℝ)) 95 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248186721/250000000 : ℝ)) (U := (9547829/8000000 : ℝ)) (Ab := (1656929089/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (115679949/125000000 : ℝ)) (σ := (248186721/250000000 : ℝ)) (Ab := (1112380767/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab087
