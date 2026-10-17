import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 31, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab031 (p : ℝ) (hpa : (703/32 : ℝ) ≤ p) (hpb : p ≤ (22 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2117593852121/95959500000000 : ℝ) (11387473/1000000000 : ℝ) (4000000575757/19191900000000 : ℝ) (3033/2500 : ℝ) (484492237/250000000 : ℝ) (968941047/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (119277271/100000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5531/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(179/400 : ℝ)
      else (7627/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11837/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2117593852121/95959500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11387473/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (912804267/1000000000 : ℝ) ^ p + (62091399/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (912804267/1000000000 : ℝ)) (y := (62091399/62500000 : ℝ)) (X := (6718596492501/50000000000000 : ℝ)) (Y := (86562823205107/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (62091399/62500000 : ℝ) ^ p + (912804267/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62091399/62500000 : ℝ)) (y := (912804267/1000000000 : ℝ)) (X := (86562823205107/100000000000000 : ℝ)) (Y := (6718596492501/50000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1906266651/1000000000 : ℝ)) (τ := (912804267/1000000000 : ℝ)) (σ := (62091399/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (774317326/822624653 : ℝ) ^ p + (811237180/822624653 : ℝ) ^ p := by
    exact cert_lt (x := (774317326/822624653 : ℝ)) (y := (811237180/822624653 : ℝ)) (X := (26410683585767/100000000000000 : ℝ)) (Y := (18397329320939/25000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (912804267/1000000000 : ℝ)) (n' := (822624653/1000000000 : ℝ)) (Ab := (387158663/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (459333/500000 : ℝ) ^ p + (248097569/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (459333/500000 : ℝ)) (y := (248097569/250000000 : ℝ)) (X := (15469210661269/100000000000000 : ℝ)) (Y := (42265402367607/50000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248097569/250000000 : ℝ) ^ p + (459333/500000 : ℝ) ^ p := by
    exact cert_lt (x := (248097569/250000000 : ℝ)) (y := (459333/500000 : ℝ)) (X := (42265402367607/50000000000000 : ℝ)) (Y := (15469210661269/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (477764069/250000000 : ℝ)) (τ := (459333/500000 : ℝ)) (σ := (248097569/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (780648585/829626038 : ℝ) ^ p + (818238565/829626038 : ℝ) ^ p := by
    exact cert_lt (x := (780648585/829626038 : ℝ)) (y := (818238565/829626038 : ℝ)) (X := (524373164197/2000000000000 : ℝ)) (Y := (737813427573/1000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (459333/500000 : ℝ)) (n' := (414813019/500000000 : ℝ)) (Ab := (156129717/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (183789687/200000000 : ℝ) ^ p + (992334229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183789687/200000000 : ℝ)) (y := (992334229/1000000000 : ℝ)) (X := (7787089010381/50000000000000 : ℝ)) (Y := (10553229799933/12500000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992334229/1000000000 : ℝ) ^ p + (183789687/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992334229/1000000000 : ℝ)) (y := (183789687/200000000 : ℝ)) (X := (10553229799933/12500000000000 : ℝ)) (Y := (7787089010381/50000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (238910333/125000000 : ℝ)) (τ := (183789687/200000000 : ℝ)) (σ := (992334229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (780952584/829962281 : ℝ) ^ p + (818574808/829962281 : ℝ) ^ p := by
    exact cert_lt (x := (780952584/829962281 : ℝ)) (y := (818574808/829962281 : ℝ)) (X := (13104752955437/50000000000000 : ℝ)) (Y := (73790495205053/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (183789687/200000000 : ℝ)) (n' := (829962281/1000000000 : ℝ)) (Ab := (97619073/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (459480947/500000000 : ℝ) ^ p + (992331547/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459480947/500000000 : ℝ)) (y := (992331547/1000000000 : ℝ)) (X := (15579197009891/100000000000000 : ℝ)) (Y := (8442081859801/10000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992331547/1000000000 : ℝ) ^ p + (459480947/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992331547/1000000000 : ℝ)) (y := (459480947/500000000 : ℝ)) (X := (8442081859801/10000000000000 : ℝ)) (Y := (15579197009891/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1911293441/1000000000 : ℝ)) (τ := (459480947/500000000 : ℝ)) (σ := (992331547/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (780967069/829978302 : ℝ) ^ p + (818590829/829978302 : ℝ) ^ p := by
    exact cert_lt (x := (780967069/829978302 : ℝ)) (y := (818590829/829978302 : ℝ)) (X := (13104535168651/50000000000000 : ℝ)) (Y := (73790931134491/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (459480947/500000000 : ℝ)) (n' := (414989151/500000000 : ℝ)) (Ab := (780967069/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (183792507/200000000 : ℝ) ^ p + (992331419/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183792507/200000000 : ℝ)) (y := (992331419/1000000000 : ℝ)) (X := (77897180417/500000000000 : ℝ)) (Y := (5276286189513/6250000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992331419/1000000000 : ℝ) ^ p + (183792507/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992331419/1000000000 : ℝ)) (y := (183792507/200000000 : ℝ)) (X := (5276286189513/6250000000000 : ℝ)) (Y := (77897180417/500000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (955646977/500000000 : ℝ)) (τ := (183792507/200000000 : ℝ)) (σ := (992331419/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (780967758/829979065 : ℝ) ^ p + (818591592/829979065 : ℝ) ^ p := by
    exact cert_lt (x := (780967758/829979065 : ℝ)) (y := (818591592/829979065 : ℝ)) (X := (26209048967607/100000000000000 : ℝ)) (Y := (18447737973817/25000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (183792507/200000000 : ℝ)) (n' := (165995813/200000000 : ℝ)) (Ab := (390483879/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (183792513/200000000 : ℝ) ^ p + (992331413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183792513/200000000 : ℝ)) (y := (992331413/1000000000 : ℝ)) (X := (7789723636287/50000000000000 : ℝ)) (Y := (84420567802577/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992331413/1000000000 : ℝ) ^ p + (183792513/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992331413/1000000000 : ℝ)) (y := (183792513/200000000 : ℝ)) (X := (84420567802577/100000000000000 : ℝ)) (Y := (7789723636287/50000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (955646989/500000000 : ℝ)) (τ := (183792513/200000000 : ℝ)) (σ := (992331413/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (78096779/82997910 : ℝ) ^ p + (818591627/829979100 : ℝ) ^ p := by
    exact cert_lt (x := (78096779/82997910 : ℝ)) (y := (818591627/829979100 : ℝ)) (X := (1638065517413/6250000000000 : ℝ)) (Y := (73790952847597/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (183792513/200000000 : ℝ)) (n' := (8299791/10000000 : ℝ)) (Ab := (78096779/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (459481283/500000000 : ℝ) ^ p + (992331413/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459481283/500000000 : ℝ)) (y := (992331413/1000000000 : ℝ)) (X := (7789723822773/50000000000000 : ℝ)) (Y := (84420567802577/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992331413/1000000000 : ℝ) ^ p + (459481283/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992331413/1000000000 : ℝ)) (y := (459481283/500000000 : ℝ)) (X := (84420567802577/100000000000000 : ℝ)) (Y := (7789723822773/50000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1911293979/1000000000 : ℝ)) (τ := (459481283/500000000 : ℝ)) (σ := (992331413/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (390483896/414989551 : ℝ) ^ p + (818591629/829979102 : ℝ) ^ p := by
    exact cert_lt (x := (390483896/414989551 : ℝ)) (y := (818591629/829979102 : ℝ)) (X := (5241809673161/20000000000000 : ℝ)) (Y := (576491819547/781250000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (459481283/500000000 : ℝ)) (n' := (414989551/500000000 : ℝ)) (Ab := (48810487/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1911293979/1000000000 : ℝ)) (τ := (459481283/500000000 : ℝ)) (σ := (992331413/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (459481283/500000000 : ℝ)) (n' := (414989551/500000000 : ℝ)) (Ab := (48810487/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1911293979/1000000000 : ℝ)) (τ := (459481283/500000000 : ℝ)) (σ := (992331413/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (459481283/500000000 : ℝ)) (n' := (414989551/500000000 : ℝ)) (Ab := (48810487/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1911293979/1000000000 : ℝ)) (τ := (459481283/500000000 : ℝ)) (σ := (992331413/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (459481283/500000000 : ℝ)) (n' := (414989551/500000000 : ℝ)) (Ab := (48810487/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1911293979/1000000000 : ℝ)) (τ := (459481283/500000000 : ℝ)) (σ := (992331413/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (823533092/903613645 : ℝ) ^ p + (1795839817/1807227290 : ℝ) ^ p := by
    exact cert_lt (x := (823533092/903613645 : ℝ)) (y := (1795839817/1807227290 : ℝ)) (X := (1622826374549/12500000000000 : ℝ)) (Y := (87017389190121/100000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (221223343/238554542 : ℝ) ^ p + (1181385237/1192772710 : ℝ) ^ p := by
    exact cert_lt (x := (221223343/238554542 : ℝ)) (y := (1181385237/1192772710 : ℝ)) (X := (9513093109741/50000000000000 : ℝ)) (Y := (16194762854367/20000000000000 : ℝ)) 22 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992331413/1000000000 : ℝ)) (U := (119277271/100000000 : ℝ)) (Ab := (205883273/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (459481283/500000000 : ℝ)) (σ := (992331413/1000000000 : ℝ)) (Ab := (221223343/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab031
