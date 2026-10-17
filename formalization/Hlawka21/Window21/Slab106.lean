import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 106, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab106 (p : ℝ) (hpa : (389/16 : ℝ) ≤ p) (hpb : p ≤ (779/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (261314247697/13274625000000 : ℝ) (5063637/500000000 : ℝ) (2000000318591/10619700000000 : ℝ) (3033/2500 : ℝ) (971928233/500000000 : ℝ) (485946331/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193720413/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1393/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(4619/10000 : ℝ)
      else (971/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11853/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (261314247697/13274625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5063637/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (184324543/200000000 : ℝ) ^ p + (248490063/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (184324543/200000000 : ℝ)) (y := (248490063/250000000 : ℝ)) (X := (214245279593/1562500000000 : ℝ)) (Y := (13806131409/16000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248490063/250000000 : ℝ) ^ p + (184324543/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (248490063/250000000 : ℝ)) (y := (184324543/200000000 : ℝ)) (X := (13806131409/16000000000 : ℝ)) (Y := (214245279593/1562500000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1915582967/1000000000 : ℝ)) (τ := (184324543/200000000 : ℝ)) (σ := (248490063/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (785912476/830877401 : ℝ) ^ p + (820750127/830877401 : ℝ) ^ p := by
    exact cert_lt (x := (785912476/830877401 : ℝ)) (y := (820750127/830877401 : ℝ)) (X := (2580998313343/10000000000000 : ℝ)) (Y := (37095008919239/50000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184324543/200000000 : ℝ)) (n' := (830877401/1000000000 : ℝ)) (Ab := (196478119/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (927164929/1000000000 : ℝ) ^ p + (992928277/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927164929/1000000000 : ℝ)) (y := (992928277/1000000000 : ℝ)) (X := (15866389519871/100000000000000 : ℝ)) (Y := (84133627432673/100000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992928277/1000000000 : ℝ) ^ p + (927164929/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992928277/1000000000 : ℝ)) (y := (927164929/1000000000 : ℝ)) (X := (84133627432673/100000000000000 : ℝ)) (Y := (15866389519871/100000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (960046603/500000000 : ℝ)) (τ := (927164929/1000000000 : ℝ)) (σ := (992928277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (20838800/22037191 : ℝ) ^ p + (413642992/418706629 : ℝ) ^ p := by
    exact cert_lt (x := (20838800/22037191 : ℝ)) (y := (413642992/418706629 : ℝ)) (X := (6408964174061/25000000000000 : ℝ)) (Y := (37182072297289/50000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (927164929/1000000000 : ℝ)) (n' := (418706629/500000000 : ℝ)) (Ab := (989843/1250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (927396841/1000000000 : ℝ) ^ p + (992881277/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927396841/1000000000 : ℝ)) (y := (992881277/1000000000 : ℝ)) (X := (15963284269771/100000000000000 : ℝ)) (Y := (42018366686827/50000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992881277/1000000000 : ℝ) ^ p + (927396841/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992881277/1000000000 : ℝ)) (y := (927396841/1000000000 : ℝ)) (X := (42018366686827/50000000000000 : ℝ)) (Y := (15963284269771/100000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (960139059/500000000 : ℝ)) (τ := (927396841/1000000000 : ℝ)) (σ := (992881277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (792123071/837685913 : ℝ) ^ p + (827558639/837685913 : ℝ) ^ p := by
    exact cert_lt (x := (792123071/837685913 : ℝ)) (y := (827558639/837685913 : ℝ)) (X := (2562864349197/10000000000000 : ℝ)) (Y := (36314139649/48828125000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (927396841/1000000000 : ℝ)) (n' := (837685913/1000000000 : ℝ)) (Ab := (792123071/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (927406447/1000000000 : ℝ) ^ p + (992879323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927406447/1000000000 : ℝ)) (y := (992879323/1000000000 : ℝ)) (X := (3193461989867/20000000000000 : ℝ)) (Y := (656505526347/781250000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992879323/1000000000 : ℝ) ^ p + (927406447/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992879323/1000000000 : ℝ)) (y := (927406447/1000000000 : ℝ)) (X := (656505526347/781250000000 : ℝ)) (Y := (3193461989867/20000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (192028577/100000000 : ℝ)) (τ := (927406447/1000000000 : ℝ)) (σ := (992879323/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (792133369/837697205 : ℝ) ^ p + (827569931/837697205 : ℝ) ^ p := by
    exact cert_lt (x := (792133369/837697205 : ℝ)) (y := (827569931/837697205 : ℝ)) (X := (25628344346637/100000000000000 : ℝ)) (Y := (74371656657407/100000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (927406447/1000000000 : ℝ)) (n' := (167539441/200000000 : ℝ)) (Ab := (792133369/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231851711/250000000 : ℝ) ^ p + (496439621/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (231851711/250000000 : ℝ)) (y := (496439621/500000000 : ℝ)) (X := (15967476344921/100000000000000 : ℝ)) (Y := (84032540484853/100000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496439621/500000000 : ℝ) ^ p + (231851711/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496439621/500000000 : ℝ)) (y := (231851711/250000000 : ℝ)) (X := (84032540484853/100000000000000 : ℝ)) (Y := (15967476344921/100000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (960143043/500000000 : ℝ)) (τ := (231851711/250000000 : ℝ)) (σ := (496439621/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (792133795/837697672 : ℝ) ^ p + (413785199/418848836 : ℝ) ^ p := by
    exact cert_lt (x := (792133795/837697672 : ℝ)) (y := (413785199/418848836 : ℝ)) (X := (25628332060727/100000000000000 : ℝ)) (Y := (74371669008699/100000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231851711/250000000 : ℝ)) (n' := (104712209/125000000 : ℝ)) (Ab := (158426759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (927406861/1000000000 : ℝ) ^ p + (992879239/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (927406861/1000000000 : ℝ)) (y := (992879239/1000000000 : ℝ)) (X := (1596748347021/10000000000000 : ℝ)) (Y := (42016267151919/50000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992879239/1000000000 : ℝ) ^ p + (927406861/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992879239/1000000000 : ℝ)) (y := (927406861/1000000000 : ℝ)) (X := (42016267151919/50000000000000 : ℝ)) (Y := (1596748347021/10000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (19202861/10000000 : ℝ)) (τ := (927406861/1000000000 : ℝ)) (σ := (992879239/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (792133813/837697692 : ℝ) ^ p + (137928403/139616282 : ℝ) ^ p := by
    exact cert_lt (x := (792133813/837697692 : ℝ)) (y := (137928403/139616282 : ℝ)) (X := (25628331342301/100000000000000 : ℝ)) (Y := (37185834768831/50000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (927406861/1000000000 : ℝ)) (n' := (209424423/250000000 : ℝ)) (Ab := (792133813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (19202861/10000000 : ℝ)) (τ := (927406861/1000000000 : ℝ)) (σ := (992879239/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (927406861/1000000000 : ℝ)) (n' := (209424423/250000000 : ℝ)) (Ab := (792133813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (19202861/10000000 : ℝ)) (τ := (927406861/1000000000 : ℝ)) (σ := (992879239/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (927406861/1000000000 : ℝ)) (n' := (209424423/250000000 : ℝ)) (Ab := (792133813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (19202861/10000000 : ℝ)) (τ := (927406861/1000000000 : ℝ)) (σ := (992879239/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (927406861/1000000000 : ℝ)) (n' := (209424423/250000000 : ℝ)) (Ab := (792133813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (19202861/10000000 : ℝ)) (τ := (927406861/1000000000 : ℝ)) (σ := (992879239/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (927406861/1000000000 : ℝ)) (n' := (209424423/250000000 : ℝ)) (Ab := (792133813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (19202861/10000000 : ℝ)) (τ := (927406861/1000000000 : ℝ)) (σ := (992879239/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1659966379/1806279587 : ℝ) ^ p + (1796152313/1806279587 : ℝ) ^ p := by
    exact cert_lt (x := (1659966379/1806279587 : ℝ)) (y := (1796152313/1806279587 : ℝ)) (X := (2558367468289/20000000000000 : ℝ)) (Y := (8720816293381/10000000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1114348092/1193720413 : ℝ) ^ p + (1183593139/1193720413 : ℝ) ^ p := by
    exact cert_lt (x := (1114348092/1193720413 : ℝ)) (y := (1183593139/1193720413 : ℝ)) (X := (9365613536211/50000000000000 : ℝ)) (Y := (10158596710173/12500000000000 : ℝ)) 779 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992879239/1000000000 : ℝ)) (U := (1193720413/1000000000 : ℝ)) (Ab := (1659966379/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (927406861/1000000000 : ℝ)) (σ := (992879239/1000000000 : ℝ)) (Ab := (278587023/250000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab106
