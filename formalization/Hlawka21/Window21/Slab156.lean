import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 156, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab156 (p : ℝ) (hpa : (207/8 : ℝ) ≤ p) (hpb : p ≤ (829/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (129697623989/7063875000000 : ℝ) (1885919/200000000 : ℝ) (1000000169533/5651100000000 : ℝ) (3033/2500 : ℝ) (243399697/125000000 : ℝ) (486783663/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194352731/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1399/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(2349/5000 : ℝ)
      else (7847/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11863/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (129697623989/7063875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1885919/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (926576003/1000000000 : ℝ) ^ p + (497126967/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (926576003/1000000000 : ℝ)) (y := (497126967/500000000 : ℝ)) (X := (13867946584587/100000000000000 : ℝ)) (Y := (21533018047857/25000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497126967/500000000 : ℝ) ^ p + (926576003/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497126967/500000000 : ℝ)) (y := (926576003/1000000000 : ℝ)) (X := (21533018047857/25000000000000 : ℝ)) (Y := (13867946584587/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1920829937/1000000000 : ℝ)) (τ := (926576003/1000000000 : ℝ)) (σ := (497126967/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (792458412/835408439 : ℝ) ^ p + (825978844/835408439 : ℝ) ^ p := by
    exact cert_lt (x := (792458412/835408439 : ℝ)) (y := (825978844/835408439 : ℝ)) (X := (25478105966233/100000000000000 : ℝ)) (Y := (74521895068961/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (926576003/1000000000 : ℝ)) (n' := (835408439/1000000000 : ℝ)) (Ab := (198114603/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931904803/1000000000 : ℝ) ^ p + (248312937/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (931904803/1000000000 : ℝ)) (y := (248312937/250000000 : ℝ)) (X := (16089098819971/100000000000000 : ℝ)) (Y := (83910918682329/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248312937/250000000 : ℝ) ^ p + (931904803/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248312937/250000000 : ℝ)) (y := (931904803/1000000000 : ℝ)) (X := (83910918682329/100000000000000 : ℝ)) (Y := (16089098819971/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1925156551/1000000000 : ℝ)) (τ := (931904803/1000000000 : ℝ)) (σ := (248312937/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (266059523/280549277 : ℝ) ^ p + (832218236/841647831 : ℝ) ^ p := by
    exact cert_lt (x := (266059523/280549277 : ℝ)) (y := (832218236/841647831 : ℝ)) (X := (6328635972421/25000000000000 : ℝ)) (Y := (14937091398429/20000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931904803/1000000000 : ℝ)) (n' := (841647831/1000000000 : ℝ)) (Ab := (798178569/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (466054877/500000000 : ℝ) ^ p + (993209727/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (466054877/500000000 : ℝ)) (y := (993209727/1000000000 : ℝ)) (X := (1011313605333/6250000000000 : ℝ)) (Y := (41909500265293/50000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993209727/1000000000 : ℝ) ^ p + (466054877/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993209727/1000000000 : ℝ)) (y := (466054877/500000000 : ℝ)) (X := (41909500265293/50000000000000 : ℝ)) (Y := (1011313605333/6250000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1925319481/1000000000 : ℝ)) (τ := (466054877/500000000 : ℝ)) (σ := (993209727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (798397897/841887103 : ℝ) ^ p + (832457508/841887103 : ℝ) ^ p := by
    exact cert_lt (x := (798397897/841887103 : ℝ)) (y := (832457508/841887103 : ℝ)) (X := (25308313433399/100000000000000 : ℝ)) (Y := (9336460988429/12500000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (466054877/500000000 : ℝ)) (n' := (841887103/1000000000 : ℝ)) (Ab := (798397897/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (23302939/25000000 : ℝ) ^ p + (993208121/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (23302939/25000000 : ℝ)) (y := (993208121/1000000000 : ℝ)) (X := (16184528574917/100000000000000 : ℝ)) (Y := (83815489433311/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993208121/1000000000 : ℝ) ^ p + (23302939/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (993208121/1000000000 : ℝ)) (y := (23302939/25000000 : ℝ)) (X := (83815489433311/100000000000000 : ℝ)) (Y := (16184528574917/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1925325681/1000000000 : ℝ)) (τ := (23302939/25000000 : ℝ)) (σ := (993208121/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (798406249/841896215 : ℝ) ^ p + (166493324/168379243 : ℝ) ^ p := by
    exact cert_lt (x := (798406249/841896215 : ℝ)) (y := (166493324/168379243 : ℝ)) (X := (25308075861643/100000000000000 : ℝ)) (Y := (37345962567077/50000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (23302939/25000000 : ℝ)) (n' := (168379243/200000000 : ℝ)) (Ab := (798406249/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (932117857/1000000000 : ℝ) ^ p + (49660403/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (932117857/1000000000 : ℝ)) (y := (49660403/50000000 : ℝ)) (X := (16184662170497/100000000000000 : ℝ)) (Y := (2619229877363/3125000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (49660403/50000000 : ℝ) ^ p + (932117857/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49660403/50000000 : ℝ)) (y := (932117857/1000000000 : ℝ)) (X := (2619229877363/3125000000000 : ℝ)) (Y := (16184662170497/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1925325917/1000000000 : ℝ)) (τ := (932117857/1000000000 : ℝ)) (σ := (49660403/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (798406567/841896562 : ℝ) ^ p + (832466967/841896562 : ℝ) ^ p := by
    exact cert_lt (x := (798406567/841896562 : ℝ)) (y := (832466967/841896562 : ℝ)) (X := (25308066767079/100000000000000 : ℝ)) (Y := (18672983542013/25000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (932117857/1000000000 : ℝ)) (n' := (420948281/500000000 : ℝ)) (Ab := (798406567/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (233029467/250000000 : ℝ) ^ p + (496604029/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (233029467/250000000 : ℝ)) (y := (496604029/500000000 : ℝ)) (X := (8092333559251/50000000000000 : ℝ)) (Y := (20953837925809/25000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496604029/500000000 : ℝ) ^ p + (233029467/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496604029/500000000 : ℝ)) (y := (233029467/250000000 : ℝ)) (X := (20953837925809/25000000000000 : ℝ)) (Y := (8092333559251/50000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962662963/500000000 : ℝ)) (τ := (233029467/250000000 : ℝ)) (σ := (496604029/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (798406579/841896575 : ℝ) ^ p + (166493396/168379315 : ℝ) ^ p := by
    exact cert_lt (x := (798406579/841896575 : ℝ)) (y := (166493396/168379315 : ℝ)) (X := (6327016624339/25000000000000 : ℝ)) (Y := (37345967253249/50000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (233029467/250000000 : ℝ)) (n' := (33675863/40000000 : ℝ)) (Ab := (798406579/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (93211787/100000000 : ℝ) ^ p + (993208057/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (93211787/100000000 : ℝ)) (y := (993208057/1000000000 : ℝ)) (X := (16184668018139/100000000000000 : ℝ)) (Y := (41907674758523/50000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993208057/1000000000 : ℝ) ^ p + (93211787/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (993208057/1000000000 : ℝ)) (y := (93211787/100000000 : ℝ)) (X := (41907674758523/50000000000000 : ℝ)) (Y := (16184668018139/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1925325927/1000000000 : ℝ)) (τ := (93211787/100000000 : ℝ)) (σ := (993208057/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (798406581/841896577 : ℝ) ^ p + (832466982/841896577 : ℝ) ^ p := by
    exact cert_lt (x := (798406581/841896577 : ℝ)) (y := (832466982/841896577 : ℝ)) (X := (6327016645549/25000000000000 : ℝ)) (Y := (37345967279283/50000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (93211787/100000000 : ℝ)) (n' := (841896577/1000000000 : ℝ)) (Ab := (798406581/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1925325927/1000000000 : ℝ)) (τ := (93211787/100000000 : ℝ)) (σ := (993208057/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (93211787/100000000 : ℝ)) (n' := (841896577/1000000000 : ℝ)) (Ab := (798406581/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1925325927/1000000000 : ℝ)) (τ := (93211787/100000000 : ℝ)) (σ := (993208057/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (93211787/100000000 : ℝ)) (n' := (841896577/1000000000 : ℝ)) (Ab := (798406581/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1925325927/1000000000 : ℝ)) (τ := (93211787/100000000 : ℝ)) (σ := (993208057/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (93211787/100000000 : ℝ)) (n' := (841896577/1000000000 : ℝ)) (Ab := (798406581/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1925325927/1000000000 : ℝ)) (τ := (93211787/100000000 : ℝ)) (σ := (993208057/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1667319569/1805647269 : ℝ) ^ p + (1796217674/1805647269 : ℝ) ^ p := by
    exact cert_lt (x := (1667319569/1805647269 : ℝ)) (y := (1796217674/1805647269 : ℝ)) (X := (1268467377761/10000000000000 : ℝ)) (Y := (43657663246309/50000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1119185984/1194352731 : ℝ) ^ p + (1184923136/1194352731 : ℝ) ^ p := by
    exact cert_lt (x := (1119185984/1194352731 : ℝ)) (y := (1184923136/1194352731 : ℝ)) (X := (9281702585213/50000000000000 : ℝ)) (Y := (81436595352139/100000000000000 : ℝ)) 829 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993208057/1000000000 : ℝ)) (U := (1194352731/1000000000 : ℝ)) (Ab := (1667319569/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (93211787/100000000 : ℝ)) (σ := (993208057/1000000000 : ℝ)) (Ab := (17487281/15625000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab156
