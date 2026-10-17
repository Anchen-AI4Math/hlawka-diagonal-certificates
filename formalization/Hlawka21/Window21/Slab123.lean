import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 123, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab123 (p : ℝ) (hpa : (795/32 : ℝ) ≤ p) (hpb : p ≤ (199/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (417015934339/21703500000000 : ℝ) (617433/62500000 : ℝ) (800000130221/4340700000000 : ℝ) (3033/2500 : ℝ) (972519441/500000000 : ℝ) (972485353/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149242049/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11161/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4647/10000 : ℝ)
      else (1949/2500 : ℝ) ≤ X j i ∧ X j i ≤ (741/625 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (417015934339/21703500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (617433/62500000 : ℝ) := by norm_num
  have pc0 : 1 < (461689951/500000000 : ℝ) ^ p + (49703163/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (461689951/500000000 : ℝ)) (y := (49703163/50000000 : ℝ)) (X := (13766954839659/100000000000000 : ℝ)) (Y := (43116532015201/50000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (49703163/50000000 : ℝ) ^ p + (461689951/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (49703163/50000000 : ℝ)) (y := (461689951/500000000 : ℝ)) (X := (43116532015201/50000000000000 : ℝ)) (Y := (13766954839659/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (958721581/500000000 : ℝ)) (τ := (461689951/500000000 : ℝ)) (σ := (49703163/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (788231822/832493429 : ℝ) ^ p + (822614501/832493429 : ℝ) ^ p := by
    exact cert_lt (x := (788231822/832493429 : ℝ)) (y := (822614501/832493429 : ℝ)) (X := (25691803932231/100000000000000 : ℝ)) (Y := (37154098574357/50000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (461689951/500000000 : ℝ)) (n' := (832493429/1000000000 : ℝ)) (Ab := (394115911/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (928849111/1000000000 : ℝ) ^ p + (496520631/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (928849111/1000000000 : ℝ)) (y := (496520631/500000000 : ℝ)) (X := (15945424959679/100000000000000 : ℝ)) (Y := (84054592259857/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496520631/500000000 : ℝ) ^ p + (928849111/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496520631/500000000 : ℝ)) (y := (928849111/1000000000 : ℝ)) (X := (84054592259857/100000000000000 : ℝ)) (Y := (15945424959679/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1921890373/1000000000 : ℝ)) (τ := (928849111/1000000000 : ℝ)) (σ := (496520631/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (794110699/838926842 : ℝ) ^ p + (414523957/419463421 : ℝ) ^ p := by
    exact cert_lt (x := (794110699/838926842 : ℝ)) (y := (414523957/419463421 : ℝ)) (X := (5104277818001/20000000000000 : ℝ)) (Y := (14895722454861/20000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (928849111/1000000000 : ℝ)) (n' := (419463421/500000000 : ℝ)) (Ab := (794110699/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (929071327/1000000000 : ℝ) ^ p + (24824901/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (929071327/1000000000 : ℝ)) (y := (24824901/25000000 : ℝ)) (X := (16040588400849/100000000000000 : ℝ)) (Y := (5247464290281/6250000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (24824901/25000000 : ℝ) ^ p + (929071327/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24824901/25000000 : ℝ)) (y := (929071327/1000000000 : ℝ)) (X := (5247464290281/6250000000000 : ℝ)) (Y := (16040588400849/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1922067367/1000000000 : ℝ)) (τ := (929071327/1000000000 : ℝ)) (σ := (24824901/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (264782934/279729149 : ℝ) ^ p + (276436173/279729149 : ℝ) ^ p := by
    exact cert_lt (x := (264782934/279729149 : ℝ)) (y := (276436173/279729149 : ℝ)) (X := (25514532683773/100000000000000 : ℝ)) (Y := (18621367056719/25000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (929071327/1000000000 : ℝ)) (n' := (839187447/1000000000 : ℝ)) (Ab := (397174401/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (185816053/200000000 : ℝ) ^ p + (198598843/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (185816053/200000000 : ℝ)) (y := (198598843/200000000 : ℝ)) (X := (3208885491559/20000000000000 : ℝ)) (Y := (20988897587291/25000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198598843/200000000 : ℝ) ^ p + (185816053/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (198598843/200000000 : ℝ)) (y := (185816053/200000000 : ℝ)) (X := (20988897587291/25000000000000 : ℝ)) (Y := (3208885491559/20000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (24025931/12500000 : ℝ)) (τ := (185816053/200000000 : ℝ)) (σ := (198598843/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (397179189/419598964 : ℝ) ^ p + (103664875/104899741 : ℝ) ^ p := by
    exact cert_lt (x := (397179189/419598964 : ℝ)) (y := (103664875/104899741 : ℝ)) (X := (6378564261683/25000000000000 : ℝ)) (Y := (3724287194143/5000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (185816053/200000000 : ℝ)) (n' := (104899741/125000000 : ℝ)) (Ab := (397179189/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (1486529/1600000 : ℝ) ^ p + (992994141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (1486529/1600000 : ℝ)) (y := (992994141/1000000000 : ℝ)) (X := (8022291051879/50000000000000 : ℝ)) (Y := (2623607334929/3125000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992994141/1000000000 : ℝ) ^ p + (1486529/1600000 : ℝ) ^ p := by
    exact cert_lt (x := (992994141/1000000000 : ℝ)) (y := (1486529/1600000 : ℝ)) (X := (2623607334929/3125000000000 : ℝ)) (Y := (8022291051879/50000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961037383/500000000 : ℝ)) (τ := (1486529/1600000 : ℝ)) (σ := (992994141/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (397179382/419599175 : ℝ) ^ p + (414659711/419599175 : ℝ) ^ p := by
    exact cert_lt (x := (397179382/419599175 : ℝ)) (y := (414659711/419599175 : ℝ)) (X := (25514246299071/100000000000000 : ℝ)) (Y := (14897150996313/20000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (1486529/1600000 : ℝ)) (n' := (16783967/20000000 : ℝ)) (Ab := (198589691/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (464540319/500000000 : ℝ) ^ p + (992994139/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (464540319/500000000 : ℝ)) (y := (992994139/1000000000 : ℝ)) (X := (16044587688223/100000000000000 : ℝ)) (Y := (83955430511477/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992994139/1000000000 : ℝ) ^ p + (464540319/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992994139/1000000000 : ℝ)) (y := (464540319/500000000 : ℝ)) (X := (83955430511477/100000000000000 : ℝ)) (Y := (16044587688223/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1922074777/1000000000 : ℝ)) (τ := (464540319/500000000 : ℝ)) (σ := (992994139/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (794358778/839198365 : ℝ) ^ p + (829319437/839198365 : ℝ) ^ p := by
    exact cert_lt (x := (794358778/839198365 : ℝ)) (y := (829319437/839198365 : ℝ)) (X := (25514246140453/100000000000000 : ℝ)) (Y := (74485755376069/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (464540319/500000000 : ℝ)) (n' := (167839673/200000000 : ℝ)) (Ab := (397179389/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (2903377/3125000 : ℝ) ^ p + (496497069/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (2903377/3125000 : ℝ)) (y := (496497069/500000000 : ℝ)) (X := (16044588547371/100000000000000 : ℝ)) (Y := (83955428408351/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496497069/500000000 : ℝ) ^ p + (2903377/3125000 : ℝ) ^ p := by
    exact cert_lt (x := (496497069/500000000 : ℝ)) (y := (2903377/3125000 : ℝ)) (X := (83955428408351/100000000000000 : ℝ)) (Y := (16044588547371/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (961037389/500000000 : ℝ)) (τ := (2903377/3125000 : ℝ)) (σ := (496497069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (198589695/209799592 : ℝ) ^ p + (51832465/52449898 : ℝ) ^ p := by
    exact cert_lt (x := (198589695/209799592 : ℝ)) (y := (51832465/52449898 : ℝ)) (X := (6378561367389/25000000000000 : ℝ)) (Y := (74485755454969/100000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (2903377/3125000 : ℝ)) (n' := (26224949/31250000 : ℝ)) (Ab := (39717939/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (961037389/500000000 : ℝ)) (τ := (2903377/3125000 : ℝ)) (σ := (496497069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (2903377/3125000 : ℝ)) (n' := (26224949/31250000 : ℝ)) (Ab := (39717939/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (961037389/500000000 : ℝ)) (τ := (2903377/3125000 : ℝ)) (σ := (496497069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (2903377/3125000 : ℝ)) (n' := (26224949/31250000 : ℝ)) (Ab := (39717939/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (961037389/500000000 : ℝ)) (τ := (2903377/3125000 : ℝ)) (σ := (496497069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (2903377/3125000 : ℝ)) (n' := (26224949/31250000 : ℝ)) (Ab := (39717939/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (961037389/500000000 : ℝ)) (τ := (2903377/3125000 : ℝ)) (σ := (496497069/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (415641491/451515902 : ℝ) ^ p + (224523085/225757951 : ℝ) ^ p := by
    exact cert_lt (x := (415641491/451515902 : ℝ)) (y := (224523085/225757951 : ℝ)) (X := (6376911145001/50000000000000 : ℝ)) (Y := (17449235599727/20000000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (558023143/596968196 : ℝ) ^ p + (148007183/149242049 : ℝ) ^ p := by
    exact cert_lt (x := (558023143/596968196 : ℝ)) (y := (148007183/149242049 : ℝ)) (X := (746874751697/4000000000000 : ℝ)) (Y := (2033203299731/2500000000000 : ℝ)) 199 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496497069/500000000 : ℝ)) (U := (149242049/125000000 : ℝ)) (Ab := (415641491/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (2903377/3125000 : ℝ)) (σ := (496497069/500000000 : ℝ)) (Ab := (558023143/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab123
