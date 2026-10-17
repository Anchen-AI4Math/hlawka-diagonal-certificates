import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 29, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab029 (p : ℝ) (hpa : (701/32 : ℝ) ≤ p) (hpb : p ≤ (351/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1059197161123/47843250000000 : ℝ) (2856327/250000000 : ℝ) (4000000574119/19137300000000 : ℝ) (3033/2500 : ℝ) (387559/200000 : ℝ) (242213457/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298186989/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11059/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4471/10000 : ℝ)
      else (3811/5000 : ℝ) ≤ X j i ∧ X j i ≤ (2959/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1059197161123/47843250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2856327/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (912541973/1000000000 : ℝ) ^ p + (496724027/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (912541973/1000000000 : ℝ)) (y := (496724027/500000000 : ℝ)) (X := (13429099161907/100000000000000 : ℝ)) (Y := (43285458911619/50000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496724027/500000000 : ℝ) ^ p + (912541973/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496724027/500000000 : ℝ)) (y := (912541973/1000000000 : ℝ)) (X := (43285458911619/50000000000000 : ℝ)) (Y := (13429099161907/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1905990027/1000000000 : ℝ)) (τ := (912541973/1000000000 : ℝ)) (σ := (496724027/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (773973527/822375554 : ℝ) ^ p + (405475123/411187777 : ℝ) ^ p := by
    exact cert_lt (x := (773973527/822375554 : ℝ)) (y := (405475123/411187777 : ℝ)) (X := (13214374948011/50000000000000 : ℝ)) (Y := (36785625678813/50000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (912541973/1000000000 : ℝ)) (n' := (411187777/500000000 : ℝ)) (Ab := (773973527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (918411973/1000000000 : ℝ) ^ p + (31011719/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (918411973/1000000000 : ℝ)) (y := (31011719/31250000 : ℝ)) (X := (7728691433379/50000000000000 : ℝ)) (Y := (10567829074649/12500000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (31011719/31250000 : ℝ) ^ p + (918411973/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31011719/31250000 : ℝ)) (y := (918411973/1000000000 : ℝ)) (X := (10567829074649/12500000000000 : ℝ)) (Y := (7728691433379/50000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1910786981/1000000000 : ℝ)) (τ := (918411973/1000000000 : ℝ)) (σ := (31011719/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (195078628/207347369 : ℝ) ^ p + (204491042/207347369 : ℝ) ^ p := by
    exact cert_lt (x := (195078628/207347369 : ℝ)) (y := (204491042/207347369 : ℝ)) (X := (13118106518677/50000000000000 : ℝ)) (Y := (73763787905817/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (918411973/1000000000 : ℝ)) (n' := (207347369/250000000 : ℝ)) (Ab := (48769657/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (57418497/62500000 : ℝ) ^ p + (99231869/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (57418497/62500000 : ℝ)) (y := (99231869/100000000 : ℝ)) (X := (7781286888589/50000000000000 : ℝ)) (Y := (84437442148283/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99231869/100000000 : ℝ) ^ p + (57418497/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (99231869/100000000 : ℝ)) (y := (57418497/62500000 : ℝ)) (X := (84437442148283/100000000000000 : ℝ)) (Y := (7781286888589/50000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (955507321/500000000 : ℝ)) (τ := (57418497/62500000 : ℝ)) (σ := (99231869/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (390310105/414863842 : ℝ) ^ p + (204575594/207431921 : ℝ) ^ p := by
    exact cert_lt (x := (390310105/414863842 : ℝ)) (y := (204575594/207431921 : ℝ)) (X := (26226999688559/100000000000000 : ℝ)) (Y := (73773001692707/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (57418497/62500000 : ℝ)) (n' := (207431921/250000000 : ℝ)) (Ab := (78062021/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (918709537/1000000000 : ℝ) ^ p + (198463197/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (918709537/1000000000 : ℝ)) (y := (198463197/200000000 : ℝ)) (X := (311352459789/2000000000000 : ℝ)) (Y := (21108098227381/25000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198463197/200000000 : ℝ) ^ p + (918709537/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198463197/200000000 : ℝ)) (y := (918709537/1000000000 : ℝ)) (X := (21108098227381/25000000000000 : ℝ)) (Y := (311352459789/2000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (955512761/500000000 : ℝ)) (τ := (918709537/1000000000 : ℝ)) (σ := (198463197/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (780634831/829743861 : ℝ) ^ p + (272772851/276581287 : ℝ) ^ p := by
    exact cert_lt (x := (780634831/829743861 : ℝ)) (y := (272772851/276581287 : ℝ)) (X := (26226558530519/100000000000000 : ℝ)) (Y := (1475468844827/2000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (918709537/1000000000 : ℝ)) (n' := (829743861/1000000000 : ℝ)) (Ab := (780634831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (459355093/500000000 : ℝ) ^ p + (62019741/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (459355093/500000000 : ℝ)) (y := (62019741/62500000 : ℝ)) (X := (3113572849201/20000000000000 : ℝ)) (Y := (84432152121233/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62019741/62500000 : ℝ) ^ p + (459355093/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (62019741/62500000 : ℝ)) (y := (459355093/500000000 : ℝ)) (X := (84432152121233/100000000000000 : ℝ)) (Y := (3113572849201/20000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (955513021/500000000 : ℝ)) (τ := (459355093/500000000 : ℝ)) (σ := (62019741/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (390317765/414872317 : ℝ) ^ p + (409159663/414872317 : ℝ) ^ p := by
    exact cert_lt (x := (390317765/414872317 : ℝ)) (y := (409159663/414872317 : ℝ)) (X := (5245307542023/20000000000000 : ℝ)) (Y := (73773463292111/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (459355093/500000000 : ℝ)) (n' := (414872317/500000000 : ℝ)) (Ab := (78063553/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (459355109/500000000 : ℝ) ^ p + (992315849/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459355109/500000000 : ℝ)) (y := (992315849/1000000000 : ℝ)) (X := (3891969035411/25000000000000 : ℝ)) (Y := (84432139055221/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992315849/1000000000 : ℝ) ^ p + (459355109/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992315849/1000000000 : ℝ)) (y := (459355109/500000000 : ℝ)) (X := (84432139055221/100000000000000 : ℝ)) (Y := (3891969035411/25000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1911026067/1000000000 : ℝ)) (τ := (459355109/500000000 : ℝ)) (σ := (992315849/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (195158891/207436168 : ℝ) ^ p + (204579841/207436168 : ℝ) ^ p := by
    exact cert_lt (x := (195158891/207436168 : ℝ)) (y := (204579841/207436168 : ℝ)) (X := (6556634104909/25000000000000 : ℝ)) (Y := (73773464326947/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (459355109/500000000 : ℝ)) (n' := (25929521/31250000 : ℝ)) (Ab := (195158891/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (918710219/1000000000 : ℝ) ^ p + (992315849/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (918710219/1000000000 : ℝ)) (y := (992315849/1000000000 : ℝ)) (X := (15567876513383/100000000000000 : ℝ)) (Y := (84432139055221/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992315849/1000000000 : ℝ) ^ p + (918710219/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992315849/1000000000 : ℝ)) (y := (918710219/1000000000 : ℝ)) (X := (84432139055221/100000000000000 : ℝ)) (Y := (15567876513383/100000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (477756517/250000000 : ℝ)) (τ := (918710219/1000000000 : ℝ)) (σ := (992315849/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (780635565/829744673 : ℝ) ^ p + (818319365/829744673 : ℝ) ^ p := by
    exact cert_lt (x := (780635565/829744673 : ℝ)) (y := (818319365/829744673 : ℝ)) (X := (26226536463257/100000000000000 : ℝ)) (Y := (3688673217709/5000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (918710219/1000000000 : ℝ)) (n' := (829744673/1000000000 : ℝ)) (Ab := (156127113/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (477756517/250000000 : ℝ)) (τ := (918710219/1000000000 : ℝ)) (σ := (992315849/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (918710219/1000000000 : ℝ)) (n' := (829744673/1000000000 : ℝ)) (Ab := (156127113/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (477756517/250000000 : ℝ)) (τ := (918710219/1000000000 : ℝ)) (σ := (992315849/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (918710219/1000000000 : ℝ)) (n' := (829744673/1000000000 : ℝ)) (Ab := (156127113/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (477756517/250000000 : ℝ)) (τ := (918710219/1000000000 : ℝ)) (σ := (992315849/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (918710219/1000000000 : ℝ)) (n' := (829744673/1000000000 : ℝ)) (Ab := (156127113/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (477756517/250000000 : ℝ)) (τ := (918710219/1000000000 : ℝ)) (σ := (992315849/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (823343071/903626022 : ℝ) ^ p + (149652228/150604337 : ℝ) ^ p := by
    exact cert_lt (x := (823343071/903626022 : ℝ)) (y := (149652228/150604337 : ℝ)) (X := (649414274171/5000000000000 : ℝ)) (Y := (43505857384817/50000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1105879141/1192747956 : ℝ) ^ p + (98443554/99395663 : ℝ) ^ p := by
    exact cert_lt (x := (1105879141/1192747956 : ℝ)) (y := (98443554/99395663 : ℝ)) (X := (9517442229117/50000000000000 : ℝ)) (Y := (1619302320563/2000000000000 : ℝ)) 351 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992315849/1000000000 : ℝ)) (U := (298186989/250000000 : ℝ)) (Ab := (823343071/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (918710219/1000000000 : ℝ)) (σ := (992315849/1000000000 : ℝ)) (Ab := (1105879141/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab029
