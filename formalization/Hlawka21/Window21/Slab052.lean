import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 52, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab052 (p : ℝ) (hpa : (181/8 : ℝ) ≤ p) (hpb : p ≤ (725/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (527362984517/24706500000000 : ℝ) (1375573/125000000 : ℝ) (1000000148239/4941300000000 : ℝ) (3033/2500 : ℝ) (969869181/500000000 : ℝ) (969828197/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193035119/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5543/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(4519/10000 : ℝ)
      else (767/1000 : ℝ) ≤ X j i ∧ X j i ≤ (11841/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (527362984517/24706500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1375573/125000000 : ℝ) := by norm_num
  have pc0 : 1 < (457733309/500000000 : ℝ) ^ p + (993609387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (457733309/500000000 : ℝ)) (y := (993609387/1000000000 : ℝ)) (X := (844973703961/6250000000000 : ℝ)) (Y := (86480438148751/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993609387/1000000000 : ℝ) ^ p + (457733309/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993609387/1000000000 : ℝ)) (y := (457733309/500000000 : ℝ)) (X := (86480438148751/100000000000000 : ℝ)) (Y := (844973703961/6250000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381815201/200000000 : ℝ)) (τ := (457733309/500000000 : ℝ)) (σ := (993609387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (388905212/412570613 : ℝ) ^ p + (407068321/412570613 : ℝ) ^ p := by
    exact cert_lt (x := (388905212/412570613 : ℝ)) (y := (407068321/412570613 : ℝ)) (X := (26227966796301/100000000000000 : ℝ)) (Y := (73772034032797/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457733309/500000000 : ℝ)) (n' := (412570613/500000000 : ℝ)) (Ab := (97226303/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921240323/1000000000 : ℝ) ^ p + (992547637/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921240323/1000000000 : ℝ)) (y := (992547637/1000000000 : ℝ)) (X := (1558922041323/10000000000000 : ℝ)) (Y := (21102698940919/25000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992547637/1000000000 : ℝ) ^ p + (921240323/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992547637/1000000000 : ℝ)) (y := (921240323/1000000000 : ℝ)) (X := (21102698940919/25000000000000 : ℝ)) (Y := (1558922041323/10000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (47844699/25000000 : ℝ)) (τ := (921240323/1000000000 : ℝ)) (σ := (992547637/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (784038753/832010948 : ℝ) ^ p + (205251591/208002737 : ℝ) ^ p := by
    exact cert_lt (x := (784038753/832010948 : ℝ)) (y := (205251591/208002737 : ℝ)) (X := (26041204172357/100000000000000 : ℝ)) (Y := (73958797169251/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921240323/1000000000 : ℝ)) (n' := (208002737/250000000 : ℝ)) (Ab := (784038753/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (921507217/1000000000 : ℝ) ^ p + (992494333/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921507217/1000000000 : ℝ)) (y := (992494333/1000000000 : ℝ)) (X := (490370819831/3125000000000 : ℝ)) (Y := (4215407489319/5000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992494333/1000000000 : ℝ) ^ p + (921507217/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992494333/1000000000 : ℝ)) (y := (921507217/1000000000 : ℝ)) (X := (4215407489319/5000000000000 : ℝ)) (Y := (490370819831/3125000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (38280031/20000000 : ℝ)) (τ := (921507217/1000000000 : ℝ)) (σ := (992494333/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (784325683/832327487 : ℝ) ^ p + (821322903/832327487 : ℝ) ^ p := by
    exact cert_lt (x := (784325683/832327487 : ℝ)) (y := (821322903/832327487 : ℝ)) (X := (26032661802933/100000000000000 : ℝ)) (Y := (73967339215817/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (921507217/1000000000 : ℝ)) (n' := (832327487/1000000000 : ℝ)) (Ab := (784325683/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921519419/1000000000 : ℝ) ^ p + (992491887/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921519419/1000000000 : ℝ)) (y := (992491887/1000000000 : ℝ)) (X := (7848287229613/50000000000000 : ℝ)) (Y := (84303442458881/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992491887/1000000000 : ℝ) ^ p + (921519419/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992491887/1000000000 : ℝ)) (y := (921519419/1000000000 : ℝ)) (X := (84303442458881/100000000000000 : ℝ)) (Y := (7848287229613/50000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (957005653/500000000 : ℝ)) (τ := (921519419/1000000000 : ℝ)) (σ := (992491887/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784338799/832341956 : ℝ) ^ p + (205334343/208085489 : ℝ) ^ p := by
    exact cert_lt (x := (784338799/832341956 : ℝ)) (y := (205334343/208085489 : ℝ)) (X := (26032271871987/100000000000000 : ℝ)) (Y := (36983864770039/50000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921519419/1000000000 : ℝ)) (n' := (208085489/250000000 : ℝ)) (Ab := (784338799/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (921519977/1000000000 : ℝ) ^ p + (39699671/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (921519977/1000000000 : ℝ)) (y := (39699671/40000000 : ℝ)) (X := (15696789799603/100000000000000 : ℝ)) (Y := (84303226920873/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39699671/40000000 : ℝ) ^ p + (921519977/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39699671/40000000 : ℝ)) (y := (921519977/1000000000 : ℝ)) (X := (84303226920873/100000000000000 : ℝ)) (Y := (15696789799603/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (239251469/125000000 : ℝ)) (τ := (921519977/1000000000 : ℝ)) (σ := (39699671/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784339399/832342618 : ℝ) ^ p + (410669017/416171309 : ℝ) ^ p := by
    exact cert_lt (x := (784339399/832342618 : ℝ)) (y := (410669017/416171309 : ℝ)) (X := (6508063489899/25000000000000 : ℝ)) (Y := (36983873699151/50000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (921519977/1000000000 : ℝ)) (n' := (416171309/500000000 : ℝ)) (Ab := (784339399/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (460760001/500000000 : ℝ) ^ p + (99249177/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (460760001/500000000 : ℝ)) (y := (99249177/100000000 : ℝ)) (X := (3139359889507/20000000000000 : ℝ)) (Y := (84303217298653/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (99249177/100000000 : ℝ) ^ p + (460760001/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99249177/100000000 : ℝ)) (y := (460760001/500000000 : ℝ)) (X := (84303217298653/100000000000000 : ℝ)) (Y := (3139359889507/20000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478502943/250000000 : ℝ)) (τ := (460760001/500000000 : ℝ)) (σ := (99249177/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (392169713/416171324 : ℝ) ^ p + (102667258/104042831 : ℝ) ^ p := by
    exact cert_lt (x := (392169713/416171324 : ℝ)) (y := (102667258/104042831 : ℝ)) (X := (13016126502367/50000000000000 : ℝ)) (Y := (73967748207587/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (460760001/500000000 : ℝ)) (n' := (104042831/125000000 : ℝ)) (Ab := (392169713/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (230380001/250000000 : ℝ) ^ p + (992491769/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230380001/250000000 : ℝ)) (y := (992491769/1000000000 : ℝ)) (X := (1569680021937/10000000000000 : ℝ)) (Y := (84303215374209/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992491769/1000000000 : ℝ) ^ p + (230380001/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992491769/1000000000 : ℝ)) (y := (230380001/250000000 : ℝ)) (X := (84303215374209/100000000000000 : ℝ)) (Y := (1569680021937/10000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (130723238/138723775 : ℝ) ^ p + (410669033/416171325 : ℝ) ^ p := by
    exact cert_lt (x := (130723238/138723775 : ℝ)) (y := (410669033/416171325 : ℝ)) (X := (26032253091469/100000000000000 : ℝ)) (Y := (73967748261539/100000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (n' := (16646853/20000000 : ℝ)) (Ab := (196084857/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914011773/1000000000 : ℝ)) (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (550311846/602321627 : ℝ) ^ p + (1795960297/1806964881 : ℝ) ^ p := by
    exact cert_lt (x := (550311846/602321627 : ℝ)) (y := (1795960297/1806964881 : ℝ)) (X := (2585002871503/20000000000000 : ℝ)) (Y := (21768746457181/25000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1108551560/1193035119 : ℝ) ^ p + (1182030535/1193035119 : ℝ) ^ p := by
    exact cert_lt (x := (1108551560/1193035119 : ℝ)) (y := (1182030535/1193035119 : ℝ)) (X := (18937650780571/100000000000000 : ℝ)) (Y := (20265587434503/25000000000000 : ℝ)) 725 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992491769/1000000000 : ℝ)) (U := (1193035119/1000000000 : ℝ)) (Ab := (825467769/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (230380001/250000000 : ℝ)) (σ := (992491769/1000000000 : ℝ)) (Ab := (27713789/25000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab052
