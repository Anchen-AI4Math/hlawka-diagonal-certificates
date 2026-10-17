import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 44, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab044 (p : ℝ) (hpa : (179/8 : ℝ) ≤ p) (hpb : p ≤ (717/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (264062218741/12216750000000 : ℝ) (5573711/500000000 : ℝ) (1000000146601/4886700000000 : ℝ) (3033/2500 : ℝ) (484769083/250000000 : ℝ) (242374069/250000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596467337/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11077/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4503/10000 : ℝ)
      else (3827/5000 : ℝ) ≤ X j i ∧ X j i ≤ (148/125 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (264062218741/12216750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5573711/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (914471713/1000000000 : ℝ) ^ p + (496777061/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (914471713/1000000000 : ℝ)) (y := (496777061/500000000 : ℝ)) (X := (1348874362029/10000000000000 : ℝ)) (Y := (86511273900009/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496777061/500000000 : ℝ) ^ p + (914471713/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496777061/500000000 : ℝ)) (y := (914471713/1000000000 : ℝ)) (X := (86511273900009/100000000000000 : ℝ)) (Y := (1348874362029/10000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381605167/200000000 : ℝ)) (τ := (914471713/1000000000 : ℝ)) (σ := (496777061/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (258834777/274734442 : ℝ) ^ p + (406527952/412101663 : ℝ) ^ p := by
    exact cert_lt (x := (258834777/274734442 : ℝ)) (y := (406527952/412101663 : ℝ)) (X := (26296104933881/100000000000000 : ℝ)) (Y := (14740779244649/20000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (914471713/1000000000 : ℝ)) (n' := (412101663/500000000 : ℝ)) (Ab := (776504331/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (460139593/500000000 : ℝ) ^ p + (496244161/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (460139593/500000000 : ℝ)) (y := (496244161/500000000 : ℝ)) (X := (15544384500443/100000000000000 : ℝ)) (Y := (21113907917619/25000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496244161/500000000 : ℝ) ^ p + (460139593/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496244161/500000000 : ℝ)) (y := (460139593/500000000 : ℝ)) (X := (21113907917619/25000000000000 : ℝ)) (Y := (15544384500443/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (478191877/250000000 : ℝ)) (τ := (460139593/500000000 : ℝ)) (σ := (496244161/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (782772013/831123180 : ℝ) ^ p + (409987879/415561590 : ℝ) ^ p := by
    exact cert_lt (x := (782772013/831123180 : ℝ)) (y := (409987879/415561590 : ℝ)) (X := (26107359702533/100000000000000 : ℝ)) (Y := (73892641415927/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (460139593/500000000 : ℝ)) (n' := (41556159/50000000 : ℝ)) (Ab := (782772013/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (460275931/500000000 : ℝ) ^ p + (992433993/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460275931/500000000 : ℝ)) (y := (992433993/1000000000 : ℝ)) (X := (7823955066663/50000000000000 : ℝ)) (Y := (4217605280729/5000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992433993/1000000000 : ℝ) ^ p + (460275931/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992433993/1000000000 : ℝ)) (y := (460275931/500000000 : ℝ)) (X := (4217605280729/5000000000000 : ℝ)) (Y := (7823955066663/50000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (382597171/200000000 : ℝ)) (τ := (460275931/500000000 : ℝ)) (σ := (992433993/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (783065289/831447035 : ℝ) ^ p + (820299613/831447035 : ℝ) ^ p := by
    exact cert_lt (x := (783065289/831447035 : ℝ)) (y := (820299613/831447035 : ℝ)) (X := (41757747679/160000000000 : ℝ)) (Y := (73901409090663/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (460275931/500000000 : ℝ)) (n' := (166289407/200000000 : ℝ)) (Ab := (783065289/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (36822581/40000000 : ℝ) ^ p + (49621573/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (36822581/40000000 : ℝ)) (y := (49621573/50000000 : ℝ)) (X := (15652733805777/100000000000000 : ℝ)) (Y := (42173640921137/50000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (49621573/50000000 : ℝ) ^ p + (36822581/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (49621573/50000000 : ℝ)) (y := (36822581/40000000 : ℝ)) (X := (42173640921137/50000000000000 : ℝ)) (Y := (15652733805777/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (382599197/200000000 : ℝ)) (τ := (36822581/40000000 : ℝ)) (σ := (49621573/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (130513151/138577012 : ℝ) ^ p + (410157325/415731036 : ℝ) ^ p := by
    exact cert_lt (x := (130513151/138577012 : ℝ)) (y := (410157325/415731036 : ℝ)) (X := (1043927412757/4000000000000 : ℝ)) (Y := (18475454010793/25000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (36822581/40000000 : ℝ)) (n' := (103932759/125000000 : ℝ)) (Ab := (391539453/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (115070639/125000000 : ℝ) ^ p + (992431343/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115070639/125000000 : ℝ)) (y := (992431343/1000000000 : ℝ)) (X := (1565295744409/10000000000000 : ℝ)) (Y := (10543382379651/12500000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992431343/1000000000 : ℝ) ^ p + (115070639/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992431343/1000000000 : ℝ)) (y := (115070639/125000000 : ℝ)) (X := (10543382379651/12500000000000 : ℝ)) (Y := (1565295744409/10000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (382599291/200000000 : ℝ)) (τ := (115070639/125000000 : ℝ)) (σ := (992431343/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (783079537/831462769 : ℝ) ^ p + (820315347/831462769 : ℝ) ^ p := by
    exact cert_lt (x := (783079537/831462769 : ℝ)) (y := (820315347/831462769 : ℝ)) (X := (26098166320753/100000000000000 : ℝ)) (Y := (14780366981213/20000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (115070639/125000000 : ℝ)) (n' := (831462769/1000000000 : ℝ)) (Ab := (783079537/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (46028257/50000000 : ℝ) ^ p + (992431337/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46028257/50000000 : ℝ)) (y := (992431337/1000000000 : ℝ)) (X := (1956621013969/12500000000000 : ℝ)) (Y := (84347047611323/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992431337/1000000000 : ℝ) ^ p + (46028257/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (992431337/1000000000 : ℝ)) (y := (46028257/50000000 : ℝ)) (X := (84347047611323/100000000000000 : ℝ)) (Y := (1956621013969/12500000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1912996477/1000000000 : ℝ)) (τ := (46028257/50000000 : ℝ)) (σ := (992431337/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (783079567/831462802 : ℝ) ^ p + (410157690/415731401 : ℝ) ^ p := by
    exact cert_lt (x := (783079567/831462802 : ℝ)) (y := (410157690/415731401 : ℝ)) (X := (26098165514481/100000000000000 : ℝ)) (Y := (36950917899571/50000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (46028257/50000000 : ℝ)) (n' := (415731401/500000000 : ℝ)) (Ab := (783079567/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (920565141/1000000000 : ℝ) ^ p + (992431337/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920565141/1000000000 : ℝ)) (y := (992431337/1000000000 : ℝ)) (X := (782648424637/5000000000000 : ℝ)) (Y := (84347047611323/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992431337/1000000000 : ℝ) ^ p + (920565141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992431337/1000000000 : ℝ)) (y := (920565141/1000000000 : ℝ)) (X := (84347047611323/100000000000000 : ℝ)) (Y := (782648424637/5000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (956498239/500000000 : ℝ)) (τ := (920565141/1000000000 : ℝ)) (σ := (992431337/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (783079568/831462803 : ℝ) ^ p + (820315381/831462803 : ℝ) ^ p := by
    exact cert_lt (x := (783079568/831462803 : ℝ)) (y := (820315381/831462803 : ℝ)) (X := (13049082778967/50000000000000 : ℝ)) (Y := (14780367165241/20000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (920565141/1000000000 : ℝ)) (n' := (831462803/1000000000 : ℝ)) (Ab := (48942473/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (956498239/500000000 : ℝ)) (τ := (920565141/1000000000 : ℝ)) (σ := (992431337/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (920565141/1000000000 : ℝ)) (n' := (831462803/1000000000 : ℝ)) (Ab := (48942473/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (956498239/500000000 : ℝ)) (τ := (920565141/1000000000 : ℝ)) (σ := (992431337/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (920565141/1000000000 : ℝ)) (n' := (831462803/1000000000 : ℝ)) (Ab := (48942473/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (956498239/500000000 : ℝ)) (τ := (920565141/1000000000 : ℝ)) (σ := (992431337/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (920565141/1000000000 : ℝ)) (n' := (831462803/1000000000 : ℝ)) (Ab := (48942473/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (956498239/500000000 : ℝ)) (τ := (920565141/1000000000 : ℝ)) (σ := (992431337/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (824743522/903532663 : ℝ) ^ p + (81632632/82139333 : ℝ) ^ p := by
    exact cert_lt (x := (824743522/903532663 : ℝ)) (y := (81632632/82139333 : ℝ)) (X := (1618317054127/12500000000000 : ℝ)) (Y := (87053463858749/100000000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1107636653/1192934674 : ℝ) ^ p + (590893626/596467337 : ℝ) ^ p := by
    exact cert_lt (x := (1107636653/1192934674 : ℝ)) (y := (590893626/596467337 : ℝ)) (X := (18970786519223/100000000000000 : ℝ)) (Y := (10128651780063/12500000000000 : ℝ)) 717 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992431337/1000000000 : ℝ)) (U := (596467337/500000000 : ℝ)) (Ab := (412371761/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (920565141/1000000000 : ℝ)) (σ := (992431337/1000000000 : ℝ)) (Ab := (1107636653/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab044
