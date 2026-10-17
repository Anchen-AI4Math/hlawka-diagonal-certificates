import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 19, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab019 (p : ℝ) (hpa : (435/16 : ℝ) ≤ p) (hpb : p ≤ (109/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (36180552577/2408812500000 : ℝ) (770397/100000000 : ℝ) (640000115623/3854100000000 : ℝ) (591/500 : ℝ) (974884191/500000000 : ℝ) (487413593/500000000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (23122463/20000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5413/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1377/2500 : ℝ)
      else (8163/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2869/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (36180552577/2408812500000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (770397/100000000 : ℝ) := by norm_num
  have pc0 : 1 < (936278083/1000000000 : ℝ) ^ p + (993349517/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (936278083/1000000000 : ℝ)) (y := (993349517/1000000000 : ℝ)) (X := (3325158533483/20000000000000 : ℝ)) (Y := (41687112962863/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993349517/1000000000 : ℝ) ^ p + (936278083/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993349517/1000000000 : ℝ)) (y := (936278083/1000000000 : ℝ)) (X := (41687112962863/50000000000000 : ℝ)) (Y := (3325158533483/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (4824069/2500000 : ℝ)) (τ := (936278083/1000000000 : ℝ)) (σ := (993349517/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (817353727/864572558 : ℝ) ^ p + (428434294/432286279 : ℝ) ^ p := by
    exact cert_lt (x := (817353727/864572558 : ℝ)) (y := (428434294/432286279 : ℝ)) (X := (1082192128577/5000000000000 : ℝ)) (Y := (78356158418043/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (936278083/1000000000 : ℝ)) (n' := (432286279/500000000 : ℝ)) (Ab := (817353727/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (939699391/1000000000 : ℝ) ^ p + (992582143/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939699391/1000000000 : ℝ)) (y := (992582143/1000000000 : ℝ)) (X := (18363216820113/100000000000000 : ℝ)) (Y := (81636800292541/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992582143/1000000000 : ℝ) ^ p + (939699391/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992582143/1000000000 : ℝ)) (y := (939699391/1000000000 : ℝ)) (X := (81636800292541/100000000000000 : ℝ)) (Y := (18363216820113/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (966140767/500000000 : ℝ)) (τ := (939699391/1000000000 : ℝ)) (σ := (992582143/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (820957133/868512700 : ℝ) ^ p + (86080873/86851270 : ℝ) ^ p := by
    exact cert_lt (x := (820957133/868512700 : ℝ)) (y := (86080873/86851270 : ℝ)) (X := (4311340942351/20000000000000 : ℝ)) (Y := (39221648272359/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (939699391/1000000000 : ℝ)) (n' := (8685127/10000000 : ℝ)) (Ab := (820957133/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (37592113/40000000 : ℝ) ^ p + (248139381/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (37592113/40000000 : ℝ)) (y := (248139381/250000000 : ℝ)) (X := (2302296990323/12500000000000 : ℝ)) (Y := (81581641460931/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248139381/250000000 : ℝ) ^ p + (37592113/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (248139381/250000000 : ℝ)) (y := (37592113/40000000 : ℝ)) (X := (81581641460931/100000000000000 : ℝ)) (Y := (2302296990323/12500000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1932360349/1000000000 : ℝ)) (τ := (37592113/40000000 : ℝ)) (σ := (248139381/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (45614770/48257311 : ℝ) ^ p + (143487938/144771933 : ℝ) ^ p := by
    exact cert_lt (x := (45614770/48257311 : ℝ)) (y := (143487938/144771933 : ℝ)) (X := (21554085866013/100000000000000 : ℝ)) (Y := (3137836607479/4000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (37592113/40000000 : ℝ)) (n' := (434315799/500000000 : ℝ)) (Ab := (41053293/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (939805933/1000000000 : ℝ) ^ p + (992556783/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (939805933/1000000000 : ℝ)) (y := (992556783/1000000000 : ℝ)) (X := (18420035818873/100000000000000 : ℝ)) (Y := (81579981808247/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992556783/1000000000 : ℝ) ^ p + (939805933/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992556783/1000000000 : ℝ)) (y := (939805933/1000000000 : ℝ)) (X := (81579981808247/100000000000000 : ℝ)) (Y := (18420035818873/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (483090679/250000000 : ℝ)) (τ := (939805933/1000000000 : ℝ)) (σ := (992556783/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (91229903/96515019 : ℝ) ^ p + (286977067/289545057 : ℝ) ^ p := by
    exact cert_lt (x := (91229903/96515019 : ℝ)) (y := (286977067/289545057 : ℝ)) (X := (4310801386297/20000000000000 : ℝ)) (Y := (39222996934959/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (939805933/1000000000 : ℝ)) (n' := (868635171/1000000000 : ℝ)) (Ab := (821069127/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (469903013/500000000 : ℝ) ^ p + (992556761/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (469903013/500000000 : ℝ)) (y := (992556761/1000000000 : ℝ)) (X := (3684017097961/20000000000000 : ℝ)) (Y := (16315986506861/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992556761/1000000000 : ℝ) ^ p + (469903013/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992556761/1000000000 : ℝ)) (y := (469903013/500000000 : ℝ)) (X := (16315986506861/20000000000000 : ℝ)) (Y := (3684017097961/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1932362787/1000000000 : ℝ)) (τ := (469903013/500000000 : ℝ)) (σ := (992556761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (821069225/868635278 : ℝ) ^ p + (430465654/434317639 : ℝ) ^ p := by
    exact cert_lt (x := (821069225/868635278 : ℝ)) (y := (430465654/434317639 : ℝ)) (X := (10777002342391/50000000000000 : ℝ)) (Y := (78445996226213/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (469903013/500000000 : ℝ)) (n' := (434317639/500000000 : ℝ)) (Ab := (32842769/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (939806029/1000000000 : ℝ) ^ p + (24813919/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (939806029/1000000000 : ℝ)) (y := (24813919/25000000 : ℝ)) (X := (3684017418419/20000000000000 : ℝ)) (Y := (81579930294581/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (24813919/25000000 : ℝ) ^ p + (939806029/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24813919/25000000 : ℝ)) (y := (939806029/1000000000 : ℝ)) (X := (81579930294581/100000000000000 : ℝ)) (Y := (3684017418419/20000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (821069228/868635281 : ℝ) ^ p + (860931311/868635281 : ℝ) ^ p := by
    exact cert_lt (x := (821069228/868635281 : ℝ)) (y := (860931311/868635281 : ℝ)) (X := (10777002401149/50000000000000 : ℝ)) (Y := (78445996292277/100000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (n' := (868635281/1000000000 : ℝ)) (Ab := (205267307/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1932362789/1000000000 : ℝ)) (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (849582098/921938425 : ℝ) ^ p + (183617288/184387685 : ℝ) ^ p := by
    exact cert_lt (x := (849582098/921938425 : ℝ)) (y := (183617288/184387685 : ℝ)) (X := (134780994761/1250000000000 : ℝ)) (Y := (5576095040917/6250000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1082524459/1156123150 : ℝ) ^ p + (114841918/115612315 : ℝ) ^ p := by
    exact cert_lt (x := (1082524459/1156123150 : ℝ)) (y := (114841918/115612315 : ℝ)) (X := (8327912554513/50000000000000 : ℝ)) (Y := (41672087767457/50000000000000 : ℝ)) 109 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (24813919/25000000 : ℝ)) (U := (23122463/20000000 : ℝ)) (Ab := (424791049/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (939806029/1000000000 : ℝ)) (σ := (24813919/25000000 : ℝ)) (Ab := (1082524459/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab019
