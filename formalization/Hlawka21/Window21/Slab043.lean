import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 43, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab043 (p : ℝ) (hpa : (715/32 : ℝ) ≤ p) (hpb : p ≤ (179/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (211288338263/9759750000000 : ℝ) (2233107/200000000 : ℝ) (800000117117/3903900000000 : ℝ) (3033/2500 : ℝ) (969496277/500000000 : ℝ) (15147723/15625000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192922161/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2769/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(4501/10000 : ℝ)
      else (1913/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11839/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (211288338263/9759750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2233107/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (182869141/200000000 : ℝ) ^ p + (993547151/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (182869141/200000000 : ℝ)) (y := (993547151/1000000000 : ℝ)) (X := (13484841723169/100000000000000 : ℝ)) (Y := (86515175395361/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993547151/1000000000 : ℝ) ^ p + (182869141/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993547151/1000000000 : ℝ)) (y := (182869141/200000000 : ℝ)) (X := (86515175395361/100000000000000 : ℝ)) (Y := (13484841723169/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (238486607/125000000 : ℝ)) (τ := (182869141/200000000 : ℝ)) (σ := (993547151/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (776338975/824084319 : ℝ) ^ p + (270972928/274694773 : ℝ) ^ p := by
    exact cert_lt (x := (776338975/824084319 : ℝ)) (y := (270972928/274694773 : ℝ)) (X := (6576187408911/25000000000000 : ℝ)) (Y := (18423812818357/25000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (182869141/200000000 : ℝ)) (n' := (824084319/1000000000 : ℝ)) (Ab := (31053559/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46007869/50000000 : ℝ) ^ p + (496240427/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (46007869/50000000 : ℝ)) (y := (496240427/500000000 : ℝ)) (X := (7769351992943/50000000000000 : ℝ)) (Y := (42230656351639/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496240427/500000000 : ℝ) ^ p + (46007869/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (496240427/500000000 : ℝ)) (y := (46007869/50000000 : ℝ)) (X := (42230656351639/50000000000000 : ℝ)) (Y := (7769351992943/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (956319117/500000000 : ℝ)) (τ := (46007869/50000000 : ℝ)) (σ := (496240427/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (260870522/277003481 : ℝ) ^ p + (273281636/277003481 : ℝ) ^ p := by
    exact cert_lt (x := (260870522/277003481 : ℝ)) (y := (273281636/277003481 : ℝ)) (X := (13057877585859/50000000000000 : ℝ)) (Y := (36942123098811/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46007869/50000000 : ℝ)) (n' := (831010443/1000000000 : ℝ)) (Ab := (391305783/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (920430791/1000000000 : ℝ) ^ p + (198485279/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (920430791/1000000000 : ℝ)) (y := (198485279/200000000 : ℝ)) (X := (15642340180793/100000000000000 : ℝ)) (Y := (10544709495857/12500000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198485279/200000000 : ℝ) ^ p + (920430791/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198485279/200000000 : ℝ)) (y := (920430791/1000000000 : ℝ)) (X := (10544709495857/12500000000000 : ℝ)) (Y := (15642340180793/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (956428593/500000000 : ℝ)) (τ := (920430791/1000000000 : ℝ)) (σ := (198485279/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (782905648/831335229 : ℝ) ^ p + (91129966/92370581 : ℝ) ^ p := by
    exact cert_lt (x := (782905648/831335229 : ℝ)) (y := (91129966/92370581 : ℝ)) (X := (26106958365053/100000000000000 : ℝ)) (Y := (14778608533973/20000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (920430791/1000000000 : ℝ)) (n' := (831335229/1000000000 : ℝ)) (Ab := (48931603/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (920443513/1000000000 : ℝ) ^ p + (992423851/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920443513/1000000000 : ℝ)) (y := (992423851/1000000000 : ℝ)) (X := (15647178485083/100000000000000 : ℝ)) (Y := (84352837647253/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992423851/1000000000 : ℝ) ^ p + (920443513/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992423851/1000000000 : ℝ)) (y := (920443513/1000000000 : ℝ)) (X := (84352837647253/100000000000000 : ℝ)) (Y := (15647178485083/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (478216841/250000000 : ℝ)) (τ := (920443513/1000000000 : ℝ)) (σ := (992423851/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (782919330/831350339 : ℝ) ^ p + (820184804/831350339 : ℝ) ^ p := by
    exact cert_lt (x := (782919330/831350339 : ℝ)) (y := (820184804/831350339 : ℝ)) (X := (5221309935303/20000000000000 : ℝ)) (Y := (36946725882327/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (920443513/1000000000 : ℝ)) (n' := (831350339/1000000000 : ℝ)) (Ab := (78291933/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (115055513/125000000 : ℝ) ^ p + (992423733/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115055513/125000000 : ℝ)) (y := (992423733/1000000000 : ℝ)) (X := (15647403283061/100000000000000 : ℝ)) (Y := (42176306617387/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992423733/1000000000 : ℝ) ^ p + (115055513/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992423733/1000000000 : ℝ)) (y := (115055513/125000000 : ℝ)) (X := (42176306617387/50000000000000 : ℝ)) (Y := (15647403283061/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1912867837/1000000000 : ℝ)) (τ := (115055513/125000000 : ℝ)) (σ := (992423733/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (782919965/831351041 : ℝ) ^ p + (820185506/831351041 : ℝ) ^ p := by
    exact cert_lt (x := (782919965/831351041 : ℝ)) (y := (820185506/831351041 : ℝ)) (X := (1631658137507/6250000000000 : ℝ)) (Y := (36946735385301/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (115055513/125000000 : ℝ)) (n' := (831351041/1000000000 : ℝ)) (Ab := (156583993/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (230111033/250000000 : ℝ) ^ p + (992423727/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (230111033/250000000 : ℝ)) (y := (992423727/1000000000 : ℝ)) (X := (3129482786693/20000000000000 : ℝ)) (Y := (42176300911993/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992423727/1000000000 : ℝ) ^ p + (230111033/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992423727/1000000000 : ℝ)) (y := (230111033/250000000 : ℝ)) (X := (42176300911993/50000000000000 : ℝ)) (Y := (3129482786693/20000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1912867859/1000000000 : ℝ)) (τ := (230111033/250000000 : ℝ)) (σ := (992423727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (260973332/277117025 : ℝ) ^ p + (54679036/55423405 : ℝ) ^ p := by
    exact cert_lt (x := (260973332/277117025 : ℝ)) (y := (54679036/55423405 : ℝ)) (X := (203957261247/781250000000 : ℝ)) (Y := (73893471691117/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (230111033/250000000 : ℝ)) (n' := (33254043/40000000 : ℝ)) (Ab := (195729999/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (920444133/1000000000 : ℝ) ^ p + (992423727/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920444133/1000000000 : ℝ)) (y := (992423727/1000000000 : ℝ)) (X := (3911853578459/25000000000000 : ℝ)) (Y := (42176300911993/50000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992423727/1000000000 : ℝ) ^ p + (920444133/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992423727/1000000000 : ℝ)) (y := (920444133/1000000000 : ℝ)) (X := (42176300911993/50000000000000 : ℝ)) (Y := (3911853578459/25000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (95643393/50000000 : ℝ)) (τ := (920444133/1000000000 : ℝ)) (σ := (992423727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (782919997/831351076 : ℝ) ^ p + (820185541/831351076 : ℝ) ^ p := by
    exact cert_lt (x := (782919997/831351076 : ℝ)) (y := (820185541/831351076 : ℝ)) (X := (26106529483081/100000000000000 : ℝ)) (Y := (73893471718191/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (920444133/1000000000 : ℝ)) (n' := (207837769/250000000 : ℝ)) (Ab := (782919997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (95643393/50000000 : ℝ)) (τ := (920444133/1000000000 : ℝ)) (σ := (992423727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (920444133/1000000000 : ℝ)) (n' := (207837769/250000000 : ℝ)) (Ab := (782919997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (95643393/50000000 : ℝ)) (τ := (920444133/1000000000 : ℝ)) (σ := (992423727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (920444133/1000000000 : ℝ)) (n' := (207837769/250000000 : ℝ)) (Ab := (782919997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (95643393/50000000 : ℝ)) (τ := (920444133/1000000000 : ℝ)) (σ := (992423727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (920444133/1000000000 : ℝ)) (n' := (207837769/250000000 : ℝ)) (Ab := (782919997/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (95643393/50000000 : ℝ)) (τ := (920444133/1000000000 : ℝ)) (σ := (992423727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1649303811/1807077839 : ℝ) ^ p + (1795912304/1807077839 : ℝ) ^ p := by
    exact cert_lt (x := (1649303811/1807077839 : ℝ)) (y := (1795912304/1807077839 : ℝ)) (X := (12949263879249/100000000000000 : ℝ)) (Y := (87050736316773/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1107521218/1192922161 : ℝ) ^ p + (1181756626/1192922161 : ℝ) ^ p := by
    exact cert_lt (x := (1107521218/1192922161 : ℝ)) (y := (1181756626/1192922161 : ℝ)) (X := (9487490530783/50000000000000 : ℝ)) (Y := (81025019691883/100000000000000 : ℝ)) 179 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992423727/1000000000 : ℝ)) (U := (1192922161/1000000000 : ℝ)) (Ab := (1649303811/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (920444133/1000000000 : ℝ)) (σ := (992423727/1000000000 : ℝ)) (Ab := (553760609/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab043
