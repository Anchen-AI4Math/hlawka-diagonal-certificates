import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 150, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab150 (p : ℝ) (hpa : (411/16 : ℝ) ≤ p) (hpb : p ≤ (823/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (207690708773/11220300000000 : ℝ) (9508271/1000000000 : ℝ) (2000000336609/11220300000000 : ℝ) (3033/2500 : ℝ) (486704447/250000000 : ℝ) (973376979/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194277433/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11187/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4689/10000 : ℝ)
      else (3919/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5931/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (207690708773/11220300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9508271/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (926014811/1000000000 : ℝ) ^ p + (62138759/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (926014811/1000000000 : ℝ)) (y := (62138759/62500000 : ℝ)) (X := (6925082769337/50000000000000 : ℝ)) (Y := (86149853481047/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (62138759/62500000 : ℝ) ^ p + (926014811/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62138759/62500000 : ℝ)) (y := (926014811/1000000000 : ℝ)) (X := (86149853481047/100000000000000 : ℝ)) (Y := (6925082769337/50000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (384046991/200000000 : ℝ)) (τ := (926014811/1000000000 : ℝ)) (σ := (62138759/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (791715527/834898874 : ℝ) ^ p + (825390603/834898874 : ℝ) ^ p := by
    exact cert_lt (x := (791715527/834898874 : ℝ)) (y := (825390603/834898874 : ℝ)) (X := (12757759677409/50000000000000 : ℝ)) (Y := (74484482192183/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (926014811/1000000000 : ℝ)) (n' := (417449437/500000000 : ℝ)) (Ab := (791715527/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931368967/1000000000 : ℝ) ^ p + (39728573/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (931368967/1000000000 : ℝ)) (y := (39728573/40000000 : ℝ)) (X := (16063876199333/100000000000000 : ℝ)) (Y := (41968071186857/50000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (39728573/40000000 : ℝ) ^ p + (931368967/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39728573/40000000 : ℝ)) (y := (931368967/1000000000 : ℝ)) (X := (41968071186857/50000000000000 : ℝ)) (Y := (16063876199333/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (481145823/250000000 : ℝ)) (τ := (931368967/1000000000 : ℝ)) (σ := (39728573/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (797464257/841173034 : ℝ) ^ p + (831664763/841173034 : ℝ) ^ p := by
    exact cert_lt (x := (797464257/841173034 : ℝ)) (y := (831664763/841173034 : ℝ)) (X := (6337686271897/25000000000000 : ℝ)) (Y := (4665578524499/6250000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931368967/1000000000 : ℝ)) (n' := (420586517/500000000 : ℝ)) (Ab := (797464257/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (465788457/500000000 : ℝ) ^ p + (198634349/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (465788457/500000000 : ℝ)) (y := (198634349/200000000 : ℝ)) (X := (16156373698427/100000000000000 : ℝ)) (Y := (838436445643/1000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (198634349/200000000 : ℝ) ^ p + (465788457/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198634349/200000000 : ℝ)) (y := (465788457/500000000 : ℝ)) (X := (838436445643/1000000000000 : ℝ)) (Y := (16156373698427/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1924748659/1000000000 : ℝ)) (τ := (465788457/500000000 : ℝ)) (σ := (198634349/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (265895613/280471999 : ℝ) ^ p + (831907726/841415997 : ℝ) ^ p := by
    exact cert_lt (x := (265895613/280471999 : ℝ)) (y := (831907726/841415997 : ℝ)) (X := (25344406354603/100000000000000 : ℝ)) (Y := (74655594734291/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (465788457/500000000 : ℝ)) (n' := (841415997/1000000000 : ℝ)) (Ab := (797686839/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (931584911/1000000000 : ℝ) ^ p + (496585051/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (931584911/1000000000 : ℝ)) (y := (496585051/500000000 : ℝ)) (X := (16159941068819/100000000000000 : ℝ)) (Y := (83840077389977/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496585051/500000000 : ℝ) ^ p + (931584911/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496585051/500000000 : ℝ)) (y := (931584911/1000000000 : ℝ)) (X := (83840077389977/100000000000000 : ℝ)) (Y := (16159941068819/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924755013/1000000000 : ℝ)) (τ := (931584911/1000000000 : ℝ)) (σ := (496585051/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (398847699/420712670 : ℝ) ^ p + (831917069/841425340 : ℝ) ^ p := by
    exact cert_lt (x := (398847699/420712670 : ℝ)) (y := (831917069/841425340 : ℝ)) (X := (5068832498583/20000000000000 : ℝ)) (Y := (37327919204387/50000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (931584911/1000000000 : ℝ)) (n' := (42071267/50000000 : ℝ)) (Ab := (398847699/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (46579261/50000000 : ℝ) ^ p + (496585019/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (46579261/50000000 : ℝ)) (y := (496585019/500000000 : ℝ)) (X := (16160078925381/100000000000000 : ℝ)) (Y := (83839938440307/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496585019/500000000 : ℝ) ^ p + (46579261/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (496585019/500000000 : ℝ)) (y := (46579261/50000000 : ℝ)) (X := (83839938440307/100000000000000 : ℝ)) (Y := (16160078925381/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (962377629/500000000 : ℝ)) (τ := (46579261/50000000 : ℝ)) (σ := (496585019/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797695729/841425701 : ℝ) ^ p + (831917430/841425701 : ℝ) ^ p := by
    exact cert_lt (x := (797695729/841425701 : ℝ)) (y := (831917430/841425701 : ℝ)) (X := (12672076654859/50000000000000 : ℝ)) (Y := (7465584782391/10000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (46579261/50000000 : ℝ)) (n' := (841425701/1000000000 : ℝ)) (Ab := (797695729/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (931585231/1000000000 : ℝ) ^ p + (248292509/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (931585231/1000000000 : ℝ)) (y := (248292509/250000000 : ℝ)) (X := (16160083832917/100000000000000 : ℝ)) (Y := (41919967049067/50000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248292509/250000000 : ℝ) ^ p + (931585231/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248292509/250000000 : ℝ)) (y := (931585231/1000000000 : ℝ)) (X := (41919967049067/50000000000000 : ℝ)) (Y := (16160083832917/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1924755267/1000000000 : ℝ)) (τ := (931585231/1000000000 : ℝ)) (σ := (248292509/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797695741/841425714 : ℝ) ^ p + (831917443/841425714 : ℝ) ^ p := by
    exact cert_lt (x := (797695741/841425714 : ℝ)) (y := (831917443/841425714 : ℝ)) (X := (3168019130583/12500000000000 : ℝ)) (Y := (933198102037/1250000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (931585231/1000000000 : ℝ)) (n' := (420712857/500000000 : ℝ)) (Ab := (797695741/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (58224077/62500000 : ℝ) ^ p + (248292509/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (58224077/62500000 : ℝ)) (y := (248292509/250000000 : ℝ)) (X := (16160084279057/100000000000000 : ℝ)) (Y := (41919967049067/50000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248292509/250000000 : ℝ) ^ p + (58224077/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (248292509/250000000 : ℝ)) (y := (58224077/62500000 : ℝ)) (X := (41919967049067/50000000000000 : ℝ)) (Y := (16160084279057/100000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (481188817/250000000 : ℝ)) (τ := (58224077/62500000 : ℝ)) (σ := (248292509/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (797695742/841425715 : ℝ) ^ p + (831917444/841425715 : ℝ) ^ p := by
    exact cert_lt (x := (797695742/841425715 : ℝ)) (y := (831917444/841425715 : ℝ)) (X := (25344153087131/100000000000000 : ℝ)) (Y := (933198102363/1250000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (58224077/62500000 : ℝ)) (n' := (168285143/200000000 : ℝ)) (Ab := (398847871/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (481188817/250000000 : ℝ)) (τ := (58224077/62500000 : ℝ)) (σ := (248292509/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (58224077/62500000 : ℝ)) (n' := (168285143/200000000 : ℝ)) (Ab := (398847871/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (481188817/250000000 : ℝ)) (τ := (58224077/62500000 : ℝ)) (σ := (248292509/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (58224077/62500000 : ℝ)) (n' := (168285143/200000000 : ℝ)) (Ab := (398847871/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (481188817/250000000 : ℝ)) (τ := (58224077/62500000 : ℝ)) (σ := (248292509/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (58224077/62500000 : ℝ)) (n' := (168285143/200000000 : ℝ)) (Ab := (398847871/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (481188817/250000000 : ℝ)) (τ := (58224077/62500000 : ℝ)) (σ := (248292509/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1666482541/1805722567 : ℝ) ^ p + (1796214296/1805722567 : ℝ) ^ p := by
    exact cert_lt (x := (1666482541/1805722567 : ℝ)) (y := (1796214296/1805722567 : ℝ)) (X := (6348409643917/50000000000000 : ℝ)) (Y := (43651590481431/50000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1118629925/1194277433 : ℝ) ^ p + (1184769162/1194277433 : ℝ) ^ p := by
    exact cert_lt (x := (1118629925/1194277433 : ℝ)) (y := (1184769162/1194277433 : ℝ)) (X := (371650026447/2000000000000 : ℝ)) (Y := (40708749700329/50000000000000 : ℝ)) 823 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248292509/250000000 : ℝ)) (U := (1194277433/1000000000 : ℝ)) (Ab := (1666482541/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (58224077/62500000 : ℝ)) (σ := (248292509/250000000 : ℝ)) (Ab := (44745197/40000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab150
