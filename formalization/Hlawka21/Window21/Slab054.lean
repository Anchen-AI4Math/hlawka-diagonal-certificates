import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 54, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab054 (p : ℝ) (hpa : (363/16 : ℝ) ≤ p) (hpb : p ≤ (727/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1054350215929/49549500000000 : ℝ) (10969433/1000000000 : ℝ) (2000000297297/9909900000000 : ℝ) (3033/2500 : ℝ) (969950813/500000000 : ℝ) (969910051/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (149132537/125000000 : ℝ)) ∧
    (∀ j i, if j = i then -(693/625 : ℝ) ≤ X j i ∧ X j i ≤ -(4523/10000 : ℝ)
      else (3837/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5921/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1054350215929/49549500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10969433/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (457855879/500000000 : ℝ) ^ p + (993623063/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (457855879/500000000 : ℝ)) (y := (993623063/1000000000 : ℝ)) (X := (6763594001043/50000000000000 : ℝ)) (Y := (432364142233/500000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993623063/1000000000 : ℝ) ^ p + (457855879/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993623063/1000000000 : ℝ)) (y := (457855879/500000000 : ℝ)) (X := (432364142233/500000000000 : ℝ)) (Y := (6763594001043/50000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1909334821/1000000000 : ℝ)) (τ := (457855879/500000000 : ℝ)) (σ := (993623063/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (778132373/825371862 : ℝ) ^ p + (814402429/825371862 : ℝ) ^ p := by
    exact cert_lt (x := (778132373/825371862 : ℝ)) (y := (814402429/825371862 : ℝ)) (X := (26211199304917/100000000000000 : ℝ)) (Y := (73788801739121/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (457855879/500000000 : ℝ)) (n' := (412685931/500000000 : ℝ)) (Ab := (778132373/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (921476983/1000000000 : ℝ) ^ p + (124070293/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (921476983/1000000000 : ℝ)) (y := (124070293/125000000 : ℝ)) (X := (15600267532841/100000000000000 : ℝ)) (Y := (84399748292229/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124070293/125000000 : ℝ) ^ p + (921476983/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124070293/125000000 : ℝ)) (y := (921476983/1000000000 : ℝ)) (X := (84399748292229/100000000000000 : ℝ)) (Y := (15600267532841/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1914039327/1000000000 : ℝ)) (τ := (921476983/1000000000 : ℝ)) (σ := (124070293/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (392175421/416114531 : ℝ) ^ p + (821259629/832229062 : ℝ) ^ p := by
    exact cert_lt (x := (392175421/416114531 : ℝ)) (y := (821259629/832229062 : ℝ)) (X := (26024927455549/100000000000000 : ℝ)) (Y := (73975073680111/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (921476983/1000000000 : ℝ)) (n' := (416114531/500000000 : ℝ)) (Ab := (392175421/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (115217807/125000000 : ℝ) ^ p + (992509293/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (115217807/125000000 : ℝ)) (y := (992509293/1000000000 : ℝ)) (X := (15702693866383/100000000000000 : ℝ)) (Y := (84297322504777/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992509293/1000000000 : ℝ) ^ p + (115217807/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (992509293/1000000000 : ℝ)) (y := (115217807/125000000 : ℝ)) (X := (84297322504777/100000000000000 : ℝ)) (Y := (15702693866383/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1914251749/1000000000 : ℝ)) (τ := (115217807/125000000 : ℝ)) (σ := (992509293/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (392318107/416271903 : ℝ) ^ p + (821574373/832543806 : ℝ) ^ p := by
    exact cert_lt (x := (392318107/416271903 : ℝ)) (y := (821574373/832543806 : ℝ)) (X := (26016440477107/100000000000000 : ℝ)) (Y := (73983560553531/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (115217807/125000000 : ℝ)) (n' := (416271903/500000000 : ℝ)) (Ab := (392318107/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (921754549/1000000000 : ℝ) ^ p + (992506867/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (921754549/1000000000 : ℝ)) (y := (992506867/1000000000 : ℝ)) (X := (7853687467103/50000000000000 : ℝ)) (Y := (10536580182359/12500000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992506867/1000000000 : ℝ) ^ p + (921754549/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992506867/1000000000 : ℝ)) (y := (921754549/1000000000 : ℝ)) (X := (10536580182359/12500000000000 : ℝ)) (Y := (7853687467103/50000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (239282677/125000000 : ℝ)) (τ := (921754549/1000000000 : ℝ)) (σ := (992506867/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (784649211/832558141 : ℝ) ^ p + (821588708/832558141 : ℝ) ^ p := by
    exact cert_lt (x := (784649211/832558141 : ℝ)) (y := (821588708/832558141 : ℝ)) (X := (5203210792549/20000000000000 : ℝ)) (Y := (73983946957133/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (921754549/1000000000 : ℝ)) (n' := (832558141/1000000000 : ℝ)) (Ab := (784649211/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (9217551/10000000 : ℝ) ^ p + (248126689/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (9217551/10000000 : ℝ)) (y := (248126689/250000000 : ℝ)) (X := (15707588252043/100000000000000 : ℝ)) (Y := (42146213643353/50000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248126689/250000000 : ℝ) ^ p + (9217551/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (248126689/250000000 : ℝ)) (y := (9217551/10000000 : ℝ)) (X := (42146213643353/50000000000000 : ℝ)) (Y := (15707588252043/100000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (59820683/31250000 : ℝ)) (τ := (9217551/10000000 : ℝ)) (σ := (248126689/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (784649803/832558794 : ℝ) ^ p + (821589361/832558794 : ℝ) ^ p := by
    exact cert_lt (x := (784649803/832558794 : ℝ)) (y := (821589361/832558794 : ℝ)) (X := (13008018159239/50000000000000 : ℝ)) (Y := (14796792911729/20000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (9217551/10000000 : ℝ)) (n' := (416279397/500000000 : ℝ)) (Ab := (784649803/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (7374041/8000000 : ℝ) ^ p + (992506751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (7374041/8000000 : ℝ)) (y := (992506751/1000000000 : ℝ)) (X := (1963449741347/12500000000000 : ℝ)) (Y := (21073104409831/25000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992506751/1000000000 : ℝ) ^ p + (7374041/8000000 : ℝ) ^ p := by
    exact cert_lt (x := (992506751/1000000000 : ℝ)) (y := (7374041/8000000 : ℝ)) (X := (21073104409831/25000000000000 : ℝ)) (Y := (1963449741347/12500000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (478565469/250000000 : ℝ)) (τ := (7374041/8000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (784649831/832558824 : ℝ) ^ p + (821589391/832558824 : ℝ) ^ p := by
    exact cert_lt (x := (784649831/832558824 : ℝ)) (y := (821589391/832558824 : ℝ)) (X := (2601603611233/10000000000000 : ℝ)) (Y := (7398396536729/10000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (7374041/8000000 : ℝ)) (n' := (104069853/125000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (460877563/500000000 : ℝ) ^ p + (992506751/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460877563/500000000 : ℝ)) (y := (992506751/1000000000 : ℝ)) (X := (628303932717/4000000000000 : ℝ)) (Y := (21073104409831/25000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992506751/1000000000 : ℝ) ^ p + (460877563/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992506751/1000000000 : ℝ)) (y := (460877563/500000000 : ℝ)) (X := (21073104409831/25000000000000 : ℝ)) (Y := (628303932717/4000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (112092833/118936975 : ℝ) ^ p + (821589392/832558825 : ℝ) ^ p := by
    exact cert_lt (x := (112092833/118936975 : ℝ)) (y := (821589392/832558825 : ℝ)) (X := (3252004425301/12500000000000 : ℝ)) (Y := (18495991348561/25000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (n' := (33302353/40000000 : ℝ)) (Ab := (784649831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1914261877/1000000000 : ℝ)) (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (412823223/451734926 : ℝ) ^ p + (1795970271/1806939704 : ℝ) ^ p := by
    exact cert_lt (x := (412823223/451734926 : ℝ)) (y := (1795970271/1806939704 : ℝ)) (X := (12919709226957/100000000000000 : ℝ)) (Y := (5442518189209/6250000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (554388945/596530148 : ℝ) ^ p + (1182090863/1193060296 : ℝ) ^ p := by
    exact cert_lt (x := (554388945/596530148 : ℝ)) (y := (1182090863/1193060296 : ℝ)) (X := (4732368447961/25000000000000 : ℝ)) (Y := (8107052675829/10000000000000 : ℝ)) 727 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992506751/1000000000 : ℝ)) (U := (149132537/125000000 : ℝ)) (Ab := (412823223/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (460877563/500000000 : ℝ)) (σ := (992506751/1000000000 : ℝ)) (Ab := (110877789/100000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab054
