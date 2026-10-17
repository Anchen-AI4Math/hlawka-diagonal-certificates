import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 92, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab092 (p : ℝ) (hpa : (191/8 : ℝ) ≤ p) (hpb : p ≤ (765/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (130948074827/6517875000000 : ℝ) (5170609/500000000 : ℝ) (1000000156429/5214300000000 : ℝ) (3033/2500 : ℝ) (971421913/500000000 : ℝ) (485692523/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1193542247/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1113/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(919/2000 : ℝ)
      else (484/625 : ℝ) ≤ X j i ∧ X j i ≤ (237/200 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (130948074827/6517875000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (5170609/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (920114147/1000000000 : ℝ) ^ p + (496936419/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (920114147/1000000000 : ℝ)) (y := (496936419/500000000 : ℝ)) (X := (13664408453799/100000000000000 : ℝ)) (Y := (17267121810277/20000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496936419/500000000 : ℝ) ^ p + (920114147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496936419/500000000 : ℝ)) (y := (920114147/1000000000 : ℝ)) (X := (17267121810277/20000000000000 : ℝ)) (Y := (13664408453799/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (382797397/200000000 : ℝ)) (τ := (920114147/1000000000 : ℝ)) (σ := (496936419/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (783923710/829482463 : ℝ) ^ p + (819141245/829482463 : ℝ) ^ p := by
    exact cert_lt (x := (783923710/829482463 : ℝ)) (y := (819141245/829482463 : ℝ)) (X := (25911836924683/100000000000000 : ℝ)) (Y := (74088164628779/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (920114147/1000000000 : ℝ)) (n' := (829482463/1000000000 : ℝ)) (Ab := (78392371/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (925716617/1000000000 : ℝ) ^ p + (49641641/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (925716617/1000000000 : ℝ)) (y := (49641641/50000000 : ℝ)) (X := (15798509349227/100000000000000 : ℝ)) (Y := (84201507567279/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (49641641/50000000 : ℝ) ^ p + (925716617/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (49641641/50000000 : ℝ)) (y := (925716617/1000000000 : ℝ)) (X := (84201507567279/100000000000000 : ℝ)) (Y := (15798509349227/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1918549437/1000000000 : ℝ)) (τ := (925716617/1000000000 : ℝ)) (σ := (49641641/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (789954489/836103797 : ℝ) ^ p + (825762579/836103797 : ℝ) ^ p := by
    exact cert_lt (x := (789954489/836103797 : ℝ)) (y := (825762579/836103797 : ℝ)) (X := (5146911617699/20000000000000 : ℝ)) (Y := (18566360760637/25000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (925716617/1000000000 : ℝ)) (n' := (836103797/1000000000 : ℝ)) (Ab := (789954489/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925956963/1000000000 : ℝ) ^ p + (248196071/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925956963/1000000000 : ℝ)) (y := (248196071/250000000 : ℝ)) (X := (15896860252867/100000000000000 : ℝ)) (Y := (42051578594193/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248196071/250000000 : ℝ) ^ p + (925956963/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248196071/250000000 : ℝ)) (y := (925956963/1000000000 : ℝ)) (X := (42051578594193/50000000000000 : ℝ)) (Y := (15896860252867/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1918741247/1000000000 : ℝ)) (τ := (925956963/1000000000 : ℝ)) (σ := (248196071/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (790212364/836386973 : ℝ) ^ p + (826045755/836386973 : ℝ) ^ p := by
    exact cert_lt (x := (790212364/836386973 : ℝ)) (y := (826045755/836386973 : ℝ)) (X := (2572702998523/10000000000000 : ℝ)) (Y := (14854594227199/20000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925956963/1000000000 : ℝ)) (n' := (836386973/1000000000 : ℝ)) (Ab := (197553091/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462983583/500000000 : ℝ) ^ p + (124097777/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (462983583/500000000 : ℝ)) (y := (124097777/125000000 : ℝ)) (X := (15901048330343/100000000000000 : ℝ)) (Y := (84098969165599/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124097777/125000000 : ℝ) ^ p + (462983583/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124097777/125000000 : ℝ)) (y := (462983583/500000000 : ℝ)) (X := (84098969165599/100000000000000 : ℝ)) (Y := (15901048330343/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (959374691/500000000 : ℝ)) (τ := (462983583/500000000 : ℝ)) (σ := (124097777/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (790223310/836398993 : ℝ) ^ p + (826057775/836398993 : ℝ) ^ p := by
    exact cert_lt (x := (790223310/836398993 : ℝ)) (y := (826057775/836398993 : ℝ)) (X := (6431677640697/25000000000000 : ℝ)) (Y := (37136645292561/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (462983583/500000000 : ℝ)) (n' := (836398993/1000000000 : ℝ)) (Ab := (79022331/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (925967599/1000000000 : ℝ) ^ p + (62048883/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (925967599/1000000000 : ℝ)) (y := (62048883/62500000 : ℝ)) (X := (7950613044723/50000000000000 : ℝ)) (Y := (10512348869537/12500000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62048883/62500000 : ℝ) ^ p + (925967599/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62048883/62500000 : ℝ)) (y := (925967599/1000000000 : ℝ)) (X := (10512348869537/12500000000000 : ℝ)) (Y := (7950613044723/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1918749727/1000000000 : ℝ)) (τ := (925967599/1000000000 : ℝ)) (σ := (62048883/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (790223774/836399503 : ℝ) ^ p + (826058285/836399503 : ℝ) ^ p := by
    exact cert_lt (x := (790223774/836399503 : ℝ)) (y := (826058285/836399503 : ℝ)) (X := (25726696674803/100000000000000 : ℝ)) (Y := (37136652069473/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (925967599/1000000000 : ℝ)) (n' := (836399503/1000000000 : ℝ)) (Ab := (395111887/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (462983809/500000000 : ℝ) ^ p + (248195531/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (462983809/500000000 : ℝ)) (y := (248195531/250000000 : ℝ)) (X := (15901233889543/100000000000000 : ℝ)) (Y := (42049391427941/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248195531/250000000 : ℝ) ^ p + (462983809/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248195531/250000000 : ℝ)) (y := (462983809/500000000 : ℝ)) (X := (42049391427941/50000000000000 : ℝ)) (Y := (15901233889543/100000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (959374871/500000000 : ℝ)) (τ := (462983809/500000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (790223794/836399525 : ℝ) ^ p + (826058307/836399525 : ℝ) ^ p := by
    exact cert_lt (x := (790223794/836399525 : ℝ)) (y := (826058307/836399525 : ℝ)) (X := (12863348031753/50000000000000 : ℝ)) (Y := (3713665236181/5000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (462983809/500000000 : ℝ)) (n' := (33455981/40000000 : ℝ)) (Ab := (395111897/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (925967619/1000000000 : ℝ) ^ p + (248195531/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (925967619/1000000000 : ℝ)) (y := (248195531/250000000 : ℝ)) (X := (7950617150037/50000000000000 : ℝ)) (Y := (42049391427941/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248195531/250000000 : ℝ) ^ p + (925967619/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248195531/250000000 : ℝ)) (y := (925967619/1000000000 : ℝ)) (X := (42049391427941/50000000000000 : ℝ)) (Y := (7950617150037/50000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (790223795/836399526 : ℝ) ^ p + (413029154/418199763 : ℝ) ^ p := by
    exact cert_lt (x := (790223795/836399526 : ℝ)) (y := (413029154/418199763 : ℝ)) (X := (12863348053237/50000000000000 : ℝ)) (Y := (18568326187549/25000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (n' := (418199763/500000000 : ℝ)) (Ab := (158044759/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1918749743/1000000000 : ℝ)) (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1657742392/1806457753 : ℝ) ^ p + (1796116535/1806457753 : ℝ) ^ p := by
    exact cert_lt (x := (1657742392/1806457753 : ℝ)) (y := (1796116535/1806457753 : ℝ)) (X := (6412236140197/50000000000000 : ℝ)) (Y := (8717552801053/10000000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1112905784/1193542247 : ℝ) ^ p + (1183201029/1193542247 : ℝ) ^ p := by
    exact cert_lt (x := (1112905784/1193542247 : ℝ)) (y := (1183201029/1193542247 : ℝ)) (X := (18782030969977/100000000000000 : ℝ)) (Y := (2030449242983/2500000000000 : ℝ)) 765 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248195531/250000000 : ℝ)) (U := (1193542247/1000000000 : ℝ)) (Ab := (207217799/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (925967619/1000000000 : ℝ)) (σ := (248195531/250000000 : ℝ)) (Ab := (139113223/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab092
