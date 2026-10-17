import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 97, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab097 (p : ℝ) (hpa : (769/32 : ℝ) ≤ p) (hpb : p ≤ (385/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (418697523157/20993700000000 : ℝ) (10263797/1000000000 : ℝ) (4000000629811/20993700000000 : ℝ) (3033/2500 : ℝ) (38864193/20000000 : ℝ) (971568429/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (298401473/250000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2227/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(1151/2500 : ℝ)
      else (7753/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11851/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (418697523157/20993700000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (10263797/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (230164879/250000000 : ℝ) ^ p + (248476083/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (230164879/250000000 : ℝ)) (y := (248476083/250000000 : ℝ)) (X := (3420371767831/25000000000000 : ℝ)) (Y := (43159265490349/50000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248476083/250000000 : ℝ) ^ p + (230164879/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248476083/250000000 : ℝ)) (y := (230164879/250000000 : ℝ)) (X := (43159265490349/50000000000000 : ℝ)) (Y := (3420371767831/25000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (239320481/125000000 : ℝ)) (τ := (230164879/250000000 : ℝ)) (σ := (248476083/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (261547475/276662518 : ℝ) ^ p + (819723757/829987554 : ℝ) ^ p := by
    exact cert_lt (x := (261547475/276662518 : ℝ)) (y := (819723757/829987554 : ℝ)) (X := (25874976628469/100000000000000 : ℝ)) (Y := (2316407022047/3125000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (230164879/250000000 : ℝ)) (n' := (414993777/500000000 : ℝ)) (Ab := (31385697/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (926240463/1000000000 : ℝ) ^ p + (496433583/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (926240463/1000000000 : ℝ)) (y := (496433583/500000000 : ℝ)) (X := (7911525317477/50000000000000 : ℝ)) (Y := (4208848311791/5000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496433583/500000000 : ℝ) ^ p + (926240463/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496433583/500000000 : ℝ)) (y := (926240463/1000000000 : ℝ)) (X := (4208848311791/5000000000000 : ℝ)) (Y := (7911525317477/50000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1919107629/1000000000 : ℝ)) (τ := (926240463/1000000000 : ℝ)) (σ := (496433583/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (790648576/836578255 : ℝ) ^ p + (826314458/836578255 : ℝ) ^ p := by
    exact cert_lt (x := (790648576/836578255 : ℝ)) (y := (826314458/836578255 : ℝ)) (X := (25698833862353/100000000000000 : ℝ)) (Y := (74301167646853/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (926240463/1000000000 : ℝ)) (n' := (167315651/200000000 : ℝ)) (Ab := (3088471/3906250 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (926477749/1000000000 : ℝ) ^ p + (496409593/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (926477749/1000000000 : ℝ)) (y := (496409593/500000000 : ℝ)) (X := (15920878550679/100000000000000 : ℝ)) (Y := (1313736542161/1562500000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496409593/500000000 : ℝ) ^ p + (926477749/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496409593/500000000 : ℝ)) (y := (926477749/1000000000 : ℝ)) (X := (1313736542161/1562500000000 : ℝ)) (Y := (15920878550679/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (383859387/200000000 : ℝ)) (τ := (926477749/1000000000 : ℝ)) (σ := (496409593/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (790903109/836857609 : ℝ) ^ p + (826593812/836857609 : ℝ) ^ p := by
    exact cert_lt (x := (790903109/836857609 : ℝ)) (y := (826593812/836857609 : ℝ)) (X := (5138283964071/20000000000000 : ℝ)) (Y := (14861716228981/20000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (926477749/1000000000 : ℝ)) (n' := (836857609/1000000000 : ℝ)) (Ab := (790903109/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (926487733/1000000000 : ℝ) ^ p + (24820429/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (926487733/1000000000 : ℝ)) (y := (24820429/25000000 : ℝ)) (X := (7962503710883/50000000000000 : ℝ)) (Y := (21018752559623/25000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (24820429/25000000 : ℝ) ^ p + (926487733/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (24820429/25000000 : ℝ)) (y := (926487733/1000000000 : ℝ)) (X := (21018752559623/25000000000000 : ℝ)) (Y := (7962503710883/50000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1919304893/1000000000 : ℝ)) (τ := (926487733/1000000000 : ℝ)) (σ := (24820429/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (395456909/418434681 : ℝ) ^ p + (826605565/836869362 : ℝ) ^ p := by
    exact cert_lt (x := (395456909/418434681 : ℝ)) (y := (826605565/836869362 : ℝ)) (X := (6422777065337/25000000000000 : ℝ)) (Y := (37154446476563/50000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (926487733/1000000000 : ℝ)) (n' := (418434681/500000000 : ℝ)) (Ab := (395456909/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (463244077/500000000 : ℝ) ^ p + (496408537/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (463244077/500000000 : ℝ)) (y := (496408537/500000000 : ℝ)) (X := (15925181548353/100000000000000 : ℝ)) (Y := (84074834997211/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496408537/500000000 : ℝ) ^ p + (463244077/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496408537/500000000 : ℝ)) (y := (463244077/500000000 : ℝ)) (X := (84074834997211/100000000000000 : ℝ)) (Y := (15925181548353/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (479826307/250000000 : ℝ)) (τ := (463244077/500000000 : ℝ)) (σ := (496408537/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (790914269/836869857 : ℝ) ^ p + (826606060/836869857 : ℝ) ^ p := by
    exact cert_lt (x := (790914269/836869857 : ℝ)) (y := (826606060/836869857 : ℝ)) (X := (6422773779077/25000000000000 : ℝ)) (Y := (74308906085359/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (463244077/500000000 : ℝ)) (n' := (836869857/1000000000 : ℝ)) (Ab := (790914269/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926488171/1000000000 : ℝ) ^ p + (992817071/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926488171/1000000000 : ℝ)) (y := (992817071/1000000000 : ℝ)) (X := (15925188579631/100000000000000 : ℝ)) (Y := (84074828884149/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992817071/1000000000 : ℝ) ^ p + (926488171/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992817071/1000000000 : ℝ)) (y := (926488171/1000000000 : ℝ)) (X := (84074828884149/100000000000000 : ℝ)) (Y := (15925188579631/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (959652621/500000000 : ℝ)) (τ := (926488171/1000000000 : ℝ)) (σ := (992817071/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (131819048/139478313 : ℝ) ^ p + (826606081/836869878 : ℝ) ^ p := by
    exact cert_lt (x := (131819048/139478313 : ℝ)) (y := (826606081/836869878 : ℝ)) (X := (1027643778177/4000000000000 : ℝ)) (Y := (18577226660621/25000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926488171/1000000000 : ℝ)) (n' := (418434939/500000000 : ℝ)) (Ab := (49432143/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (926488173/1000000000 : ℝ) ^ p + (99281707/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (926488173/1000000000 : ℝ)) (y := (99281707/100000000 : ℝ)) (X := (15925189406841/100000000000000 : ℝ)) (Y := (42037413423231/50000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (99281707/100000000 : ℝ) ^ p + (926488173/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99281707/100000000 : ℝ)) (y := (926488173/1000000000 : ℝ)) (X := (42037413423231/50000000000000 : ℝ)) (Y := (15925189406841/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1919305243/1000000000 : ℝ)) (τ := (926488173/1000000000 : ℝ)) (σ := (99281707/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (4652437/4922764 : ℝ) ^ p + (826606083/836869880 : ℝ) ^ p := by
    exact cert_lt (x := (4652437/4922764 : ℝ)) (y := (826606083/836869880 : ℝ)) (X := (6422773635067/25000000000000 : ℝ)) (Y := (74308906695543/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (926488173/1000000000 : ℝ)) (n' := (20921747/25000000 : ℝ)) (Ab := (79091429/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1919305243/1000000000 : ℝ)) (τ := (926488173/1000000000 : ℝ)) (σ := (99281707/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (926488173/1000000000 : ℝ)) (n' := (20921747/25000000 : ℝ)) (Ab := (79091429/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1919305243/1000000000 : ℝ)) (τ := (926488173/1000000000 : ℝ)) (σ := (99281707/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (926488173/1000000000 : ℝ)) (n' := (20921747/25000000 : ℝ)) (Ab := (79091429/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1919305243/1000000000 : ℝ)) (τ := (926488173/1000000000 : ℝ)) (σ := (99281707/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (926488173/1000000000 : ℝ)) (n' := (20921747/25000000 : ℝ)) (Ab := (79091429/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1919305243/1000000000 : ℝ)) (τ := (926488173/1000000000 : ℝ)) (σ := (99281707/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (414636395/451598527 : ℝ) ^ p + (1796130311/1806394108 : ℝ) ^ p := by
    exact cert_lt (x := (414636395/451598527 : ℝ)) (y := (1796130311/1806394108 : ℝ)) (X := (3203169111003/25000000000000 : ℝ)) (Y := (21796830978837/25000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (278356390/298401473 : ℝ) ^ p + (1183342095/1193605892 : ℝ) ^ p := by
    exact cert_lt (x := (278356390/298401473 : ℝ)) (y := (1183342095/1193605892 : ℝ)) (X := (9381841858439/50000000000000 : ℝ)) (Y := (81236316859163/100000000000000 : ℝ)) 385 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (99281707/100000000 : ℝ)) (U := (298401473/250000000 : ℝ)) (Ab := (82927279/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (926488173/1000000000 : ℝ)) (σ := (99281707/100000000 : ℝ)) (Ab := (27835639/25000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab097
