import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 38, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab038 (p : ℝ) (hpa : (355/16 : ℝ) ≤ p) (hpb : p ≤ (711/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (211482655841/9691500000000 : ℝ) (2251393/200000000 : ℝ) (400000058149/1938300000000 : ℝ) (3033/2500 : ℝ) (969285093/500000000 : ℝ) (969242503/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192859701/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(1107/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(449/1000 : ℝ)
      else (7641/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5919/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (211482655841/9691500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2251393/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (91371009/100000000 : ℝ) ^ p + (496756041/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (91371009/100000000 : ℝ)) (y := (496756041/500000000 : ℝ)) (X := (2693035605589/20000000000000 : ℝ)) (Y := (86534839151001/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496756041/500000000 : ℝ) ^ p + (91371009/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (496756041/500000000 : ℝ)) (y := (91371009/100000000 : ℝ)) (X := (86534839151001/100000000000000 : ℝ)) (Y := (2693035605589/20000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (476805543/250000000 : ℝ)) (τ := (91371009/100000000 : ℝ)) (σ := (496756041/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (775505085/823483304 : ℝ) ^ p + (812226339/823483304 : ℝ) ^ p := by
    exact cert_lt (x := (775505085/823483304 : ℝ)) (y := (812226339/823483304 : ℝ)) (X := (13174189079169/50000000000000 : ℝ)) (Y := (18412905716499/25000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (91371009/100000000 : ℝ)) (n' := (102935413/125000000 : ℝ)) (Ab := (155101017/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (114942839/125000000 : ℝ) ^ p + (496221663/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (114942839/125000000 : ℝ)) (y := (496221663/500000000 : ℝ)) (X := (15510053689421/100000000000000 : ℝ)) (Y := (42244981203769/50000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496221663/500000000 : ℝ) ^ p + (114942839/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496221663/500000000 : ℝ)) (y := (114942839/125000000 : ℝ)) (X := (42244981203769/50000000000000 : ℝ)) (Y := (15510053689421/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (955993019/500000000 : ℝ)) (τ := (114942839/125000000 : ℝ)) (σ := (496221663/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (781802179/830440789 : ℝ) ^ p + (819183824/830440789 : ℝ) ^ p := by
    exact cert_lt (x := (781802179/830440789 : ℝ)) (y := (819183824/830440789 : ℝ)) (X := (26158128017127/100000000000000 : ℝ)) (Y := (14768374593367/20000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (114942839/125000000 : ℝ)) (n' := (830440789/1000000000 : ℝ)) (Ab := (781802179/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (229954959/250000000 : ℝ) ^ p + (248097053/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (229954959/250000000 : ℝ)) (y := (248097053/250000000 : ℝ)) (X := (3122848657061/20000000000000 : ℝ)) (Y := (21096443158169/25000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (248097053/250000000 : ℝ) ^ p + (229954959/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248097053/250000000 : ℝ)) (y := (229954959/250000000 : ℝ)) (X := (21096443158169/25000000000000 : ℝ)) (Y := (3122848657061/20000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (119513003/62500000 : ℝ)) (τ := (229954959/250000000 : ℝ)) (σ := (248097053/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (195525085/207692571 : ℝ) ^ p + (819513319/830770284 : ℝ) ^ p := by
    exact cert_lt (x := (195525085/207692571 : ℝ)) (y := (819513319/830770284 : ℝ)) (X := (2614918561993/10000000000000 : ℝ)) (Y := (14770163078181/20000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (229954959/250000000 : ℝ)) (n' := (207692571/250000000 : ℝ)) (Ab := (39105017/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (459916429/500000000 : ℝ) ^ p + (248096403/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (459916429/500000000 : ℝ)) (y := (248096403/250000000 : ℝ)) (X := (1952394442273/12500000000000 : ℝ)) (Y := (42190430258797/50000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248096403/250000000 : ℝ) ^ p + (459916429/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248096403/250000000 : ℝ)) (y := (459916429/500000000 : ℝ)) (X := (42190430258797/50000000000000 : ℝ)) (Y := (1952394442273/12500000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (191221847/100000000 : ℝ)) (τ := (459916429/500000000 : ℝ)) (σ := (248096403/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (195528587/207696441 : ℝ) ^ p + (819528799/830785764 : ℝ) ^ p := by
    exact cert_lt (x := (195528587/207696441 : ℝ)) (y := (819528799/830785764 : ℝ)) (X := (13074382909727/50000000000000 : ℝ)) (Y := (73851235365777/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (459916429/500000000 : ℝ)) (n' := (207696441/250000000 : ℝ)) (Ab := (195528587/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (919833469/1000000000 : ℝ) ^ p + (99238549/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (919833469/1000000000 : ℝ)) (y := (99238549/100000000 : ℝ)) (X := (15619386060261/100000000000000 : ℝ)) (Y := (84380630032747/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99238549/100000000 : ℝ) ^ p + (919833469/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99238549/100000000 : ℝ)) (y := (919833469/1000000000 : ℝ)) (X := (84380630032747/100000000000000 : ℝ)) (Y := (15619386060261/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1912218959/1000000000 : ℝ)) (τ := (919833469/1000000000 : ℝ)) (σ := (99238549/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (782115006/830786491 : ℝ) ^ p + (819529526/830786491 : ℝ) ^ p := by
    exact cert_lt (x := (782115006/830786491 : ℝ)) (y := (819529526/830786491 : ℝ)) (X := (3268593275211/12500000000000 : ℝ)) (Y := (36925627544537/50000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (919833469/1000000000 : ℝ)) (n' := (830786491/1000000000 : ℝ)) (Ab := (391057503/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (459916749/500000000 : ℝ) ^ p + (248096371/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (459916749/500000000 : ℝ)) (y := (248096371/250000000 : ℝ)) (X := (3904849250413/25000000000000 : ℝ)) (Y := (42190309348721/50000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (248096371/250000000 : ℝ) ^ p + (459916749/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248096371/250000000 : ℝ)) (y := (459916749/500000000 : ℝ)) (X := (42190309348721/50000000000000 : ℝ)) (Y := (3904849250413/25000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (956109491/500000000 : ℝ)) (τ := (459916749/500000000 : ℝ)) (σ := (248096371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (782115037/830786525 : ℝ) ^ p + (163905912/166157305 : ℝ) ^ p := by
    exact cert_lt (x := (782115037/830786525 : ℝ)) (y := (163905912/166157305 : ℝ)) (X := (26148745452811/100000000000000 : ℝ)) (Y := (18462814002871/25000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (459916749/500000000 : ℝ)) (n' := (33231461/40000000 : ℝ)) (Ab := (782115037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (919833499/1000000000 : ℝ) ^ p + (248096371/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (919833499/1000000000 : ℝ)) (y := (248096371/250000000 : ℝ)) (X := (15619397378941/100000000000000 : ℝ)) (Y := (42190309348721/50000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (248096371/250000000 : ℝ) ^ p + (919833499/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248096371/250000000 : ℝ)) (y := (919833499/1000000000 : ℝ)) (X := (42190309348721/50000000000000 : ℝ)) (Y := (15619397378941/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1912218983/1000000000 : ℝ)) (τ := (919833499/1000000000 : ℝ)) (σ := (248096371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (782115037/830786526 : ℝ) ^ p + (819529561/830786526 : ℝ) ^ p := by
    exact cert_lt (x := (782115037/830786526 : ℝ)) (y := (819529561/830786526 : ℝ)) (X := (26148744753483/100000000000000 : ℝ)) (Y := (73851256038613/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (919833499/1000000000 : ℝ)) (n' := (415393263/500000000 : ℝ)) (Ab := (782115037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1912218983/1000000000 : ℝ)) (τ := (919833499/1000000000 : ℝ)) (σ := (248096371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (919833499/1000000000 : ℝ)) (n' := (415393263/500000000 : ℝ)) (Ab := (782115037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1912218983/1000000000 : ℝ)) (τ := (919833499/1000000000 : ℝ)) (σ := (248096371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (919833499/1000000000 : ℝ)) (n' := (415393263/500000000 : ℝ)) (Ab := (782115037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1912218983/1000000000 : ℝ)) (τ := (919833499/1000000000 : ℝ)) (σ := (248096371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (919833499/1000000000 : ℝ)) (n' := (415393263/500000000 : ℝ)) (Ab := (782115037/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1912218983/1000000000 : ℝ)) (τ := (919833499/1000000000 : ℝ)) (σ := (248096371/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1648380231/1807140299 : ℝ) ^ p + (1795883334/1807140299 : ℝ) ^ p := by
    exact cert_lt (x := (1648380231/1807140299 : ℝ)) (y := (1795883334/1807140299 : ℝ)) (X := (12963011932691/100000000000000 : ℝ)) (Y := (21759247072801/25000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1106940315/1192859701 : ℝ) ^ p + (1181602736/1192859701 : ℝ) ^ p := by
    exact cert_lt (x := (1106940315/1192859701 : ℝ)) (y := (1181602736/1192859701 : ℝ)) (X := (4749027565099/25000000000000 : ℝ)) (Y := (81003890462123/100000000000000 : ℝ)) 711 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (248096371/250000000 : ℝ)) (U := (1192859701/1000000000 : ℝ)) (Ab := (1648380231/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (919833499/1000000000 : ℝ)) (σ := (248096371/250000000 : ℝ)) (Ab := (221388063/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab038
