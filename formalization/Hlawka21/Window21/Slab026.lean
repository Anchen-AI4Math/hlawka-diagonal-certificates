import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 26, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab026 (p : ℝ) (hpa : (349/16 : ℝ) ≤ p) (hpb : p ≤ (699/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (264950497951/11909625000000 : ℝ) (11482527/1000000000 : ℝ) (2000000285831/9527700000000 : ℝ) (3033/2500 : ℝ) (968766119/500000000 : ℝ) (484361039/500000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (29817773/25000000 : ℝ)) ∧
    (∀ j i, if j = i then -(691/625 : ℝ) ≤ X j i ∧ X j i ≤ -(279/625 : ℝ)
      else (476/625 : ℝ) ≤ X j i ∧ X j i ≤ (2959/2500 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (264950497951/11909625000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11482527/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (456072783/500000000 : ℝ) ^ p + (993426449/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (456072783/500000000 : ℝ)) (y := (993426449/1000000000 : ℝ)) (X := (2683374580971/20000000000000 : ℝ)) (Y := (17316628745101/20000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993426449/1000000000 : ℝ) ^ p + (456072783/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993426449/1000000000 : ℝ)) (y := (456072783/500000000 : ℝ)) (X := (17316628745101/20000000000000 : ℝ)) (Y := (2683374580971/20000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381114403/200000000 : ℝ)) (τ := (456072783/500000000 : ℝ)) (σ := (993426449/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (257818019/273999563 : ℝ) ^ p + (270172054/273999563 : ℝ) ^ p := by
    exact cert_lt (x := (257818019/273999563 : ℝ)) (y := (270172054/273999563 : ℝ)) (X := (5291215467153/20000000000000 : ℝ)) (Y := (18385980954949/25000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (456072783/500000000 : ℝ)) (n' := (821998689/1000000000 : ℝ)) (Ab := (773454057/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (11475349/12500000 : ℝ) ^ p + (198470403/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (11475349/12500000 : ℝ)) (y := (198470403/200000000 : ℝ)) (X := (7719751898351/50000000000000 : ℝ)) (Y := (84560512207377/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (198470403/200000000 : ℝ) ^ p + (11475349/12500000 : ℝ) ^ p := by
    exact cert_lt (x := (198470403/200000000 : ℝ)) (y := (11475349/12500000 : ℝ)) (X := (84560512207377/100000000000000 : ℝ)) (Y := (7719751898351/50000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (382075987/200000000 : ℝ)) (τ := (11475349/12500000 : ℝ)) (σ := (198470403/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (48738100/51814463 : ℝ) ^ p + (817548881/829031408 : ℝ) ^ p := by
    exact cert_lt (x := (48738100/51814463 : ℝ)) (y := (817548881/829031408 : ℝ)) (X := (26262771238379/100000000000000 : ℝ)) (Y := (18434307541537/25000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (11475349/12500000 : ℝ)) (n' := (51814463/62500000 : ℝ)) (Ab := (487381/625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (459157117/500000000 : ℝ) ^ p + (124036911/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (459157117/500000000 : ℝ)) (y := (124036911/125000000 : ℝ)) (X := (15545029794071/100000000000000 : ℝ)) (Y := (42227493021921/50000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (124036911/125000000 : ℝ) ^ p + (459157117/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124036911/125000000 : ℝ)) (y := (459157117/500000000 : ℝ)) (X := (42227493021921/50000000000000 : ℝ)) (Y := (15545029794071/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (955304761/500000000 : ℝ)) (τ := (459157117/500000000 : ℝ)) (σ := (124036911/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (390058933/414686295 : ℝ) ^ p + (272630021/276457530 : ℝ) ^ p := by
    exact cert_lt (x := (390058933/414686295 : ℝ)) (y := (272630021/276457530 : ℝ)) (X := (3281682974553/12500000000000 : ℝ)) (Y := (73746536965437/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (459157117/500000000 : ℝ)) (n' := (82937259/100000000 : ℝ)) (Ab := (390058933/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (459164007/500000000 : ℝ) ^ p + (992292547/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459164007/500000000 : ℝ)) (y := (992292547/1000000000 : ℝ)) (X := (7775062985971/50000000000000 : ℝ)) (Y := (16889978058809/20000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992292547/1000000000 : ℝ) ^ p + (459164007/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992292547/1000000000 : ℝ)) (y := (459164007/500000000 : ℝ)) (X := (16889978058809/20000000000000 : ℝ)) (Y := (7775062985971/50000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1910620561/1000000000 : ℝ)) (τ := (459164007/500000000 : ℝ)) (σ := (992292547/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (195033175/207347252 : ℝ) ^ p + (116843783/118484144 : ℝ) ^ p := by
    exact cert_lt (x := (195033175/207347252 : ℝ)) (y := (116843783/118484144 : ℝ)) (X := (26253016148499/100000000000000 : ℝ)) (Y := (73746984652563/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (459164007/500000000 : ℝ)) (n' := (51836813/62500000 : ℝ)) (Ab := (7801327/10000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (918328677/1000000000 : ℝ) ^ p + (198458483/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (918328677/1000000000 : ℝ)) (y := (198458483/200000000 : ℝ)) (X := (7775185602799/50000000000000 : ℝ)) (Y := (16889928980467/20000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (198458483/200000000 : ℝ) ^ p + (918328677/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (198458483/200000000 : ℝ)) (y := (918328677/1000000000 : ℝ)) (X := (16889928980467/20000000000000 : ℝ)) (Y := (7775185602799/50000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (477655273/250000000 : ℝ)) (τ := (918328677/1000000000 : ℝ)) (σ := (198458483/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (390066707/414694899 : ℝ) ^ p + (272635757/276463266 : ℝ) ^ p := by
    exact cert_lt (x := (390066707/414694899 : ℝ)) (y := (272635757/276463266 : ℝ)) (X := (26252994770067/100000000000000 : ℝ)) (Y := (14749401238791/20000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (918328677/1000000000 : ℝ)) (n' := (414694899/500000000 : ℝ)) (Ab := (390066707/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (91832871/100000000 : ℝ) ^ p + (124036551/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (91832871/100000000 : ℝ)) (y := (124036551/125000000 : ℝ)) (X := (3110076682379/20000000000000 : ℝ)) (Y := (84449631889157/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124036551/125000000 : ℝ) ^ p + (91832871/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (124036551/125000000 : ℝ)) (y := (91832871/100000000 : ℝ)) (X := (84449631889157/100000000000000 : ℝ)) (Y := (3110076682379/20000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (955310559/500000000 : ℝ)) (τ := (91832871/100000000 : ℝ)) (σ := (124036551/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (260044483/276463279 : ℝ) ^ p + (272635770/276463279 : ℝ) ^ p := by
    exact cert_lt (x := (260044483/276463279 : ℝ)) (y := (272635770/276463279 : ℝ)) (X := (13126496766151/50000000000000 : ℝ)) (Y := (7374700725739/10000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (91832871/100000000 : ℝ)) (n' := (829389837/1000000000 : ℝ)) (Ab := (780133449/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (918328711/1000000000 : ℝ) ^ p + (124036551/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (918328711/1000000000 : ℝ)) (y := (124036551/125000000 : ℝ)) (X := (15550383781783/100000000000000 : ℝ)) (Y := (84449631889157/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124036551/125000000 : ℝ) ^ p + (918328711/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (124036551/125000000 : ℝ)) (y := (918328711/1000000000 : ℝ)) (X := (84449631889157/100000000000000 : ℝ)) (Y := (15550383781783/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1910621119/1000000000 : ℝ)) (τ := (918328711/1000000000 : ℝ)) (σ := (124036551/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (390066725/414694919 : ℝ) ^ p + (817907311/829389838 : ℝ) ^ p := by
    exact cert_lt (x := (390066725/414694919 : ℝ)) (y := (817907311/829389838 : ℝ)) (X := (13126496787979/50000000000000 : ℝ)) (Y := (73747007284657/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (918328711/1000000000 : ℝ)) (n' := (414694919/500000000 : ℝ)) (Ab := (15602669/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1910621119/1000000000 : ℝ)) (τ := (918328711/1000000000 : ℝ)) (σ := (124036551/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (918328711/1000000000 : ℝ)) (n' := (414694919/500000000 : ℝ)) (Ab := (15602669/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1910621119/1000000000 : ℝ)) (τ := (918328711/1000000000 : ℝ)) (σ := (124036551/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (918328711/1000000000 : ℝ)) (n' := (414694919/500000000 : ℝ)) (Ab := (15602669/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1910621119/1000000000 : ℝ)) (τ := (918328711/1000000000 : ℝ)) (σ := (124036551/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (918328711/1000000000 : ℝ)) (n' := (414694919/500000000 : ℝ)) (Ab := (15602669/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1910621119/1000000000 : ℝ)) (τ := (918328711/1000000000 : ℝ)) (σ := (124036551/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (164611219/180728908 : ℝ) ^ p + (1795806553/1807289080 : ℝ) ^ p := by
    exact cert_lt (x := (164611219/180728908 : ℝ)) (y := (1795806553/1807289080 : ℝ)) (X := (12996862474977/100000000000000 : ℝ)) (Y := (87003137819129/100000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (221104177/238542184 : ℝ) ^ p + (1181228393/1192710920 : ℝ) ^ p := by
    exact cert_lt (x := (221104177/238542184 : ℝ)) (y := (1181228393/1192710920 : ℝ)) (X := (1904802356789/10000000000000 : ℝ)) (Y := (16190395401211/20000000000000 : ℝ)) 699 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124036551/125000000 : ℝ)) (U := (29817773/25000000 : ℝ)) (Ab := (164611219/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (918328711/1000000000 : ℝ)) (σ := (124036551/125000000 : ℝ)) (Ab := (221104177/200000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab026
