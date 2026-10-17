import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 12, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab012 (p : ℝ) (hpa : (171/8 : ℝ) ≤ p) (hpb : p ≤ (685/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (106269323707/4668300000000 : ℝ) (11757161/1000000000 : ℝ) (1000000140049/4668300000000 : ℝ) (3033/2500 : ℝ) (968138041/500000000 : ℝ) (968092209/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192539751/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11039/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4433/10000 : ℝ)
      else (1517/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11833/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (106269323707/4668300000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11757161/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (910247347/1000000000 : ℝ) ^ p + (496661923/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (910247347/1000000000 : ℝ)) (y := (496661923/500000000 : ℝ)) (X := (1669807418853/12500000000000 : ℝ)) (Y := (43320778834693/50000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496661923/500000000 : ℝ) ^ p + (910247347/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496661923/500000000 : ℝ)) (y := (910247347/1000000000 : ℝ)) (X := (43320778834693/50000000000000 : ℝ)) (Y := (1669807418853/12500000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1903571193/1000000000 : ℝ)) (τ := (910247347/1000000000 : ℝ)) (σ := (496661923/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (192742104/205046861 : ℝ) ^ p + (808430283/820187444 : ℝ) ^ p := by
    exact cert_lt (x := (192742104/205046861 : ℝ)) (y := (808430283/820187444 : ℝ)) (X := (830853220933/3125000000000 : ℝ)) (Y := (73412698159723/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (910247347/1000000000 : ℝ)) (n' := (205046861/250000000 : ℝ)) (Ab := (24092763/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (916186513/1000000000 : ℝ) ^ p + (248060809/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (916186513/1000000000 : ℝ)) (y := (248060809/250000000 : ℝ)) (X := (1535386571257/10000000000000 : ℝ)) (Y := (84646150149553/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (248060809/250000000 : ℝ) ^ p + (916186513/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248060809/250000000 : ℝ)) (y := (916186513/1000000000 : ℝ)) (X := (84646150149553/100000000000000 : ℝ)) (Y := (1535386571257/10000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1908429749/1000000000 : ℝ)) (τ := (916186513/1000000000 : ℝ)) (σ := (248060809/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (259130421/275769211 : ℝ) ^ p + (815550472/827307633 : ℝ) ^ p := by
    exact cert_lt (x := (259130421/275769211 : ℝ)) (y := (815550472/827307633 : ℝ)) (X := (26390355087819/100000000000000 : ℝ)) (Y := (73609645846779/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (916186513/1000000000 : ℝ)) (n' := (827307633/1000000000 : ℝ)) (Ab := (777391263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (458242033/500000000 : ℝ) ^ p + (992184553/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (458242033/500000000 : ℝ)) (y := (992184553/1000000000 : ℝ)) (X := (7730481507497/50000000000000 : ℝ)) (Y := (41278834231/48828125000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992184553/1000000000 : ℝ) ^ p + (458242033/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992184553/1000000000 : ℝ)) (y := (458242033/500000000 : ℝ)) (X := (41278834231/48828125000 : ℝ)) (Y := (7730481507497/50000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1908668619/1000000000 : ℝ)) (τ := (458242033/500000000 : ℝ)) (σ := (992184553/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (777711911/827663169 : ℝ) ^ p + (815906008/827663169 : ℝ) ^ p := by
    exact cert_lt (x := (777711911/827663169 : ℝ)) (y := (815906008/827663169 : ℝ)) (X := (26380596967367/100000000000000 : ℝ)) (Y := (73619404375329/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (458242033/500000000 : ℝ)) (n' := (827663169/1000000000 : ℝ)) (Ab := (777711911/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (229124701/250000000 : ℝ) ^ p + (496090817/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (229124701/250000000 : ℝ)) (y := (496090817/500000000 : ℝ)) (X := (15466286083153/100000000000000 : ℝ)) (Y := (84533728645823/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496090817/500000000 : ℝ) ^ p + (229124701/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496090817/500000000 : ℝ)) (y := (229124701/250000000 : ℝ)) (X := (84533728645823/100000000000000 : ℝ)) (Y := (15466286083153/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (954340219/500000000 : ℝ)) (τ := (229124701/250000000 : ℝ)) (σ := (496090817/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (388863895/413840388 : ℝ) ^ p + (62763355/63667752 : ℝ) ^ p := by
    exact cert_lt (x := (388863895/413840388 : ℝ)) (y := (62763355/63667752 : ℝ)) (X := (2638011383861/10000000000000 : ℝ)) (Y := (14723977491071/20000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (229124701/250000000 : ℝ)) (n' := (103460097/125000000 : ℝ)) (Ab := (77772779/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (916499533/1000000000 : ℝ) ^ p + (99218149/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (916499533/1000000000 : ℝ)) (y := (99218149/100000000 : ℝ)) (X := (15466549428581/100000000000000 : ℝ)) (Y := (84533466017667/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99218149/100000000 : ℝ) ^ p + (916499533/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (99218149/100000000 : ℝ)) (y := (916499533/1000000000 : ℝ)) (X := (84533466017667/100000000000000 : ℝ)) (Y := (15466549428581/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1908681023/1000000000 : ℝ)) (τ := (916499533/1000000000 : ℝ)) (σ := (99218149/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (59825275/63667819 : ℝ) ^ p + (62763422/63667819 : ℝ) ^ p := by
    exact cert_lt (x := (59825275/63667819 : ℝ)) (y := (62763422/63667819 : ℝ)) (X := (26380089563637/100000000000000 : ℝ)) (Y := (73619911352367/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (916499533/1000000000 : ℝ)) (n' := (827681647/1000000000 : ℝ)) (Ab := (31109143/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (916499569/1000000000 : ℝ) ^ p + (992181483/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (916499569/1000000000 : ℝ)) (y := (992181483/1000000000 : ℝ)) (X := (3866640608351/25000000000000 : ℝ)) (Y := (84533453251041/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992181483/1000000000 : ℝ) ^ p + (916499569/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992181483/1000000000 : ℝ)) (y := (916499569/1000000000 : ℝ)) (X := (84533453251041/100000000000000 : ℝ)) (Y := (3866640608351/25000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477170263/250000000 : ℝ)) (τ := (916499569/1000000000 : ℝ)) (σ := (992181483/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (388864307/413840845 : ℝ) ^ p + (815924529/827681690 : ℝ) ^ p := by
    exact cert_lt (x := (388864307/413840845 : ℝ)) (y := (815924529/827681690 : ℝ)) (X := (13190044271807/50000000000000 : ℝ)) (Y := (73619912532127/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (916499569/1000000000 : ℝ)) (n' := (82768169/100000000 : ℝ)) (Ab := (388864307/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (229124893/250000000 : ℝ) ^ p + (496090741/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (229124893/250000000 : ℝ)) (y := (496090741/500000000 : ℝ)) (X := (773328175857/5000000000000 : ℝ)) (Y := (84533451427237/100000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (496090741/500000000 : ℝ) ^ p + (229124893/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496090741/500000000 : ℝ)) (y := (229124893/250000000 : ℝ)) (X := (84533451427237/100000000000000 : ℝ)) (Y := (773328175857/5000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (954340527/500000000 : ℝ)) (τ := (229124893/250000000 : ℝ)) (σ := (496090741/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (777728617/827681693 : ℝ) ^ p + (815924532/827681693 : ℝ) ^ p := by
    exact cert_lt (x := (777728617/827681693 : ℝ)) (y := (815924532/827681693 : ℝ)) (X := (26380088675079/100000000000000 : ℝ)) (Y := (14723982522887/20000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (229124893/250000000 : ℝ)) (n' := (827681693/1000000000 : ℝ)) (Ab := (777728617/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (954340527/500000000 : ℝ)) (τ := (229124893/250000000 : ℝ)) (σ := (496090741/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (229124893/250000000 : ℝ)) (n' := (827681693/1000000000 : ℝ)) (Ab := (777728617/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (954340527/500000000 : ℝ)) (τ := (229124893/250000000 : ℝ)) (σ := (496090741/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (229124893/250000000 : ℝ)) (n' := (827681693/1000000000 : ℝ)) (Ab := (777728617/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (954340527/500000000 : ℝ)) (τ := (229124893/250000000 : ℝ)) (σ := (496090741/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (229124893/250000000 : ℝ)) (n' := (827681693/1000000000 : ℝ)) (Ab := (777728617/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (954340527/500000000 : ℝ)) (τ := (229124893/250000000 : ℝ)) (σ := (496090741/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1643370313/1807460249 : ℝ) ^ p + (1795703088/1807460249 : ℝ) ^ p := by
    exact cert_lt (x := (1643370313/1807460249 : ℝ)) (y := (1795703088/1807460249 : ℝ)) (X := (2607586171387/20000000000000 : ℝ)) (Y := (43481034667009/50000000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (84909096/91733827 : ℝ) ^ p + (90829430/91733827 : ℝ) ^ p := by
    exact cert_lt (x := (84909096/91733827 : ℝ)) (y := (90829430/91733827 : ℝ)) (X := (4777699736481/25000000000000 : ℝ)) (Y := (1011115021893/1250000000000 : ℝ)) 685 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496090741/500000000 : ℝ)) (U := (1192539751/1000000000 : ℝ)) (Ab := (1643370313/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (229124893/250000000 : ℝ)) (σ := (496090741/500000000 : ℝ)) (Ab := (137977281/125000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab012
