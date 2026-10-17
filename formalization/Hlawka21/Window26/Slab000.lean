import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff26/contractor.json, slab 0, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract26_slab000 (p : ℝ) (hpa : (26 : ℝ) ≤ p) (hpb : p ≤ (417/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (22744613551/1439750000000 : ℝ) (8112217/1000000000 : ℝ) (100000017277/575900000000 : ℝ) (591/500 : ℝ) (973754973/500000000 : ℝ) (12171159/12500000 : ℝ) X N)
    (hn0 : ∀ i, (3/4 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (577673829/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(10789/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5461/10000 : ℝ)
      else (1623/2000 : ℝ) ≤ X j i ∧ X j i ≤ (2293/2000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (22744613551/1439750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (8112217/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (933221087/1000000000 : ℝ) ^ p + (248275217/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (933221087/1000000000 : ℝ)) (y := (248275217/250000000 : ℝ)) (X := (16509053142289/100000000000000 : ℝ)) (Y := (10436370691909/12500000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248275217/250000000 : ℝ) ^ p + (933221087/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248275217/250000000 : ℝ)) (y := (933221087/1000000000 : ℝ)) (X := (10436370691909/12500000000000 : ℝ)) (Y := (16509053142289/100000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (385264391/200000000 : ℝ)) (τ := (933221087/1000000000 : ℝ)) (σ := (248275217/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (813174023/862056233 : ℝ) ^ p + (853944016/862056233 : ℝ) ^ p := by
    exact cert_lt (x := (813174023/862056233 : ℝ)) (y := (853944016/862056233 : ℝ)) (X := (21840415699183/100000000000000 : ℝ)) (Y := (39079792714549/50000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (933221087/1000000000 : ℝ)) (n' := (862056233/1000000000 : ℝ)) (Ab := (813174023/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (936744331/1000000000 : ℝ) ^ p + (992315607/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (936744331/1000000000 : ℝ)) (y := (992315607/1000000000 : ℝ)) (X := (9106347783541/50000000000000 : ℝ)) (Y := (40893660620791/50000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992315607/1000000000 : ℝ) ^ p + (936744331/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992315607/1000000000 : ℝ)) (y := (936744331/1000000000 : ℝ)) (X := (40893660620791/50000000000000 : ℝ)) (Y := (9106347783541/50000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (964529969/500000000 : ℝ)) (τ := (936744331/1000000000 : ℝ)) (σ := (992315607/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (102111012/108266563 : ℝ) ^ p + (858020287/866132504 : ℝ) ^ p := by
    exact cert_lt (x := (102111012/108266563 : ℝ)) (y := (858020287/866132504 : ℝ)) (X := (1359330768447/6250000000000 : ℝ)) (Y := (782507089569/1000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (936744331/1000000000 : ℝ)) (n' := (108266563/125000000 : ℝ)) (Ab := (25527753/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (468428633/500000000 : ℝ) ^ p + (992288917/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468428633/500000000 : ℝ)) (y := (992288917/1000000000 : ℝ)) (X := (9135004343233/50000000000000 : ℝ)) (Y := (81730008070711/100000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (992288917/1000000000 : ℝ) ^ p + (468428633/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992288917/1000000000 : ℝ)) (y := (468428633/500000000 : ℝ)) (X := (81730008070711/100000000000000 : ℝ)) (Y := (9135004343233/50000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1929146183/1000000000 : ℝ)) (τ := (468428633/500000000 : ℝ)) (σ := (992288917/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (9390884/9957045 : ℝ) ^ p + (858150698/866262915 : ℝ) ^ p := by
    exact cert_lt (x := (9390884/9957045 : ℝ)) (y := (858150698/866262915 : ℝ)) (X := (2174638934087/10000000000000 : ℝ)) (Y := (4890850735429/6250000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (468428633/500000000 : ℝ)) (n' := (173252583/200000000 : ℝ)) (Ab := (204251727/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (14638451/15625000 : ℝ) ^ p + (198457613/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (14638451/15625000 : ℝ)) (y := (198457613/200000000 : ℝ)) (X := (913591873743/5000000000000 : ℝ)) (Y := (2554005598501/3125000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (198457613/200000000 : ℝ) ^ p + (14638451/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (198457613/200000000 : ℝ)) (y := (14638451/15625000 : ℝ)) (X := (2554005598501/3125000000000 : ℝ)) (Y := (913591873743/5000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1929148929/1000000000 : ℝ)) (τ := (14638451/15625000 : ℝ)) (σ := (198457613/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (817010692/866267069 : ℝ) ^ p + (858154852/866267069 : ℝ) ^ p := by
    exact cert_lt (x := (817010692/866267069 : ℝ)) (y := (858154852/866267069 : ℝ)) (X := (869851860869/4000000000000 : ℝ)) (Y := (39126852108909/50000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (14638451/15625000 : ℝ)) (n' := (866267069/1000000000 : ℝ)) (Ab := (204252673/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (468430489/500000000 : ℝ) ^ p + (496144019/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (468430489/500000000 : ℝ)) (y := (496144019/500000000 : ℝ)) (X := (456797385539/2500000000000 : ℝ)) (Y := (16345624238797/20000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496144019/500000000 : ℝ) ^ p + (468430489/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496144019/500000000 : ℝ)) (y := (468430489/500000000 : ℝ)) (X := (16345624238797/20000000000000 : ℝ)) (Y := (456797385539/2500000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (241143627/125000000 : ℝ)) (τ := (468430489/500000000 : ℝ)) (σ := (496144019/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (817010813/866267201 : ℝ) ^ p + (858154984/866267201 : ℝ) ^ p := by
    exact cert_lt (x := (817010813/866267201 : ℝ)) (y := (858154984/866267201 : ℝ)) (X := (21746294097639/100000000000000 : ℝ)) (Y := (39126853577791/50000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (468430489/500000000 : ℝ)) (n' := (866267201/1000000000 : ℝ)) (Ab := (817010813/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (468430491/500000000 : ℝ) ^ p + (992288037/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (468430491/500000000 : ℝ)) (y := (992288037/1000000000 : ℝ)) (X := (18271897454781/100000000000000 : ℝ)) (Y := (81728119047391/100000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992288037/1000000000 : ℝ) ^ p + (468430491/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992288037/1000000000 : ℝ)) (y := (468430491/500000000 : ℝ)) (X := (81728119047391/100000000000000 : ℝ)) (Y := (18271897454781/100000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1929149019/1000000000 : ℝ)) (τ := (468430491/500000000 : ℝ)) (σ := (992288037/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (116715831/123752458 : ℝ) ^ p + (858154989/866267206 : ℝ) ^ p := by
    exact cert_lt (x := (116715831/123752458 : ℝ)) (y := (858154989/866267206 : ℝ)) (X := (10873146800579/50000000000000 : ℝ)) (Y := (78253707266861/100000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (468430491/500000000 : ℝ)) (n' := (433133603/500000000 : ℝ)) (Ab := (817010817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1929149019/1000000000 : ℝ)) (τ := (468430491/500000000 : ℝ)) (σ := (992288037/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (468430491/500000000 : ℝ)) (n' := (433133603/500000000 : ℝ)) (Ab := (817010817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1929149019/1000000000 : ℝ)) (τ := (468430491/500000000 : ℝ)) (σ := (992288037/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (468430491/500000000 : ℝ)) (n' := (433133603/500000000 : ℝ)) (Ab := (817010817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1929149019/1000000000 : ℝ)) (τ := (468430491/500000000 : ℝ)) (σ := (992288037/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (468430491/500000000 : ℝ)) (n' := (433133603/500000000 : ℝ)) (Ab := (817010817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1929149019/1000000000 : ℝ)) (τ := (468430491/500000000 : ℝ)) (σ := (992288037/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (468430491/500000000 : ℝ)) (n' := (433133603/500000000 : ℝ)) (Ab := (817010817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1929149019/1000000000 : ℝ)) (τ := (468430491/500000000 : ℝ)) (σ := (992288037/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1693975319/1844652342 : ℝ) ^ p + (1836540125/1844652342 : ℝ) ^ p := by
    exact cert_lt (x := (1693975319/1844652342 : ℝ)) (y := (1836540125/1844652342 : ℝ)) (X := (2712897373583/25000000000000 : ℝ)) (Y := (44574205380991/50000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (359620051/385115886 : ℝ) ^ p + (1147235441/1155347658 : ℝ) ^ p := by
    exact cert_lt (x := (359620051/385115886 : ℝ)) (y := (1147235441/1155347658 : ℝ)) (X := (16776635188723/100000000000000 : ℝ)) (Y := (4161168278831/5000000000000 : ℝ)) 417 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992288037/1000000000 : ℝ)) (U := (577673829/500000000 : ℝ)) (Ab := (1693975319/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (468430491/500000000 : ℝ)) (σ := (992288037/1000000000 : ℝ)) (Ab := (1078860153/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract26_slab000
