import Hlawka21.ContractionRounds

/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 42, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalCutoff21

theorem contract21_slab042 (p : ℝ) (hpa : (357/16 : ℝ) ≤ p) (hpb : p ≤ (715/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (528317496257/24365250000000 : ℝ) (2236741/200000000 : ℝ) (2000000292383/9746100000000 : ℝ) (3033/2500 : ℝ) (969454273/500000000 : ℝ) (121176519/125000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (596454827/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(443/400 : ℝ) ≤ X j i ∧ X j i ≤ -(4499/10000 : ℝ)
      else (153/200 : ℝ) ≤ X j i ∧ X j i ≤ (11839/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (528317496257/24365250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2236741/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (14284677/15625000 : ℝ) ^ p + (496770083/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (14284677/15625000 : ℝ)) (y := (496770083/500000000 : ℝ)) (X := (13480929763709/100000000000000 : ℝ)) (Y := (86519087671251/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (496770083/500000000 : ℝ) ^ p + (14284677/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (496770083/500000000 : ℝ)) (y := (14284677/15625000 : ℝ)) (X := (86519087671251/100000000000000 : ℝ)) (Y := (13480929763709/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (953879747/500000000 : ℝ)) (τ := (14284677/15625000 : ℝ)) (σ := (496770083/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (776173149/823964918 : ℝ) ^ p + (812781213/823964918 : ℝ) ^ p := by
    exact cert_lt (x := (776173149/823964918 : ℝ)) (y := (812781213/823964918 : ℝ)) (X := (26313420659323/100000000000000 : ℝ)) (Y := (36843290132771/50000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (14284677/15625000 : ℝ)) (n' := (411982459/500000000 : ℝ)) (Ab := (776173149/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (460017601/500000000 : ℝ) ^ p + (992473373/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (460017601/500000000 : ℝ)) (y := (992473373/1000000000 : ℝ)) (X := (15533007638699/100000000000000 : ℝ)) (Y := (42233504506893/50000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (992473373/1000000000 : ℝ) ^ p + (460017601/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992473373/1000000000 : ℝ)) (y := (460017601/500000000 : ℝ)) (X := (42233504506893/50000000000000 : ℝ)) (Y := (15533007638699/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (76500343/40000000 : ℝ)) (τ := (460017601/500000000 : ℝ)) (σ := (992473373/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (782450647/830897314 : ℝ) ^ p + (63054893/63915178 : ℝ) ^ p := by
    exact cert_lt (x := (782450647/830897314 : ℝ)) (y := (63054893/63915178 : ℝ)) (X := (26124176034753/100000000000000 : ℝ)) (Y := (73875825382811/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (460017601/500000000 : ℝ)) (n' := (415448657/500000000 : ℝ)) (Ab := (782450647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (18406187/20000000 : ℝ) ^ p + (31013087/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (18406187/20000000 : ℝ)) (y := (31013087/31250000 : ℝ)) (X := (15636754242673/100000000000000 : ℝ)) (Y := (5272703890749/6250000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31013087/31250000 : ℝ) ^ p + (18406187/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (31013087/31250000 : ℝ)) (y := (18406187/20000000 : ℝ)) (X := (5272703890749/6250000000000 : ℝ)) (Y := (15636754242673/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (956364067/500000000 : ℝ)) (τ := (18406187/20000000 : ℝ)) (σ := (31013087/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (391372769/415611517 : ℝ) ^ p + (820039329/831223034 : ℝ) ^ p := by
    exact cert_lt (x := (391372769/415611517 : ℝ)) (y := (820039329/831223034 : ℝ)) (X := (2611535014169/10000000000000 : ℝ)) (Y := (36942325383319/50000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (18406187/20000000 : ℝ)) (n' := (415611517/500000000 : ℝ)) (Ab := (391372769/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (920322131/1000000000 : ℝ) ^ p + (992416229/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (920322131/1000000000 : ℝ)) (y := (992416229/1000000000 : ℝ)) (X := (7820803552897/50000000000000 : ℝ)) (Y := (1687168188809/2000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992416229/1000000000 : ℝ) ^ p + (920322131/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992416229/1000000000 : ℝ)) (y := (920322131/1000000000 : ℝ)) (X := (1687168188809/2000000000000 : ℝ)) (Y := (7820803552897/50000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (47818459/25000000 : ℝ)) (τ := (920322131/1000000000 : ℝ)) (σ := (992416229/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (782759284/831238217 : ℝ) ^ p + (820054512/831238217 : ℝ) ^ p := by
    exact cert_lt (x := (782759284/831238217 : ℝ)) (y := (820054512/831238217 : ℝ)) (X := (26114939011789/100000000000000 : ℝ)) (Y := (18471265501471/25000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (920322131/1000000000 : ℝ)) (n' := (831238217/1000000000 : ℝ)) (Ab := (195689821/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (460161363/500000000 : ℝ) ^ p + (99241611/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (460161363/500000000 : ℝ)) (y := (99241611/100000000 : ℝ)) (X := (3910458264623/25000000000000 : ℝ)) (Y := (8435818342559/10000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (99241611/100000000 : ℝ) ^ p + (460161363/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99241611/100000000 : ℝ)) (y := (460161363/500000000 : ℝ)) (X := (8435818342559/10000000000000 : ℝ)) (Y := (3910458264623/25000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (478184709/250000000 : ℝ)) (τ := (460161363/500000000 : ℝ)) (σ := (99241611/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (195689981/207809731 : ℝ) ^ p + (820055219/831238924 : ℝ) ^ p := by
    exact cert_lt (x := (195689981/207809731 : ℝ)) (y := (820055219/831238924 : ℝ)) (X := (1305745990201/5000000000000 : ℝ)) (Y := (4617817572189/6250000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (460161363/500000000 : ℝ)) (n' := (207809731/250000000 : ℝ)) (Ab := (195689981/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (460161377/500000000 : ℝ) ^ p + (124052013/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (460161377/500000000 : ℝ)) (y := (124052013/125000000 : ℝ)) (X := (15641843691637/100000000000000 : ℝ)) (Y := (42179086014949/50000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (124052013/125000000 : ℝ) ^ p + (460161377/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124052013/125000000 : ℝ)) (y := (460161377/500000000 : ℝ)) (X := (42179086014949/50000000000000 : ℝ)) (Y := (15641843691637/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (956369429/500000000 : ℝ)) (τ := (460161377/500000000 : ℝ)) (σ := (124052013/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (782759954/831238957 : ℝ) ^ p + (820055252/831238957 : ℝ) ^ p := by
    exact cert_lt (x := (782759954/831238957 : ℝ)) (y := (820055252/831238957 : ℝ)) (X := (26114919002371/100000000000000 : ℝ)) (Y := (73885082048831/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (460161377/500000000 : ℝ)) (n' := (831238957/1000000000 : ℝ)) (Ab := (391379977/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (230080689/250000000 : ℝ) ^ p + (124052013/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (230080689/250000000 : ℝ)) (y := (124052013/125000000 : ℝ)) (X := (3910461112787/25000000000000 : ℝ)) (Y := (42179086014949/50000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (124052013/125000000 : ℝ) ^ p + (230080689/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124052013/125000000 : ℝ)) (y := (230080689/250000000 : ℝ)) (X := (42179086014949/50000000000000 : ℝ)) (Y := (3910461112787/25000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (95636943/50000000 : ℝ)) (τ := (230080689/250000000 : ℝ)) (σ := (124052013/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (782759956/831238959 : ℝ) ^ p + (820055254/831238959 : ℝ) ^ p := by
    exact cert_lt (x := (782759956/831238959 : ℝ)) (y := (820055254/831238959 : ℝ)) (X := (13057459544661/50000000000000 : ℝ)) (Y := (73885082103001/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (230080689/250000000 : ℝ)) (n' := (831238959/1000000000 : ℝ)) (Ab := (195689989/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (95636943/50000000 : ℝ)) (τ := (230080689/250000000 : ℝ)) (σ := (124052013/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (230080689/250000000 : ℝ)) (n' := (831238959/1000000000 : ℝ)) (Ab := (195689989/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (95636943/50000000 : ℝ)) (τ := (230080689/250000000 : ℝ)) (σ := (124052013/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (230080689/250000000 : ℝ)) (n' := (831238959/1000000000 : ℝ)) (Ab := (195689989/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (95636943/50000000 : ℝ)) (τ := (230080689/250000000 : ℝ)) (σ := (124052013/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (230080689/250000000 : ℝ)) (n' := (831238959/1000000000 : ℝ)) (Ab := (195689989/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (95636943/50000000 : ℝ)) (τ := (230080689/250000000 : ℝ)) (σ := (124052013/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (824560043/903545173 : ℝ) ^ p + (1795906641/1807090346 : ℝ) ^ p := by
    exact cert_lt (x := (824560043/903545173 : ℝ)) (y := (1795906641/1807090346 : ℝ)) (X := (809499906107/6250000000000 : ℝ)) (Y := (87048001800051/100000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1107405533/1192909654 : ℝ) ^ p + (1181725949/1192909654 : ℝ) ^ p := by
    exact cert_lt (x := (1107405533/1192909654 : ℝ)) (y := (1181725949/1192909654 : ℝ)) (X := (18979185290659/100000000000000 : ℝ)) (Y := (40510407612371/50000000000000 : ℝ)) 715 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (124052013/125000000 : ℝ)) (U := (596454827/500000000 : ℝ)) (Ab := (824560043/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (230080689/250000000 : ℝ)) (σ := (124052013/125000000 : ℝ)) (Ab := (1107405533/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalCutoff21

#print axioms HlawkaSchatten.DiagonalCutoff21.contract21_slab042
