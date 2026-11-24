import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaTerm
import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaDecayIteration
import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaStepOne
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFlatnessMu
import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaSupRate

/-!
# Lemma 5.9 of Armstrong and Dario in every dimension

With `r = 3^{-1/4}`, there are `C` and `N` such that for `n ≥ N`

`D_n ≤ C rⁿ + C ∑_{l ≤ n} 3^{l - n} τ_l`

(`exists_cubeOmegaD_le_decay`). This is display (5.25) of Lemma 5.9 of Armstrong and Dario, in
the form `D_n ≤ C 3^{-n/4} + C ∑_{l ≤ n} 3^{l-n} τ_l` consumed by Steps 2 and 3 of the proof of
Lemma 5.10 (`exists_cubeOmegaD_le_pow_of_decay`). The printed statement has the exponent `-n s` for
some `s(d, 𝔭) > 0`; the proof here gives `s = 1/4`.

The term `i` of `D_n`, `E[ν(□_n, eᵢ)] + E[-μ(□_n, ā_n eᵢ)] - (ā_n eᵢ)ᵢ`, is the expectation of
`cubeOmegaX` at `p = eᵢ`, `q = ā_n eᵢ`. Its bound (`integral_cubeOmegaX_le`, with the cap scale
`⌊n / 4d⌋`) is made of

* the deterministic part (`omegaConst_le`), at most `C 3^{-n/4}`;
* the subadditivity majorant of the energy of the differences of the maximizers of `ν`
  (`exists_integral_nuDefectMajorant_le`), at most `C (τ_n + 3^{-n/2})` by the bound of the
  increments of `ν` at `ā⁻¹ (σ eᵢ) = eᵢ`;
* the flatness errors (displays (5.32) and (5.33), both at the slope `eᵢ`), at most
  `C (3^{-n/4} + ∑_{k ≤ n} 3^{k-n} τ_k)` after the Caccioppoli factor `≤ C 9^{-n}`;
* the bad event (`exists_integral_omegaBad_le`), at most `C 3^{-n}`;
* the energy of the differences of the minimizers of `μ` (Lemma 5.4,
  `exists_lintegral_cubeMuDefect_le_tau`), at most `C (τ_n + 3^{-n/4})`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {p : unitInterval}

/-- The constant of the deterministic part. -/
noncomputable def omegaRateConst (d : ℕ) : ℝ :=
  1 + (1 + 2 * d + 2 * 3 ^ d * √(4 * d * d * Real.exp 1)) +
    96 * coarseningConst d ^ 2 * d * 3 ^ d * (3 ^ d + 4 * (d * d * coarseGradConstant d ^ 2))

theorem latticeVolume_succ_eq (n : ℕ) :
    (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume = 3 ^ d * (⟨n, 0⟩ : TriadicCube d).latticeVolume := by
  change ((3 : ℝ) ^ (n + 1)) ^ d = 3 ^ d * ((3 : ℝ) ^ n) ^ d
  rw [pow_succ, mul_pow, mul_comm]

/-- `K_n |□_{n+1}| ≤ 48 d 3^d / 9ⁿ`. -/
theorem caccioppoliFactor_mul_le {n : ℕ} (hn : 1 ≤ n) :
    caccioppoliFactor d n * (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume ≤
      48 * d * 3 ^ d / ((3 : ℝ) ^ n) ^ 2 := by
  unfold caccioppoliFactor
  rw [latticeVolume_succ_eq]
  set L : ℝ := (3 : ℝ) ^ n with hL
  have hL3 : 3 ≤ L := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hn
    rwa [pow_one] at this
  have hV := (⟨n, 0⟩ : TriadicCube d).latticeVolume_pos
  have hL1 : 0 < L - 1 := by linarith
  have e : 12 * (d : ℝ) / ((L - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube d).latticeVolume) *
      (3 ^ d * (⟨n, 0⟩ : TriadicCube d).latticeVolume) = 12 * d * 3 ^ d / (L - 1) ^ 2 := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : L ^ 2 ≤ 4 * (L - 1) ^ 2 := by nlinarith
  have : (0 : ℝ) ≤ 12 * d * 3 ^ d := by positivity
  nlinarith

/-- The Caccioppoli term of the deterministic part. -/
theorem caccioppoli_term_le {K Uv w L P Q2 Kμ cc : ℝ} {d : ℕ}
    (hKU : K * Uv ≤ 48 * d * 3 ^ d / L ^ 2) (hL : 0 < L) (hw1 : 1 ≤ w) (hw4 : w ^ (4 * d) ≤ L)
    (hQ2 : 0 ≤ Q2) (hKμ : 0 ≤ Kμ) :
    K * 2 * (cc ^ 2 * w ^ (2 * d) * (3 ^ d * Uv * P ^ 2 + 4 * Kμ * Q2 * (Uv * w ^ (2 * d - 1)))) ≤
      96 * cc ^ 2 * d * 3 ^ d * (3 ^ d + 4 * Kμ) * (P ^ 2 + Q2) * (1 / L) := by
  have hwa : w ^ (2 * d) ≤ w ^ (4 * d) := pow_le_pow_right₀ hw1 (by omega)
  have hwb : w ^ (2 * d) * w ^ (2 * d - 1) ≤ w ^ (4 * d) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hw1 (by omega)
  have e : K * 2 * (cc ^ 2 * w ^ (2 * d) *
      (3 ^ d * Uv * P ^ 2 + 4 * Kμ * Q2 * (Uv * w ^ (2 * d - 1)))) =
      2 * cc ^ 2 * (K * Uv) *
        (3 ^ d * P ^ 2 * w ^ (2 * d) + 4 * Kμ * Q2 * (w ^ (2 * d) * w ^ (2 * d - 1))) := by
    ring
  have hin : 3 ^ d * P ^ 2 * w ^ (2 * d) + 4 * Kμ * Q2 * (w ^ (2 * d) * w ^ (2 * d - 1)) ≤
      (3 ^ d + 4 * Kμ) * (P ^ 2 + Q2) * L := by
    have h1 : 3 ^ d * P ^ 2 * w ^ (2 * d) ≤ 3 ^ d * P ^ 2 * L :=
      mul_le_mul_of_nonneg_left (hwa.trans hw4) (by positivity)
    have h2 : 4 * Kμ * Q2 * (w ^ (2 * d) * w ^ (2 * d - 1)) ≤ 4 * Kμ * Q2 * L :=
      mul_le_mul_of_nonneg_left (hwb.trans hw4) (by positivity)
    have h3 : 0 ≤ 3 ^ d * Q2 * L := by positivity
    have h4 : 0 ≤ 4 * Kμ * P ^ 2 * L := by positivity
    have e2 : (3 ^ d + 4 * Kμ) * (P ^ 2 + Q2) * L =
        3 ^ d * P ^ 2 * L + 4 * Kμ * Q2 * L + (3 ^ d * Q2 * L + 4 * Kμ * P ^ 2 * L) := by ring
    rw [e2]
    linarith
  rw [e]
  have hin0 : 0 ≤ 3 ^ d * P ^ 2 * w ^ (2 * d) + 4 * Kμ * Q2 * (w ^ (2 * d) * w ^ (2 * d - 1)) := by
    positivity
  calc 2 * cc ^ 2 * (K * Uv) *
        (3 ^ d * P ^ 2 * w ^ (2 * d) + 4 * Kμ * Q2 * (w ^ (2 * d) * w ^ (2 * d - 1)))
      ≤ 2 * cc ^ 2 * (48 * d * 3 ^ d / L ^ 2) * ((3 ^ d + 4 * Kμ) * (P ^ 2 + Q2) * L) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hKU (by positivity)) hin hin0 ?_
        positivity
    _ = 96 * cc ^ 2 * d * 3 ^ d * (3 ^ d + 4 * Kμ) * (P ^ 2 + Q2) * (1 / L) := by
        field_simp
        ring

theorem three_terms_le {A QP S r C1 C2 : ℝ} (hA : 0 ≤ A) (hQP : 0 ≤ QP) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) :
    A * r + C1 * QP * r + C2 * S * r ≤ (1 + C1 + C2) * (QP + A + S) * r := by
  have key : (1 + C1 + C2) * (QP + A + S) * r - (A * r + C1 * QP * r + C2 * S * r) =
      r * (QP + S + C1 * A + C1 * S + C2 * QP + C2 * A) := by ring
  have : 0 ≤ r * (QP + S + C1 * A + C1 * S + C2 * QP + C2 * A) := by positivity
  linarith

/-- **The deterministic part of the bound of a term of `D_n`**, with the cap scale `⌊n / 4d⌋`. -/
theorem omegaConst_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (p' q : Fin d → ℝ) :
    omegaConst d n (omegaCap d n) p' q ≤ omegaRateConst d *
      ((∑ i, |q i|) * (∑ i, |p' i|) + |∑ i, q i * p' i| + (∑ i, |p' i|) ^ 2 + ∑ i, q i ^ 2) *
        (1 / √(√((3 : ℝ) ^ n))) := by
  set ℓ := omegaCap d n with hℓ
  set L : ℝ := (3 : ℝ) ^ n with hL
  have hL3 : 3 ≤ L := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hn
    rwa [pow_one] at this
  have hL0 : 0 < L := by linarith
  set s : ℝ := √(√L) with hs
  have hsq : √L ^ 2 = L := Real.sq_sqrt hL0.le
  have hs2 : s ^ 2 = √L := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = L := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, hsq]
  have hs0 : 0 < s := Real.sqrt_pos.2 (Real.sqrt_pos.2 hL0)
  have hs1 : 1 ≤ s := by
    by_contra h
    push Not at h
    have : s ^ 4 < 1 := pow_lt_one₀ hs0.le h (by norm_num)
    linarith
  set w : ℝ := (3 : ℝ) ^ ℓ with hw
  have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
  have hw4 : w ^ (4 * d) ≤ L := by
    rw [hw, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by rw [mul_comm]; exact four_mul_omegaCap_le d n)
  have hwd : w ^ d ≤ s := by
    have h : (w ^ d) ^ 4 ≤ s ^ 4 := by
      rw [← pow_mul, hs4, show d * 4 = 4 * d by ring]
      exact hw4
    exact (pow_le_pow_iff_left₀ (by positivity) hs0.le (by norm_num)).1 h
  set r : ℝ := 1 / s with hr
  have hr0 : 0 ≤ r := by positivity
  have hsr : s * r = 1 := by rw [hr]; field_simp
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hs0]; exact hs1
  have hLr : 1 / L = r ^ 4 := by rw [← hs4, hr, one_div_pow]
  have hsLr : 1 / √L = r ^ 2 := by rw [← hs2, hr, one_div_pow]
  have hr4 : r ^ 4 ≤ r := pow_le_of_le_one hr0 hr1 (by norm_num)
  set P : ℝ := ∑ i, |p' i| with hP
  set Q : ℝ := ∑ i, |q i| with hQ
  set Q2 : ℝ := ∑ i, q i ^ 2 with hQ2
  set A : ℝ := |∑ i, q i * p' i| with hA
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hQ20 : 0 ≤ Q2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA0 : 0 ≤ A := abs_nonneg _
  set Ccap : ℝ := 1 + 2 * d + 2 * 3 ^ d * √(4 * d * d * Real.exp 1) with hCcap
  have hCcap0 : 0 ≤ Ccap := by positivity
  set Kμ : ℝ := d * d * coarseGradConstant d ^ 2 with hKμ
  have hKμ0 : 0 ≤ Kμ := by positivity
  set cc : ℝ := coarseningConst d with hcc
  set C3 : ℝ := 96 * cc ^ 2 * d * 3 ^ d * (3 ^ d + 4 * Kμ) with hC3
  have hC30 : 0 ≤ C3 := by positivity
  -- the first term
  have hT1 : A / L ≤ A * r := by
    rw [div_eq_mul_one_div, hLr]
    exact mul_le_mul_of_nonneg_left hr4 hA0
  -- the second term
  have hT2 : Q * P * comparisonCap d ℓ * (1 / √L) ≤ Ccap * (Q * P) * r := by
    have h1 := comparisonCap_le hd ℓ
    rw [← hw, ← hCcap] at h1
    have h2 : comparisonCap d ℓ * (1 / √L) ≤ Ccap * r := by
      rw [hsLr]
      calc comparisonCap d ℓ * r ^ 2 ≤ Ccap * w ^ d * r ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ Ccap * s * r ^ 2 := by gcongr
        _ = Ccap * r * (s * r) := by ring
        _ = Ccap * r := by rw [hsr, mul_one]
    calc Q * P * comparisonCap d ℓ * (1 / √L) = Q * P * (comparisonCap d ℓ * (1 / √L)) := by ring
      _ ≤ Q * P * (Ccap * r) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Ccap * (Q * P) * r := by ring
  -- the third term
  have hKU := caccioppoliFactor_mul_le (d := d) hn
  rw [← hL] at hKU
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  have hT3 := caccioppoli_term_le (cc := cc) (P := P) hKU hL0 hw1 hw4 hQ20 hKμ0
  rw [← hC3] at hT3
  have hT3' : C3 * (P ^ 2 + Q2) * (1 / L) ≤ C3 * (P ^ 2 + Q2) * r := by
    rw [hLr]
    exact mul_le_mul_of_nonneg_left hr4 (by positivity)
  -- assembly
  unfold omegaConst
  rw [← hL, ← hP, ← hQ, ← hQ2, ← hA, ← hw, ← hU, ← hKμ, ← hcc]
  have hRC : omegaRateConst d = 1 + Ccap + C3 := by
    rw [omegaRateConst, hC3, hCcap, hKμ, hcc]
  rw [hRC]
  have hfin := three_terms_le hA0 (mul_nonneg hQ0 hP0) (add_nonneg (sq_nonneg P) hQ20) hr0
    hCcap0 hC30
  have e : Q * P + A + P ^ 2 + Q2 = Q * P + A + (P ^ 2 + Q2) := by ring
  rw [e]
  linarith

/-- `3⁻ⁿ ∑_{k ≤ n} 3ᵏ τ_k = ∑_{k ≤ n} 3^{k-n} τ_k`. -/
theorem inv_three_pow_mul_sum_three_pow_eq (n : ℕ) (τ : ℕ → ℝ) :
    ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * τ k =
      ∑ k ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - k) * τ k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have h3 : (3 : ℝ) ^ n = 3 ^ (n - k) * 3 ^ k := by rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [h3, one_div, inv_pow]
  field_simp

theorem sum_abs_single_eq (i : Fin d) : ∑ j, |(Pi.single i 1 : Fin d → ℝ) j| = 1 := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem sum_sq_single_eq (i : Fin d) : ∑ j, (Pi.single i 1 : Fin d → ℝ) j ^ 2 = 1 := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem sum_mul_single_eq (i : Fin d) (x : Fin d → ℝ) :
    ∑ j, x j * (Pi.single i 1 : Fin d → ℝ) j = x i := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- `τ_n ≤ ∑_{l ≤ n} 3^{l-n} τ_l`. -/
theorem cubeTau_le_sum (p : unitInterval) (n : ℕ) :
    cubeTau (d := d) p n ≤
      ∑ l ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - l) * cubeTau (d := d) p l := by
  have h := Finset.single_le_sum (f := fun l => (1 / 3 : ℝ) ^ (n - l) * cubeTau (d := d) p l)
    (fun l _ => mul_nonneg (by positivity) (cubeTau_nonneg p l)) (Finset.self_mem_range_succ n)
  simpa using h

/-- **The term `i` of `D_n`** (proof of Lemma 5.9, every dimension `d ≥ 2`). -/
theorem exists_cubeOmegaD_term_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ i : Fin d,
      cubeNuMean p n (Pi.single i 1) + cubeMuMean p n (cubeAhomFinite p n *ᵥ Pi.single i 1) -
          (cubeAhomFinite p n *ᵥ Pi.single i 1) i ≤
        K₁ * (1 / √(√((3 : ℝ) ^ n))) +
          K₂ * ∑ l ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - l) * cubeTau (d := d) p l := by
  have hd0 : 0 < d := by omega
  obtain ⟨c₀, C₀, hc₀, -, N₁, hN₁⟩ := exists_cubeAhomInvFinite_bounds hd hpc
  obtain ⟨N₂, hN₂⟩ := exists_cubeAhomInvFinite_mul_cubeAhomFinite hd hpc
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  obtain ⟨Cv, hCv, hFv⟩ := exists_lintegral_cubeNuFlatness_le hd hpc
  obtain ⟨Cu, hCu, hFu⟩ := exists_lintegral_cubeMuFlatness_le hd hpc
  obtain ⟨CD, hCD, hDμ⟩ := exists_lintegral_cubeMuDefect_le_tau hd hpc
  obtain ⟨CM, hCM, hM⟩ := exists_integral_nuDefectMajorant_le hd hpc
  obtain ⟨C2, hC2, hinc⟩ := exists_cubeNuIncrement_le hd hpc
  obtain ⟨CBad, hCBad, hBad⟩ := exists_integral_omegaBad_le hd hpc
  set Rx : ℝ := 1 / (4 * c₀ ^ 2) with hRx
  have hRx0 : 0 ≤ Rx := by positivity
  set R : ℝ := √(d * Rx) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  set W₀ : ℝ := R + R + 1 + Rx with hW₀
  set Cf : ℝ := 192 * d * 3 ^ d * (Cv * σ ^ 2 + Cu * Rx) with hCf
  have hCf0 : 0 ≤ Cf := mul_nonneg (by positivity)
    (add_nonneg (mul_nonneg hCv (sq_nonneg σ)) (mul_nonneg hCu hRx0))
  set K₁ : ℝ := omegaRateConst d * W₀ + 3 * 3 ^ d * (d * σ ^ 2 * C2 + CM) + Cf +
    CBad * (2 + R + Rx) + 3 * 3 ^ d * CD * Rx with hK₁
  set K₂ : ℝ := 3 * 3 ^ d * (d * σ ^ 2) + Cf + 3 * 3 ^ d * CD * Rx with hK₂
  have hRC0 : 0 ≤ omegaRateConst d := by
    unfold omegaRateConst
    have := coarseningConst_nonneg d
    positivity
  have hW₀0 : 0 ≤ W₀ := by rw [hW₀]; linarith
  have hk3 : 0 ≤ 3 * 3 ^ d * CD * Rx := mul_nonneg (mul_nonneg (by positivity) hCD) hRx0
  have hK₁0 : 0 ≤ K₁ := by
    have t1 := mul_nonneg hRC0 hW₀0
    have t2 : 0 ≤ 3 * 3 ^ d * ((d : ℝ) * σ ^ 2 * C2 + CM) :=
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by positivity) hC2) hCM)
    have t4 : 0 ≤ CBad * (2 + R + Rx) := mul_nonneg hCBad (by linarith)
    rw [hK₁]
    linarith
  have hK₂0 : 0 ≤ K₂ := by
    have t1 : 0 ≤ 3 * 3 ^ d * ((d : ℝ) * σ ^ 2) := by positivity
    rw [hK₂]
    linarith
  refine ⟨K₁, K₂, hK₁0, hK₂0, max (max N₁ N₂) 1, fun n hn i => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  obtain ⟨hinv, -⟩ := hN₂ n (le_of_max_le_right (le_of_max_le_left hn))
  have hb := hN₁ n (le_of_max_le_left (le_of_max_le_left hn))
  set e : Fin d → ℝ := Pi.single i 1 with he
  set x : Fin d → ℝ := cubeAhomFinite p n *ᵥ e with hx
  set V : TriadicCube d := ⟨n, 0⟩ with hV
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  have hVv := V.latticeVolume_pos
  have hUV : U.latticeVolume = 3 ^ d * V.latticeVolume := latticeVolume_succ_eq n
  set r : ℝ := 1 / √(√((3 : ℝ) ^ n)) with hr
  have hr0 : 0 ≤ r := by positivity
  set Sτ : ℝ := ∑ l ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - l) * cubeTau (d := d) p l
    with hSτ
  have hτn : cubeTau (d := d) p n ≤ Sτ := cubeTau_le_sum p n
  have hτ0 : 0 ≤ cubeTau (d := d) p n := cubeTau_nonneg p n
  -- the slopes
  have hsq : ∑ j, x j ^ 2 ≤ Rx := sum_sq_mulVec_single_le_of_le hc₀ (fun q => (hb q).1) hinv i
  have hx1 : ∑ j, |x j| ≤ R := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have h1 := sq_sum_abs_le_card_mul x
    have h2 := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) d)
    linarith
  have hxi : |x i| ≤ R :=
    (Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)).trans hx1
  have he1 : ∑ j, |e j| = 1 := sum_abs_single_eq i
  have hxe : ∑ j, x j * e j = x i := sum_mul_single_eq i x
  have hsu : cubeAhomInvFinite p n *ᵥ x = e := by
    rw [hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  set q' : Fin d → ℝ := σ • e with hq'
  have hsv : (cubeAhom p)⁻¹ *ᵥ q' = e := by
    rw [hA, inv_smul_one_eq hσ.ne', Matrix.smul_mulVec, Matrix.one_mulVec, hq', smul_smul,
      inv_mul_cancel₀ hσ.ne', one_smul]
  have hq'2 : ∑ j, q' j ^ 2 = σ ^ 2 := by
    simp only [hq', Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, sum_sq_single_eq, mul_one]
  -- the integrated bound
  have hFv' := hFv n q'
  rw [hsv, hq'2] at hFv'
  have hFu' := hFu n x
  rw [hsu] at hFu'
  have hD := hDμ n (n + 1) x (Nat.le_succ n)
  set Z : ℝ := (3 : ℝ) ^ (-(n : ℝ) / 4) +
    ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * cubeTau (d := d) p k with hZ
  have hZ' : Z = r + Sτ := by
    rw [hZ, three_rpow_neg_div_four_eq, inv_three_pow_mul_sum_three_pow_eq]
  have hZ0 : 0 ≤ Z := by
    rw [hZ']
    exact add_nonneg hr0 (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity)
      (cubeTau_nonneg p l))
  have hx20 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set bD : ℝ := U.latticeVolume * (CD * (∑ j, x j ^ 2) *
    (∑ k ∈ Finset.Ico n (n + 1), cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)))) with hbD
  have hIco : ∑ k ∈ Finset.Ico n (n + 1), cubeTau (d := d) p k = cubeTau (d := d) p n := by
    rw [Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, zero_add]
  have hbD0 : 0 ≤ bD := by
    rw [hbD, hIco]
    exact mul_nonneg U.latticeVolume_pos.le (mul_nonneg (mul_nonneg hCD hx20)
      (add_nonneg hτ0 (by positivity)))
  have h90 : (0 : ℝ) ≤ 9 ^ n := by positivity
  have hbv0 : 0 ≤ Cv * σ ^ 2 * (9 : ℝ) ^ n * Z :=
    mul_nonneg (mul_nonneg (mul_nonneg hCv (sq_nonneg σ)) h90) hZ0
  have hbu0 : 0 ≤ Cu * (∑ j, x j ^ 2) * (9 : ℝ) ^ n * Z :=
    mul_nonneg (mul_nonneg (mul_nonneg hCu hx20) h90) hZ0
  have main := integral_cubeOmegaX_le hd hpc (ℓ := omegaCap d n) hn1 (omegaCap_le d n) e x e
    hbv0 hbu0 hbD0 hFv' hFu' hD
  have hX : ∫ ω, cubeOmegaX ω n e x ∂(latticeBondLaw d p) =
      cubeNuMean p n e + cubeMuMean p n x - x i := by
    have hI1 : Integrable (fun ω => cubeNu ω ⟨n, 0⟩ e +
        (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
          -cubeMu ω ⟨n, 0⟩ x else 0)) (latticeBondLaw d p) :=
      (integrable_cubeNu p _ e).add (integrable_neg_cubeMu_indicator hd hpc _ x)
    have e1 : ∫ ω, cubeOmegaX ω n e x ∂(latticeBondLaw d p) = ∫ ω, (cubeNu ω ⟨n, 0⟩ e +
        (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
          -cubeMu ω ⟨n, 0⟩ x else 0)) ∂(latticeBondLaw d p) - ∫ _ω, (∑ j, x j * e j) ∂(latticeBondLaw d p) :=
      integral_sub hI1 (integrable_const _)
    have e2 : ∫ ω, (cubeNu ω ⟨n, 0⟩ e +
        (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
          -cubeMu ω ⟨n, 0⟩ x else 0)) ∂(latticeBondLaw d p) = ∫ ω, cubeNu ω ⟨n, 0⟩ e ∂(latticeBondLaw d p) +
        ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
          -cubeMu ω ⟨n, 0⟩ x else 0) ∂(latticeBondLaw d p) :=
      integral_add (integrable_cubeNu p _ e) (integrable_neg_cubeMu_indicator hd hpc _ x)
    rw [e1, e2, integral_neg_cubeMu_indicator_eq_cubeMuMean hd0 p n x, integral_const, hxe]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rfl
  rw [hX] at main
  -- the deterministic part
  have h1 : omegaConst d n (omegaCap d n) e x ≤ omegaRateConst d * W₀ * r := by
    refine (omegaConst_le hd0 hn1 e x).trans ?_
    rw [he1, hxe, one_pow, mul_one]
    have hW : ∑ j, |x j| + |x i| + 1 + ∑ j, x j ^ 2 ≤ W₀ := by
      rw [hW₀]
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hRC0) hr0
  -- the majorant of the energy of the differences of the maximizers of `ν`
  have h2 : 3 * (∫ ω, nuDefectMajorant ω n e ∂(latticeBondLaw d p)) / V.latticeVolume ≤
      3 * 3 ^ d * (d * σ ^ 2) * cubeTau (d := d) p n + 3 * 3 ^ d * (d * σ ^ 2 * C2 + CM) * r := by
    have hMn : ∫ ω, nuDefectMajorant ω n e ∂(latticeBondLaw d p) ≤ U.latticeVolume *
        (cubeNuMean p n e - cubeNuMean p (n + 1) e + CM / √3 ^ n) := by
      have h := hM n e
      rw [he1, one_pow, mul_one] at h
      exact h
    have hi := hinc n q'
    rw [hsv, hq'2] at hi
    have hντ : cubeNuTau (d := d) p n ≤ cubeTau (d := d) p n := by
      unfold cubeTau
      linarith [cubeMuTau_nonneg (d := d) p n]
    have hs3 : 1 / √3 ^ n ≤ r := one_div_sqrt_three_pow_le n
    have hinc' : cubeNuMean p n e - cubeNuMean p (n + 1) e ≤
        d * σ ^ 2 * cubeTau (d := d) p n + d * σ ^ 2 * C2 * r := by
      have hi' : cubeNuMean p n e - cubeNuMean p (n + 1) e ≤
          d * σ ^ 2 * (cubeNuTau (d := d) p n + C2 / √3 ^ n) := hi
      have hC2r : C2 / √3 ^ n ≤ C2 * r := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hs3 hC2
      have hds : 0 ≤ (d : ℝ) * σ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left (add_le_add hντ hC2r) hds
      linarith
    have hCMr : CM / √3 ^ n ≤ CM * r := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hs3 hCM
    rw [div_le_iff₀ hVv]
    calc 3 * ∫ ω, nuDefectMajorant ω n e ∂(latticeBondLaw d p)
        ≤ 3 * (U.latticeVolume * (cubeNuMean p n e - cubeNuMean p (n + 1) e + CM / √3 ^ n)) := by
          linarith
      _ ≤ 3 * (U.latticeVolume * (d * σ ^ 2 * cubeTau (d := d) p n + d * σ ^ 2 * C2 * r +
            CM * r)) := by
          have hin : cubeNuMean p n e - cubeNuMean p (n + 1) e + CM / √3 ^ n ≤
              d * σ ^ 2 * cubeTau (d := d) p n + d * σ ^ 2 * C2 * r + CM * r := by linarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin U.latticeVolume_pos.le)
            (by norm_num)
      _ = (3 * 3 ^ d * (d * σ ^ 2) * cubeTau (d := d) p n +
            3 * 3 ^ d * (d * σ ^ 2 * C2 + CM) * r) * V.latticeVolume := by
          rw [hUV]
          ring
  -- the flatness errors
  have h3 : caccioppoliFactor d n * (4 * U.latticeVolume *
      (Cv * σ ^ 2 * (9 : ℝ) ^ n * Z + Cu * (∑ j, x j ^ 2) * (9 : ℝ) ^ n * Z)) ≤ Cf * (r + Sτ) := by
    have hKU := caccioppoliFactor_mul_le (d := d) hn1
    have h9 : ((3 : ℝ) ^ n) ^ 2 = 9 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h9] at hKU
    have h90 : (0 : ℝ) < 9 ^ n := by positivity
    have e : caccioppoliFactor d n * (4 * U.latticeVolume *
        (Cv * σ ^ 2 * (9 : ℝ) ^ n * Z + Cu * (∑ j, x j ^ 2) * (9 : ℝ) ^ n * Z)) =
        4 * (caccioppoliFactor d n * U.latticeVolume) * (9 : ℝ) ^ n *
          (Cv * σ ^ 2 + Cu * ∑ j, x j ^ 2) * Z := by ring
    rw [e, ← hZ']
    have hin : Cv * σ ^ 2 + Cu * ∑ j, x j ^ 2 ≤ Cv * σ ^ 2 + Cu * Rx := by
      have := mul_le_mul_of_nonneg_left hsq hCu
      linarith
    have hin0 : 0 ≤ Cv * σ ^ 2 + Cu * ∑ j, x j ^ 2 :=
      add_nonneg (mul_nonneg hCv (sq_nonneg σ)) (mul_nonneg hCu hx20)
    have hc0 : (0 : ℝ) ≤ 4 * (48 * d * 3 ^ d / 9 ^ n) * (9 : ℝ) ^ n := by positivity
    calc 4 * (caccioppoliFactor d n * U.latticeVolume) * (9 : ℝ) ^ n *
          (Cv * σ ^ 2 + Cu * ∑ j, x j ^ 2) * Z
        ≤ 4 * (48 * d * 3 ^ d / 9 ^ n) * (9 : ℝ) ^ n * (Cv * σ ^ 2 + Cu * Rx) * Z := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKU (by norm_num)) h90.le) hin hin0 hc0) hZ0
      _ = Cf * Z := by
          rw [hCf]
          field_simp
          ring
  -- the bad event
  have h4 : ∫ ω, (toMeasurable (latticeBondLaw d p) {ω : Configuration d |
        ¬ PartitionSizeLe ω ⟨n + 1, 0⟩ (omegaCap d n)}).indicator
      (fun ω => cubeNu ω ⟨n, 0⟩ e +
        (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
          -cubeMu ω ⟨n, 0⟩ x else 0) + |∑ j, x j * e j|) ω ∂(latticeBondLaw d p) ≤ CBad * (2 + R + Rx) * r := by
    refine (hBad n e x).trans ?_
    rw [he1, hxe, one_pow]
    have hw : 1 + 1 + |x i| + ∑ j, x j ^ 2 ≤ 2 + R + Rx := by linarith
    have h3n : 1 / (3 : ℝ) ^ n ≤ r := by
      rw [hr]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h1 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
      have a : √((3 : ℝ) ^ n) ≤ 3 ^ n :=
        Real.sqrt_le_iff.2 ⟨by positivity, le_self_pow₀ h1 two_ne_zero⟩
      exact (Real.sqrt_le_sqrt a).trans a
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw hCBad) h3n (by positivity)
      (mul_nonneg hCBad (by linarith))
  -- the energy of the differences of the minimizers of `μ`
  have h5 : 3 * bD / V.latticeVolume ≤ 3 * 3 ^ d * CD * Rx * (cubeTau (d := d) p n + r) := by
    rw [hbD, hIco, ← hr, hUV, div_le_iff₀ hVv]
    have : 0 ≤ cubeTau (d := d) p n + r := add_nonneg hτ0 hr0
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq this)
      (by positivity : (0 : ℝ) ≤ 3 * 3 ^ d * CD * V.latticeVolume)
    linarith
  -- assembly
  have hm := main.trans (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5)
  have hk1 : 0 ≤ 3 * 3 ^ d * ((d : ℝ) * σ ^ 2) := by positivity
  have t1 := mul_le_mul_of_nonneg_left hτn hk1
  have t2 := mul_le_mul_of_nonneg_left hτn hk3
  rw [hK₁, hK₂]
  linarith

/-- **Lemma 5.9 of Armstrong and Dario** (display (5.25), every dimension `d ≥ 2`): there are `C`
and `N` with `D_n ≤ C 3^{-n/4} + C ∑_{l ≤ n} 3^{l-n} τ_l` for `n ≥ N`. The printed statement has
`3^{-n s}` for some `s(d, 𝔭) > 0`; here `s = 1/4`, written `(1/√√3)ⁿ`. -/
theorem exists_cubeOmegaD_le_decay [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → cubeOmegaD (d := d) p n ≤
      C * (1 / √(√(3 : ℝ))) ^ n +
        C * ∑ l ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - l) * cubeTau (d := d) p l := by
  obtain ⟨K₁, K₂, hK₁, hK₂, N, h⟩ := exists_cubeOmegaD_term_le hd hpc
  refine ⟨d * (K₁ + K₂), mul_nonneg (Nat.cast_nonneg d) (add_nonneg hK₁ hK₂), N, fun n hn => ?_⟩
  set r : ℝ := (1 / √(√(3 : ℝ))) ^ n with hr
  set Sτ : ℝ := ∑ l ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - l) * cubeTau (d := d) p l
    with hSτ
  have hr0 : 0 ≤ r := by positivity
  have hS0 : 0 ≤ Sτ := Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (cubeTau_nonneg p l)
  have hterm : ∀ i : Fin d, cubeNuMean p n (Pi.single i 1) +
      cubeMuMean p n (cubeAhomFinite p n *ᵥ Pi.single i 1) -
        (cubeAhomFinite p n *ᵥ Pi.single i 1) i ≤ (K₁ + K₂) * (r + Sτ) := by
    intro i
    have hi := h n hn i
    rw [one_div_sqrt_sqrt_three_pow, ← hr, ← hSτ] at hi
    have := mul_nonneg hK₁ hS0
    have := mul_nonneg hK₂ hr0
    linarith
  unfold cubeOmegaD
  calc ∑ i : Fin d, (cubeNuMean p n (Pi.single i 1) +
        cubeMuMean p n (cubeAhomFinite p n *ᵥ Pi.single i 1) -
          (cubeAhomFinite p n *ᵥ Pi.single i 1) i)
      ≤ ∑ _i : Fin d, (K₁ + K₂) * (r + Sτ) := Finset.sum_le_sum fun i _ => hterm i
    _ = d * (K₁ + K₂) * r + d * (K₁ + K₂) * Sτ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Rigidity.Percolation
