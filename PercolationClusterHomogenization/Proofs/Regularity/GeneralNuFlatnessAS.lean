import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectedPlaneExistence
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFlatnessNuExpect
import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaMeasurable
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSectionFive
import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaSupRate

/-!
# The flatness of the maximizers of `ν` on `ℤᵈ` almost surely at all large scales

Armstrong and Dario (arXiv:1609.09431v2), Lemma 5.8, display (5.33), in every dimension
(`exists_lintegral_cubeNuFlatness_le`), bounds the expectation of the flatness error of the
coarsened maximizer `v(·, □_{n+1}, ā⁻¹ q)` of `ν` by
`C |q|² 9^n (3^{-n/4} + 3^{-n} Σ_{k ≤ n} 3^k τ_k)`, and Lemma 5.10 gives the geometric decay of
`τ_k` (`exists_cubeTau_le_pow`). `ae_eventually_cubeNuFlatness_le` upgrades them to an almost sure
bound at all large scales: the bracket is at most `B (n+1) μ₁^n` with `μ₁ < 1`
(`flatness_bracket_le`), and the Chebyshev inequality and the Borel–Cantelli lemma give
`flatness ≤ (|q|² + 1) 9^n μ^n` eventually, `μ = μ₁^{1/2}`. Since `ā = σ I` with `σ > 0`, the slope
`ā⁻¹ (ā ξ)` is `ξ` (`cubeAhom_inv_mulVec_mulVec`).
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped ENNReal Matrix

variable {d : ℕ} {p : unitInterval}

/-- `ā⁻¹ (ā ξ) = ξ`. -/
theorem cubeAhom_inv_mulVec_mulVec [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) (ξ : Fin d → ℝ) :
    (cubeAhom (d := d) p)⁻¹ *ᵥ (cubeAhom p *ᵥ ξ) = ξ := by
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  rw [hA, inv_smul_one_eq hσ.ne', Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]

/-- The bracket of (5.33) under the geometric decay of `τ`. -/
theorem flatness_bracket_le [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ B μ₁ : ℝ, 0 ≤ B ∧ 0 < μ₁ ∧ μ₁ < 1 ∧ ∀ n : ℕ,
      (3 : ℝ) ^ (-(n : ℝ) / 4) +
          ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * cubeTau (d := d) p k ≤
        B * (n + 1) * μ₁ ^ n := by
  obtain ⟨K, l, hl0, hl1, N, hN⟩ := exists_cubeTau_le_pow hd hpc
  set T₀ : ℝ := ∑ k ∈ Finset.range N, (3 : ℝ) ^ k * cubeTau (d := d) p k with hT₀
  have hT₀0 : 0 ≤ T₀ := Finset.sum_nonneg fun k _ => mul_nonneg (by positivity)
    (cubeTau_nonneg p k)
  set K' := max K 0 with hK'
  set μ₁ : ℝ := max (max l (1 / 3)) ((3 : ℝ) ^ (-(1 / 4 : ℝ))) with hμdef
  have h10 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hμ1 : μ₁ < 1 := max_lt (max_lt hl1 (by norm_num)) h10
  have hμ0 : 0 < μ₁ := lt_of_lt_of_le hl0 ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨1 + T₀ + K', μ₁, by positivity, hμ0, hμ1, fun n => ?_⟩
  -- the first term
  have h1 : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ μ₁ ^ n := by
    have e : (3 : ℝ) ^ (-(n : ℝ) / 4) = ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
    rw [e]
    exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) n
  -- the sum
  have hτ : ∀ k, (3 : ℝ) ^ k * cubeTau (d := d) p k ≤
      (if k < N then (3 : ℝ) ^ k * cubeTau (d := d) p k else 0) + K' * 3 ^ k * l ^ k := by
    intro k
    split_ifs with hk
    · have : 0 ≤ K' * 3 ^ k * l ^ k := by positivity
      linarith
    · have := hN k (by omega)
      have h2 : K * l ^ k ≤ K' * l ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      calc (3 : ℝ) ^ k * cubeTau (d := d) p k ≤ 3 ^ k * (K' * l ^ k) :=
            mul_le_mul_of_nonneg_left (this.trans h2) (by positivity)
        _ = 0 + K' * 3 ^ k * l ^ k := by ring
  have hsum : ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * cubeTau (d := d) p k ≤
      T₀ + ∑ k ∈ Finset.range (n + 1), K' * 3 ^ k * l ^ k := by
    refine (Finset.sum_le_sum fun k _ => hτ k).trans ?_
    rw [Finset.sum_add_distrib]
    gcongr
    calc ∑ k ∈ Finset.range (n + 1), (if k < N then (3 : ℝ) ^ k * cubeTau (d := d) p k else 0)
        = ∑ k ∈ (Finset.range (n + 1)).filter (· < N), (3 : ℝ) ^ k * cubeTau (d := d) p k := by
          rw [Finset.sum_filter]
      _ ≤ T₀ := by
          rw [hT₀]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ =>
            mul_nonneg (by positivity) (cubeTau_nonneg p k)
          rw [Finset.mem_filter] at hk
          exact Finset.mem_range.2 hk.2
  have hgeo : ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), K' * 3 ^ k * l ^ k ≤
      K' * (n + 1) * μ₁ ^ n := by
    have hpt : ∀ k ∈ Finset.range (n + 1),
        ((3 : ℝ) ^ n)⁻¹ * (K' * 3 ^ k * l ^ k) ≤ K' * μ₁ ^ n := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have e : ((3 : ℝ) ^ n)⁻¹ * (K' * 3 ^ k * l ^ k) = K' * ((1 / 3 : ℝ) ^ (n - k) * l ^ k) := by
        rw [div_pow, one_pow, show (3 : ℝ) ^ n = 3 ^ (n - k) * 3 ^ k by
          rw [← pow_add]; congr 1; omega]
        field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
      calc (1 / 3 : ℝ) ^ (n - k) * l ^ k ≤ μ₁ ^ (n - k) * μ₁ ^ k := by
            gcongr
            · exact (le_max_right _ _).trans (le_max_left _ _)
            · exact (le_max_left _ _).trans (le_max_left _ _)
        _ = μ₁ ^ n := by rw [← pow_add]; congr 1; omega
    rw [Finset.mul_sum]
    calc ∑ k ∈ Finset.range (n + 1), ((3 : ℝ) ^ n)⁻¹ * (K' * 3 ^ k * l ^ k)
        ≤ ∑ _k ∈ Finset.range (n + 1), K' * μ₁ ^ n := Finset.sum_le_sum hpt
      _ = K' * (n + 1) * μ₁ ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hT : ((3 : ℝ) ^ n)⁻¹ * T₀ ≤ T₀ * μ₁ ^ n := by
    have : ((3 : ℝ) ^ n)⁻¹ ≤ μ₁ ^ n := by
      rw [← one_div, show (1 : ℝ) / 3 ^ n = (1 / 3) ^ n by rw [div_pow, one_pow]]
      exact pow_le_pow_left₀ (by positivity) ((le_max_right _ _).trans (le_max_left _ _)) n
    nlinarith
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hμn : 0 ≤ μ₁ ^ n := by positivity
  calc (3 : ℝ) ^ (-(n : ℝ) / 4) +
        ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * cubeTau (d := d) p k
      ≤ μ₁ ^ n + (((3 : ℝ) ^ n)⁻¹ * T₀ +
          ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), K' * 3 ^ k * l ^ k) := by
        rw [← mul_add]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ ≤ μ₁ ^ n + (T₀ * μ₁ ^ n + K' * (n + 1) * μ₁ ^ n) := by linarith
    _ ≤ (1 + T₀ + K') * (n + 1) * μ₁ ^ n := by
        have h2 : 0 ≤ (1 + T₀) * (n : ℝ) * μ₁ ^ n := by positivity
        have e : (1 + T₀ + K') * (n + 1) * μ₁ ^ n =
            μ₁ ^ n + (T₀ * μ₁ ^ n + K' * (n + 1) * μ₁ ^ n) + (1 + T₀) * (n : ℝ) * μ₁ ^ n := by
          ring
        linarith

/-- **The flatness of the maximizers of `ν` almost surely at all large scales**, in every dimension
`d ≥ 2`, from (5.33) in expectation and the geometric decay of `τ`, by the Chebyshev inequality and
Borel–Cantelli. -/
theorem ae_eventually_cubeNuFlatness_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∀ q : Fin d → ℝ, ∀ᵐ ω ∂(latticeBondLaw d p), ∀ᶠ n in atTop,
      cubeFlatnessError ⟨n + 1, 0⟩
          (fun x => cubeExtend ω ⟨n + 1, 0⟩
            (cubeNuSolution ω ⟨n + 1, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q)) (partitionAnchor ω x))
          ((cubeAhom p)⁻¹ *ᵥ q) ≤
        (∑ i, q i ^ 2 + 1) * 9 ^ n * μ ^ n := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, hC, hΦint⟩ := exists_lintegral_cubeNuFlatness_le hd hpc
  obtain ⟨B, μ₁, hB, hμ₁0, hμ₁1, hbr⟩ := flatness_bracket_le hd hpc
  set μ : ℝ := Real.sqrt μ₁ with hμ
  have hμ0 : 0 < μ := Real.sqrt_pos.2 hμ₁0
  have hμ1 : μ < 1 := by rw [hμ, Real.sqrt_lt' one_pos]; simpa using hμ₁1
  have hμsq : μ ^ 2 = μ₁ := Real.sq_sqrt hμ₁0.le
  refine ⟨μ, hμ0, hμ1, fun q => ?_⟩
  set Φ : ℕ → Configuration d → ℝ := fun n ω => cubeFlatnessError ⟨n + 1, 0⟩
    (fun x => cubeExtend ω ⟨n + 1, 0⟩
      (cubeNuSolution ω ⟨n + 1, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q)) (partitionAnchor ω x))
    ((cubeAhom p)⁻¹ *ᵥ q) with hΦdef
  have hΦm : ∀ n, Measurable (Φ n) := fun n =>
    measurable_cubeFlatnessError_cubeNuSolution hd0 ⟨n + 1, 0⟩ _ _
  set Q : ℝ := ∑ i, q i ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set t : ℕ → ℝ := fun n => (Q + 1) * 9 ^ n * μ ^ n with ht
  have ht0 : ∀ n, 0 < t n := fun n => by rw [ht]; positivity
  set E : ℕ → Set (Configuration d) :=
    fun n => {ω | ENNReal.ofReal (t n) ≤ ENNReal.ofReal (Φ n ω)} with hE
  have hEle : ∀ n, (latticeBondLaw d p) (E n) ≤ ENNReal.ofReal (C * B * ((n + 1) * μ ^ n)) := by
    intro n
    have hm := meas_ge_le_lintegral_div (μ := latticeBondLaw d p)
      (hΦm n).ennreal_ofReal.aemeasurable
      (ENNReal.ofReal_pos.2 (ht0 n)).ne' ENNReal.ofReal_ne_top
    refine hm.trans ?_
    rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 (ht0 n)).ne' ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_mul (by positivity)]
    refine (hΦint n q).trans (ENNReal.ofReal_le_ofReal ?_)
    have hbn := hbr n
    have e : C * B * ((n + 1) * μ ^ n) * t n = C * (Q + 1) * 9 ^ n * (B * (n + 1) * μ₁ ^ n) := by
      rw [ht, ← hμsq]; ring
    rw [e]
    have hC9 : 0 ≤ C * Q * 9 ^ n := by positivity
    calc C * Q * 9 ^ n * ((3 : ℝ) ^ (-(n : ℝ) / 4) +
          ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * cubeTau (d := d) p k)
        ≤ C * Q * 9 ^ n * (B * (n + 1) * μ₁ ^ n) := mul_le_mul_of_nonneg_left hbn hC9
      _ ≤ C * (Q + 1) * 9 ^ n * (B * (n + 1) * μ₁ ^ n) := by
          have h0 : 0 ≤ B * (n + 1) * μ₁ ^ n := by positivity
          have h1 : C * Q * 9 ^ n ≤ C * (Q + 1) * 9 ^ n := by
            have := mul_le_mul_of_nonneg_left (by linarith : Q ≤ Q + 1) hC
            exact mul_le_mul_of_nonneg_right this (by positivity)
          exact mul_le_mul_of_nonneg_right h1 h0
  have hsumm : Summable fun n : ℕ => C * B * ((n + 1) * μ ^ n) := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * μ ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_pos hμ0]; exact hμ1)
    have h2 : Summable fun n : ℕ => μ ^ n := summable_geometric_of_lt_one hμ0.le hμ1
    have h3 : Summable fun n : ℕ => (n + 1 : ℝ) * μ ^ n := by
      have := h1.add h2
      refine this.congr fun n => ?_
      simp only [pow_one]; ring
    exact h3.mul_left (C * B)
  have hsum : ∑' n, (latticeBondLaw d p) (E n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  have hlt : Φ n ω < t n := by
    by_contra hge
    push Not at hge
    exact hn (ENNReal.ofReal_le_ofReal hge)
  exact hlt.le

end Rigidity.Proofs.Regularity.GeneralDim
