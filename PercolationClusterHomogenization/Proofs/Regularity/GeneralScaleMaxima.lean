import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorBasic

/-!
# The maximum of the minimal scales over a box of `ℤᵈ`, by Borel–Cantelli

For random scales `𝒳_z`, `z ∈ ℤᵈ`, with `E[exp((𝒳_z/θ)^s)] ≤ 2` uniformly in `z`, and every
`γ > 0`, almost surely `𝒳_z ≤ 3^{kγ}` for all `z` in the box `{|z_i| ≤ 3^{k+2}}` and all large `k`
(`ae_eventually_scale_le_three`). The Chebyshev bound `P(𝒳_z > t) ≤ 2 e^{-(t/θ)^s}`, the bound
`e^{-x} ≤ n!/x^n` and the union over the `(2 · 3^{k+2} + 1)^d` points of the box give
`P(∃ z, 𝒳_z > 3^{kγ}) ≤ A 3^{-k}`, which is summable. This is the step from the minimal scale at
one point to its maximum over `𝒞_∞ ∩ B_r` in the Remark after (1.19) of Armstrong and Dario
(arXiv:1609.09431v2), with the Borel–Cantelli lemma in place of (1.8).
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation
open scoped ENNReal Nat

variable {d : ℕ}

/-- The Chebyshev bound for a random variable with an exponential moment. -/
theorem measureReal_lt_le [NeZero d] {p : unitInterval} {Y : Configuration d → ℝ} {s θ t : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (ht : 0 ≤ t)
    (hYi : Integrable (fun ω => Real.exp (Real.rpow (Y ω / θ) s)) (latticeBondLaw d p))
    (hYb : (∫ ω, Real.exp (Real.rpow (Y ω / θ) s) ∂latticeBondLaw d p) ≤ 2) :
    (latticeBondLaw d p).real {ω | t < Y ω} ≤ 2 / Real.exp (Real.rpow (t / θ) s) := by
  have hE : 0 < Real.exp (Real.rpow (t / θ) s) := Real.exp_pos _
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := latticeBondLaw d p)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hYi
    (Real.exp (Real.rpow (t / θ) s))
  have hsub : {ω | t < Y ω} ⊆
      {ω | Real.exp (Real.rpow (t / θ) s) ≤ Real.exp (Real.rpow (Y ω / θ) s)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine Real.exp_le_exp.2 (Real.rpow_le_rpow (div_nonneg ht hθ.le) ?_ hs.le)
    exact div_le_div_of_nonneg_right hω.le hθ.le
  have hmono : (latticeBondLaw d p).real {ω | t < Y ω} ≤ (latticeBondLaw d p).real
      {ω | Real.exp (Real.rpow (t / θ) s) ≤ Real.exp (Real.rpow (Y ω / θ) s)} :=
    measureReal_mono hsub
  rw [le_div_iff₀ hE]
  calc (latticeBondLaw d p).real {ω | t < Y ω} * Real.exp (Real.rpow (t / θ) s)
      ≤ Real.exp (Real.rpow (t / θ) s) * (latticeBondLaw d p).real
          {ω | Real.exp (Real.rpow (t / θ) s) ≤ Real.exp (Real.rpow (Y ω / θ) s)} := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmono hE.le
    _ ≤ _ := hM
    _ ≤ 2 := hYb

/-- The box `{z ∈ ℤᵈ : |z_i| ≤ 3^{k+2}}`. -/
noncomputable def triScaleBox (d k : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(3 : ℤ) ^ (k + 2)) (3 ^ (k + 2))

theorem mem_triScaleBox {k : ℕ} {z : Vertex d} :
    z ∈ triScaleBox d k ↔ ∀ i, |z i| ≤ 3 ^ (k + 2) := by
  simp only [triScaleBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem card_triScaleBox_le (k : ℕ) :
    ((triScaleBox d k).card : ℝ) ≤ (3 : ℝ) ^ (3 * d) * ((3 : ℝ) ^ d) ^ k := by
  have hI : ((Finset.Icc (-(3 : ℤ) ^ (k + 2)) (3 ^ (k + 2))).card : ℝ) =
      2 * (3 : ℝ) ^ (k + 2) + 1 := by
    rw [Int.card_Icc, show (3 : ℤ) ^ (k + 2) + 1 - -(3 : ℤ) ^ (k + 2) = 2 * 3 ^ (k + 2) + 1 by ring]
    have h0 : (0 : ℤ) ≤ 2 * 3 ^ (k + 2) + 1 := by positivity
    have e := Int.toNat_of_nonneg h0
    have : (((2 * 3 ^ (k + 2) + 1 : ℤ).toNat : ℕ) : ℝ) = (((2 * 3 ^ (k + 2) + 1 : ℤ).toNat : ℤ) : ℝ) :=
      rfl
    rw [this, e]
    push_cast
    ring
  have h1 : ((triScaleBox d k).card : ℝ) = (2 * (3 : ℝ) ^ (k + 2) + 1) ^ d := by
    rw [triScaleBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [hI]
  rw [h1]
  have h2 : (2 * (3 : ℝ) ^ (k + 2) + 1) ≤ 3 ^ (k + 3) := by
    have : (1 : ℝ) ≤ 3 ^ (k + 2) := one_le_pow₀ (by norm_num)
    have e : (3 : ℝ) ^ (k + 3) = 3 * 3 ^ (k + 2) := by ring
    linarith
  calc (2 * (3 : ℝ) ^ (k + 2) + 1) ^ d ≤ ((3 : ℝ) ^ (k + 3)) ^ d :=
        pow_le_pow_left₀ (by positivity) h2 d
    _ = (3 : ℝ) ^ (3 * d) * ((3 : ℝ) ^ d) ^ k := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring

/-- **The maximum of the minimal scales over the triadic boxes**, almost surely for all large `k`. -/
theorem ae_eventually_scale_le_three [NeZero d] {p : unitInterval}
    {Y : Vertex d → Configuration d → ℝ} {s θ γ : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hγ : 0 < γ)
    (hYi : ∀ z, Integrable (fun ω => Real.exp (Real.rpow (Y z ω / θ) s)) (latticeBondLaw d p))
    (hYb : ∀ z, (∫ ω, Real.exp (Real.rpow (Y z ω / θ) s) ∂latticeBondLaw d p) ≤ 2) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ᶠ k : ℕ in atTop, ∀ z ∈ triScaleBox d k,
      Y z ω ≤ (3 : ℝ) ^ ((k : ℝ) * γ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (d : ℝ) + 1 ≤ γ * s * n := by
    obtain ⟨n, hn⟩ := exists_nat_ge (((d : ℝ) + 1) / (γ * s))
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  set E : ℕ → Set (Configuration d) := fun k =>
    ⋃ z ∈ triScaleBox d k, {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} with hEdef
  set A : ℝ := 2 * (3 : ℝ) ^ (3 * d) * (n ! : ℝ) * θ ^ (s * n) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hbound : ∀ k : ℕ, (latticeBondLaw d p) (E k) ≤ ENNReal.ofReal (A * (1 / 3) ^ k) := by
    intro k
    have ht0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((k : ℝ) * γ) := by positivity
    have hx : 0 < Real.rpow ((3 : ℝ) ^ ((k : ℝ) * γ) / θ) s :=
      Real.rpow_pos_of_pos (by positivity) _
    have hxpow : Real.rpow ((3 : ℝ) ^ ((k : ℝ) * γ) / θ) s ^ n =
        (3 : ℝ) ^ ((k : ℝ) * (γ * s * n)) / θ ^ (s * n) := by
      change (((3 : ℝ) ^ ((k : ℝ) * γ) / θ) ^ s) ^ n = _
      rw [Real.div_rpow (by positivity) hθ.le, div_pow, ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul hθ.le]
      congr 2
      ring
    have hpt : ∀ z ∈ triScaleBox d k, (latticeBondLaw d p).real
        {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} ≤
          2 * (n ! : ℝ) * θ ^ (s * n) / (3 : ℝ) ^ ((k : ℝ) * (γ * s * n)) := by
      intro z _
      refine (measureReal_lt_le hs hθ ht0 (hYi z) (hYb z)).trans ?_
      have h1 := inv_exp_le_factorial_div_pow hx n
      rw [hxpow] at h1
      have e : 2 / Real.exp (Real.rpow ((3 : ℝ) ^ ((k : ℝ) * γ) / θ) s) =
          2 * (1 / Real.exp (Real.rpow ((3 : ℝ) ^ ((k : ℝ) * γ) / θ) s)) := by ring
      rw [e]
      calc 2 * (1 / Real.exp (Real.rpow ((3 : ℝ) ^ ((k : ℝ) * γ) / θ) s))
          ≤ 2 * ((n ! : ℝ) / ((3 : ℝ) ^ ((k : ℝ) * (γ * s * n)) / θ ^ (s * n))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 2 * (n ! : ℝ) * θ ^ (s * n) / (3 : ℝ) ^ ((k : ℝ) * (γ * s * n)) := by
            field_simp
    have h8 : ((3 : ℝ) ^ (d + 1)) ^ k ≤ (3 : ℝ) ^ ((k : ℝ) * (γ * s * n)) := by
      calc ((3 : ℝ) ^ (d + 1)) ^ k = (3 : ℝ) ^ ((k : ℝ) * ((d : ℝ) + 1)) := by
            rw [← pow_mul, ← Real.rpow_natCast]
            congr 1
            push_cast
            ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg k))
    have hunion : (latticeBondLaw d p) (E k) ≤ ∑ z ∈ triScaleBox d k,
        (latticeBondLaw d p) {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} :=
      measure_biUnion_finset_le _ _
    refine hunion.trans ?_
    have hfin : ∀ z ∈ triScaleBox d k, (latticeBondLaw d p) {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} =
        ENNReal.ofReal ((latticeBondLaw d p).real {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω}) :=
      fun z _ => (ofReal_measureReal (measure_ne_top _ _)).symm
    rw [Finset.sum_congr rfl hfin, ← ENNReal.ofReal_sum_of_nonneg fun _ _ => measureReal_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : (0 : ℝ) < ((3 : ℝ) ^ (d + 1)) ^ k := by positivity
    calc ∑ z ∈ triScaleBox d k, (latticeBondLaw d p).real {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω}
        ≤ ∑ _z ∈ triScaleBox d k,
            2 * (n ! : ℝ) * θ ^ (s * n) / (3 : ℝ) ^ ((k : ℝ) * (γ * s * n)) :=
          Finset.sum_le_sum hpt
      _ = (triScaleBox d k).card * (2 * (n ! : ℝ) * θ ^ (s * n) /
            (3 : ℝ) ^ ((k : ℝ) * (γ * s * n))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 : ℝ) ^ (3 * d) * ((3 : ℝ) ^ d) ^ k *
            (2 * (n ! : ℝ) * θ ^ (s * n) / ((3 : ℝ) ^ (d + 1)) ^ k) := by
          gcongr
          exact card_triScaleBox_le k
      _ = A * (1 / 3) ^ k := by
          rw [hAdef, div_pow, one_pow, show ((3 : ℝ) ^ (d + 1)) ^ k = ((3 : ℝ) ^ d) ^ k * 3 ^ k by
            rw [← mul_pow, pow_succ]]
          field_simp
  have hsum : ∑' k, (latticeBondLaw d p) (E k) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with k hk z hz
  by_contra hlt
  push Not at hlt
  exact hk (Set.mem_biUnion hz hlt)

end Rigidity.Proofs.Regularity.GeneralDim
