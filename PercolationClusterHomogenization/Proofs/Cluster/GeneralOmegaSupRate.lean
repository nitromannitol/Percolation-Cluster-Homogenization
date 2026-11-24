import PercolationClusterHomogenization.Proofs.Cluster.GeneralConvergenceRate
import PercolationClusterHomogenization.Proofs.Cluster.GeneralNablaAffineExpect

/-!
# Lemma 5.10 of Armstrong and Dario, display (5.42), in every dimension, given the bound of
Lemma 5.9

For a triadic cube `U` let `ω(U, q) = ν(U, ā⁻¹ q) - μ(U, q) - q · ā⁻¹ q` (`cubeOmega`, with `μ`
and `ν` replaced by `0` off the event that the partition exists and resolves `U`) and
`ρ(U) = sup_q |q|⁻² ω(U, q)₊` (`cubeRho`). Display (5.42) of Armstrong and Dario states

`E[ρ(□_n)] ≤ C 3^{-nα}`.

Step 4 of their proof, in every dimension `d ≥ 2`:

* **sums control suprema**: on the partition event and for a resolved cube, `q ↦ ω(U, q)` is a
  quadratic form with `ω(U, q) ≥ -d S Y(U) |q|²` (Corollary 4.6, `neg_le_cubeOmega`), so that
  `ρ(U) ≤ d ∑ⱼ ω(U, eⱼ) + d³ S Y(U)` (`cubeRho_le_of_resolved`);
* off the resolution of `U`, `ω(U, q) = -q · ā⁻¹ q ≤ 0` since `ā = σ I`, so `ρ(U) = 0`
  (`cubeRho_le_zero_of_not`); on the partition event this happens only when some vertex has a
  partition cube of side at least `3 · 3ⁿ`, an event of probability `O(3^{-n})`;
* `E[Y(□_n)] ≤ C 3^{-n/2}` from the moments of the partition sizes near the faces
  (`cubeComparisonError_le`), and `E[ω(□_n, eⱼ)] ≤ C lⁿ` by display (5.4), here the bound
  `exists_abs_cubeMuMean_sub_le_of_decay`, `exists_abs_cubeNuMean_sub_le_of_decay` derived from
  the bound of Lemma 5.9.

The result (`exists_cubeRho_majorant_of_decay`) is stated with an integrable majorant of
`ρ(□_n)`, the supremum being over an uncountable set, and with the hypothesis of Lemma 5.9 as in
`exists_cubeTau_le_pow_of_decay`. This is the general-dimensional form of
`Rigidity.Proofs.Cluster.planar_omegadecayrate`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- A bound `ω(U, q)₊ ≤ B |q|²` for every `q` bounds `ρ(U)` by `B`. -/
theorem cubeRho_le_of_forall {p : unitInterval} {U : TriadicCube d} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ q, max (cubeOmega p ω U q) 0 ≤ B * ∑ i, q i ^ 2) : cubeRho p ω U ≤ B := by
  refine ciSup_le fun q => ?_
  rcases (Finset.sum_nonneg fun i _ => sq_nonneg (q i) : (0 : ℝ) ≤ ∑ i, q i ^ 2).eq_or_lt
    with h | h
  · rw [← h, div_zero]
    exact hB0
  · rw [div_le_iff₀ h]
    exact hB q

/-- **Sums control suprema** (Armstrong and Dario, Step 4 of the proof of Lemma 5.10, every
dimension): on the partition event and for a resolved cube,
`ρ(U) ≤ d ∑ⱼ ω(U, eⱼ) + d³ S Y(U)`. -/
theorem cubeRho_le_of_resolved (hd : 0 < d) (p : unitInterval) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) :
    cubeRho p ω U ≤ d * ∑ j, cubeOmega p ω U (Pi.single j 1) +
      d ^ 3 * S * cubeComparisonError ω U := by
  set K : ℝ := d * S * cubeComparisonError ω U with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hS0) (cubeComparisonError_nonneg ω U)
  have hg := (isSlopeQuadratic_cubeOmega hd p ω U).add_mul_sum_sq K
  have hg0 : ∀ q : Fin d → ℝ, 0 ≤ cubeOmega p ω U q + K * ∑ i, q i ^ 2 := fun q => by
    have := neg_le_cubeOmega hd p hP hU hS q
    linarith
  have hsingle : ∀ j : Fin d, ∑ i, (Pi.single j 1 : Fin d → ℝ) i ^ 2 = 1 := fun j => by
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
    simp
  set T : ℝ := ∑ j, cubeOmega p ω U (Pi.single j 1) + d * K with hT
  have hsum : ∑ j, (cubeOmega p ω U (Pi.single j 1) +
      K * ∑ i, (Pi.single j 1 : Fin d → ℝ) i ^ 2) = T := by
    simp only [hsingle, mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hT]
  have hT0 : 0 ≤ T := by
    rw [← hsum]
    exact Finset.sum_nonneg fun j _ => hg0 _
  have hB : d * ∑ j, cubeOmega p ω U (Pi.single j 1) + d ^ 3 * S * cubeComparisonError ω U =
      d * T := by
    rw [hT, hK]
    ring
  rw [hB]
  refine cubeRho_le_of_forall (mul_nonneg (Nat.cast_nonneg d) hT0) fun q => ?_
  have hle := hg.le_of_nonneg hg0 q
  beta_reduce at hle
  rw [hsum] at hle
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  refine max_le ?_ (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hT0) hq0)
  nlinarith [mul_nonneg hK0 hq0]

/-- `q · ā⁻¹ q ≥ 0`, since `ā = σ I` with `σ > 0`. -/
theorem sum_mul_inv_cubeAhom_mulVec_nonneg [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (q : Fin d → ℝ) :
    0 ≤ ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  have hv : (cubeAhom (d := d) p)⁻¹ *ᵥ q = σ⁻¹ • q := by
    rw [hA, inv_smul_one_eq hσ.ne', Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hv]
  refine Finset.sum_nonneg fun i _ => ?_
  have h := mul_nonneg (inv_nonneg.2 hσ.le) (mul_self_nonneg (q i))
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith [show q i * (σ⁻¹ * q i) = σ⁻¹ * (q i * q i) by ring]

/-- `ā (ā⁻¹ q) = q`. -/
theorem cubeAhom_mulVec_inv_mulVec [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (q : Fin d → ℝ) :
    cubeAhom p *ᵥ ((cubeAhom (d := d) p)⁻¹ *ᵥ q) = q := by
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  rw [hA, inv_smul_one_eq hσ.ne', Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]

/-- Off the event that the partition exists and resolves `U`, `ω(U, q) = -q · ā⁻¹ q`. -/
theorem cubeOmega_eq_of_not {p : unitInterval} {U : TriadicCube d}
    (h : ¬ (PartitionEvent ω ∧ PartitionResolved ω U)) (q : Fin d → ℝ) :
    cubeOmega p ω U q = -∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
  simp only [cubeOmega, if_neg h, add_zero, zero_sub]

/-- Off the event that the partition exists and resolves `U`, `ρ(U) = 0`. -/
theorem cubeRho_le_zero_of_not [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {U : TriadicCube d}
    (h : ¬ (PartitionEvent ω ∧ PartitionResolved ω U)) : cubeRho p ω U ≤ 0 := by
  refine cubeRho_le_of_forall le_rfl fun q => ?_
  rw [zero_mul, cubeOmega_eq_of_not h]
  exact max_le (neg_nonpos.2 (sum_mul_inv_cubeAhom_mulVec_nonneg hd hpc q)) le_rfl

/-- `2 s ≤ 1/t + t s²` for `t > 0`. -/
theorem two_mul_le_one_div_add_mul_sq {s t : ℝ} (ht : 0 < t) : 2 * s ≤ 1 / t + t * s ^ 2 := by
  rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
  nlinarith [sq_nonneg (t * s - 1)]

/-- **The comparison error is bounded by an affine function of the face and margin sizes**:
`Y(U) ≤ 3^{-n} + (2d 3^{(d-1)n} + ∑_{∂U} size²)/(2|U|) + 3ᵈ (3^{-n/2} + 3^{n/2} d M(U)/|U|)`,
`n` the scale of `U`, by the Cauchy–Schwarz inequality on the faces and `2√x ≤ 1/t + t x`. -/
theorem cubeComparisonError_le (ω : Configuration d) (U : TriadicCube d) :
    cubeComparisonError ω U ≤
      1 / (3 : ℝ) ^ U.scale + (2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) +
        faceSizeSqSum ω U) / (2 * U.latticeVolume) +
      3 ^ d * (1 / √((3 : ℝ) ^ U.scale) +
        √((3 : ℝ) ^ U.scale) * (d * marginSizeSum ω U / U.latticeVolume)) := by
  have hV := U.latticeVolume_pos
  have hF0 := faceSizeSum_nonneg ω U
  have hFq0 := faceSizeSqSum_nonneg ω U
  have hM0 := marginSizeSum_nonneg ω U
  set a : ℝ := 2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) with ha
  have ha0 : 0 ≤ a := by positivity
  have hF : faceSizeSum ω U ≤ (a + faceSizeSqSum ω U) / 2 := by
    have h := faceSizeSum_sq_le ω U
    rw [← ha] at h
    have h2 : faceSizeSum ω U ^ 2 ≤ ((a + faceSizeSqSum ω U) / 2) ^ 2 := by
      nlinarith [sq_nonneg (a - faceSizeSqSum ω U)]
    exact (sq_le_sq₀ hF0 (by positivity)).1 h2
  set x : ℝ := d * marginSizeSum ω U / U.latticeVolume with hx
  have hx0 : 0 ≤ x := by positivity
  set t : ℝ := √((3 : ℝ) ^ U.scale) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hsq : 2 * √x ≤ 1 / t + t * x := by
    have h := two_mul_le_one_div_add_mul_sq (s := √x) ht
    rwa [Real.sq_sqrt hx0] at h
  have k1 : faceSizeSum ω U / U.latticeVolume ≤
      (a + faceSizeSqSum ω U) / (2 * U.latticeVolume) := by
    rw [div_le_div_iff₀ hV (by positivity)]
    nlinarith
  have k2 : 2 * 3 ^ d * √x ≤ 3 ^ d * (1 / t + t * x) := by
    have h := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 3 ^ d)
    linarith
  unfold cubeComparisonError
  rw [← hx]
  linarith

theorem sum_sq_single_one (j : Fin d) : ∑ i, (Pi.single j 1 : Fin d → ℝ) i ^ 2 = 1 := by
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
  simp

/-- `ω(U, q)` is integrable. -/
theorem integrable_cubeOmega [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (U : TriadicCube d) (q : Fin d → ℝ) :
    Integrable (fun ω => cubeOmega p ω U q) (latticeBondLaw d p) := by
  have iν : Integrable (fun ω : Configuration d => if PartitionEvent ω ∧ PartitionResolved ω U then
      cubeNu ω U ((cubeAhom p)⁻¹ *ᵥ q) else 0) (latticeBondLaw d p) := by
    refine (integrable_cubeNu p U ((cubeAhom p)⁻¹ *ᵥ q)).mono'
      ((Measurable.ite (measurableSet_partitionEvent_resolved U) (measurable_cubeNu U _)
        measurable_const).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (cubeNu_nonneg _)]
    · rw [norm_zero]
      exact cubeNu_nonneg _
  exact (iν.add (integrable_neg_cubeMu_indicator hd hpc U q)).sub (integrable_const _)

/-- `E[ω(□_n, q)] ≤ E[ν(□_n, ā⁻¹ q)] + E[-μ(□_n, q); P, □_n res] - q · ā⁻¹ q`. -/
theorem integral_cubeOmega_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (n : ℕ) (q : Fin d → ℝ) :
    ∫ ω, cubeOmega p ω ⟨n, 0⟩ q ∂(latticeBondLaw d p) ≤
      cubeNuMean p n ((cubeAhom p)⁻¹ *ᵥ q) + cubeMuMean p n q -
        ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
  have hd0 : 0 < d := by omega
  have iν : Integrable (fun ω : Configuration d =>
      if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
        cubeNu ω ⟨n, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q) else 0) (latticeBondLaw d p) := by
    refine (integrable_cubeNu p ⟨n, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q)).mono'
      ((Measurable.ite (measurableSet_partitionEvent_resolved ⟨n, 0⟩) (measurable_cubeNu _ _)
        measurable_const).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (cubeNu_nonneg _)]
    · rw [norm_zero]
      exact cubeNu_nonneg _
  have iμ := integrable_neg_cubeMu_indicator hd hpc ⟨n, 0⟩ q
  have iνμ : Integrable (fun ω : Configuration d =>
      (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
        cubeNu ω ⟨n, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q) else 0) +
      (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
        -cubeMu ω ⟨n, 0⟩ q else 0)) (latticeBondLaw d p) := iν.add iμ
  have hval : ∫ ω, cubeOmega p ω ⟨n, 0⟩ q ∂(latticeBondLaw d p) =
      (∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
        cubeNu ω ⟨n, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q) else 0) ∂(latticeBondLaw d p)) +
      (∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
        -cubeMu ω ⟨n, 0⟩ q else 0) ∂(latticeBondLaw d p)) -
      ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
    simp only [cubeOmega]
    rw [integral_sub iνμ (integrable_const _), integral_add iν iμ, integral_const,
      probReal_univ, one_smul]
  rw [hval, integral_neg_cubeMu_indicator_eq_cubeMuMean hd0]
  have hle : ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
      cubeNu ω ⟨n, 0⟩ ((cubeAhom p)⁻¹ *ᵥ q) else 0) ∂(latticeBondLaw d p) ≤
      cubeNuMean p n ((cubeAhom p)⁻¹ *ᵥ q) :=
    integral_mono iν (integrable_cubeNu p _ _) fun ω => by
      dsimp only
      split_ifs
      · exact le_rfl
      · exact cubeNu_nonneg _
  linarith

/-- **Display (5.4) for `ω`**: from the bound of Lemma 5.9,
`∑ⱼ E[ω(□_n, eⱼ)] ≤ K lⁿ` for every `n`. -/
theorem exists_sum_integral_cubeOmega_single_le_of_decay [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ}
    (hC₉ : 0 ≤ C₉) (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∀ n : ℕ,
      ∑ j, ∫ ω, cubeOmega p ω ⟨n, 0⟩ (Pi.single j 1) ∂(latticeBondLaw d p) ≤ K * l ^ n := by
  obtain ⟨Kμ, lμ, hKμ, hlμ0, hlμ1, Nμ, hμ⟩ :=
    exists_abs_cubeMuMean_sub_le_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨Kν, lν, hKν, hlν0, hlν1, Nν, hν⟩ :=
    exists_abs_cubeNuMean_sub_le_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  set l := max lμ lν with hl
  have hl0 : 0 < l := lt_max_of_lt_left hlμ0
  have hl1 : l < 1 := max_lt hlμ1 hlν1
  set N := max Nμ Nν with hN
  set W := ∑ j : Fin d, ∑ i, ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  set B₀ := ∑ m ∈ Finset.range N,
    |∑ j, ∫ ω, cubeOmega p ω ⟨m, 0⟩ (Pi.single j 1) ∂(latticeBondLaw d p)| with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨d * Kμ + Kν * W + B₀ / l ^ N, l, by positivity, hl0, hl1, fun n => ?_⟩
  have hlN : 0 < l ^ N := pow_pos hl0 N
  have hA0 : 0 ≤ (d * Kμ + Kν * W) * l ^ n := by positivity
  have hB1 : 0 ≤ B₀ / l ^ N * l ^ n := by positivity
  by_cases hn : N ≤ n
  · have hj : ∀ j : Fin d, ∫ ω, cubeOmega p ω ⟨n, 0⟩ (Pi.single j 1) ∂(latticeBondLaw d p) ≤
        Kμ * l ^ n +
          Kν * (∑ i, ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i ^ 2) * l ^ n := by
      intro j
      have h1 := integral_cubeOmega_le hd hpc n (Pi.single j 1)
      have h2 := hμ n (le_of_max_le_left hn) (Pi.single j 1)
      have h3 := hν n (le_of_max_le_right hn) ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1)
      rw [cubeAhom_mulVec_inv_mulVec hd hpc] at h3
      rw [sum_sq_single_one, mul_one] at h2
      have hcomm : ∑ i, ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i *
          (Pi.single j 1 : Fin d → ℝ) i =
          ∑ i, (Pi.single j 1 : Fin d → ℝ) i * ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [hcomm] at h3
      have hlμ : lμ ^ n ≤ l ^ n := pow_le_pow_left₀ hlμ0.le (le_max_left _ _) n
      have hlν : lν ^ n ≤ l ^ n := pow_le_pow_left₀ hlν0.le (le_max_right _ _) n
      have a1 := le_abs_self (cubeMuMean p n (Pi.single j 1) - 1 / 2 *
        ∑ i, (Pi.single j 1 : Fin d → ℝ) i * ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i)
      have a2 := le_abs_self (cubeNuMean p n ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) - 1 / 2 *
        ∑ i, (Pi.single j 1 : Fin d → ℝ) i * ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i)
      have k1 : Kμ * lμ ^ n ≤ Kμ * l ^ n := mul_le_mul_of_nonneg_left hlμ hKμ
      have k2 : Kν * (∑ i, ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i ^ 2) * lν ^ n ≤
          Kν * (∑ i, ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i ^ 2) * l ^ n :=
        mul_le_mul_of_nonneg_left hlν (by positivity)
      linarith
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hj j
    have e : ∑ j : Fin d, (Kμ * l ^ n +
        Kν * (∑ i, ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i ^ 2) * l ^ n) =
        (d * Kμ + Kν * W) * l ^ n := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum, hW]
      ring
    rw [e] at hsum
    nlinarith
  · have hn' : n < N := not_le.1 hn
    have h1 : ∑ j, ∫ ω, cubeOmega p ω ⟨n, 0⟩ (Pi.single j 1) ∂(latticeBondLaw d p) ≤ B₀ :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun m =>
        |∑ j, ∫ ω, cubeOmega p ω ⟨m, 0⟩ (Pi.single j 1) ∂(latticeBondLaw d p)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hn'))
    have h2 : B₀ ≤ B₀ / l ^ N * l ^ n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlN]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hl0.le hl1.le hn'.le) hB₀0
    nlinarith

/-- **Lemma 5.10 of Armstrong and Dario** (display (5.42), every dimension `d ≥ 2`, given the bound
of Lemma 5.9): there are `C` and `r < 1` such that for every `n`, `ρ(□_n)` is almost surely below
an integrable `Φ` with `E[Φ] ≤ C rⁿ`. -/
theorem exists_cubeRho_majorant_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ∃ Φ : Configuration d → ℝ,
      Integrable Φ (latticeBondLaw d p) ∧
      (∀ᵐ ω ∂(latticeBondLaw d p), cubeRho p ω ⟨n, 0⟩ ≤ Φ ω) ∧
      ∫ ω, Φ ω ∂(latticeBondLaw d p) ≤ C * r ^ n := by
  have hd0 : 0 < d := by omega
  obtain ⟨K₁, l₁, hK₁, hl₁0, hl₁1, hω⟩ :=
    exists_sum_integral_cubeOmega_single_le_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨C₁, hC₁, hFS⟩ := exists_integral_faceSizeSqSum_le hd hpc
  obtain ⟨C₂, hC₂, hmar⟩ := exists_integral_sum_margin_le hd hpc
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = 2 * ((d + 1).factorial : ℝ) * θ ^ (d + 1) := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i, ∑ j, |((cubeAhom (d := d) p)⁻¹) i j| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hS : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i| :=
    fun v => by rw [hSdef]; exact sum_abs_mulVec_le _ v
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ j : Fin d,
      -(-∑ i, (Pi.single j 1 : Fin d → ℝ) i * ((cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single j 1) i) :=
    ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact Finset.sum_nonneg fun j _ => by
      rw [neg_neg]
      exact sum_mul_inv_cubeAhom_mulVec_nonneg hd hpc _
  have hs3 : 1 < √(3 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = max l₁ (√(3 : ℝ))⁻¹ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_max_of_lt_left hl₁0
  have hr1 : r < 1 := by rw [hr]; exact max_lt hl₁1 (inv_lt_one_of_one_lt₀ hs3)
  refine ⟨d * K₁ + d ^ 3 * S * (1 + d + C₁ / 2 + 3 ^ d * (1 + d * C₂)) + d * c * C₃, r,
    by positivity, hr0, hr1, fun n => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set U : TriadicCube d := ⟨n, 0⟩ with hU
  set L : ℝ := (3 : ℝ) ^ n with hL
  have hL1 : 1 ≤ L := one_le_pow₀ (by norm_num)
  have hL0 : 0 < L := by positivity
  set t : ℝ := √L with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hL0
  have ht1 : 1 ≤ t := Real.one_le_sqrt.2 hL1
  have htt : t ^ 2 = L := Real.sq_sqrt hL0.le
  have hsize : (U.toIntegerCube.size : ℝ) = L := U.cast_size_toIntegerCube
  have hV : U.latticeVolume = L ^ d := rfl
  have hLd : L ^ d = L ^ (d - 1) * L := by rw [← pow_succ, Nat.sub_add_cancel hd0]
  have hLdm : 0 < L ^ (d - 1) := by positivity
  set u : ℝ := 1 / t with hu
  have hu0 : 0 ≤ u := by positivity
  have hur : u ≤ r ^ n := by
    have e : u = (√(3 : ℝ))⁻¹ ^ n := by rw [hu, ht, hL, sqrt_three_pow, one_div, inv_pow]
    rw [e, hr]
    exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) n
  have hLu : 1 / L ≤ u := by
    rw [hu, div_le_div_iff₀ hL0 ht0, one_mul, one_mul]
    nlinarith
  have hlr : l₁ ^ n ≤ r ^ n := by
    rw [hr]
    exact pow_le_pow_left₀ hl₁0.le (le_max_left _ _) n
  set a₁ : ℝ := d ^ 3 * S * (1 / L + 2 * d * L ^ (d - 1) / (2 * L ^ d) + 3 ^ d * u) with ha₁
  set a₂ : ℝ := d ^ 3 * S / (2 * L ^ d) with ha₂
  set a₃ : ℝ := d ^ 3 * S * 3 ^ d * t * d / L ^ d with ha₃
  set a₄ : ℝ := d * c / (3 * L) ^ (d + 1) with ha₄
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha₃0 : 0 ≤ a₃ := by positivity
  have ha₄0 : 0 ≤ a₄ := by positivity
  have hf : ∀ j, Integrable (fun ω => cubeOmega p ω U (Pi.single j 1)) μ := fun j =>
    integrable_cubeOmega hd hpc U _
  have hfs : Integrable (fun ω => (d : ℝ) * ∑ j, cubeOmega p ω U (Pi.single j 1)) μ :=
    (integrable_finsetSum _ fun j _ => hf j).const_mul _
  obtain ⟨hFSi, hFSb⟩ := hFS U
  obtain ⟨hMi0, hMb⟩ := hmar U
  have hMi : Integrable (fun ω => marginSizeSum ω U) μ := hMi0
  have hZi : Integrable (fun ω => ∑ x ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) μ :=
    (hmom (d + 1) U.toIntegerCube.vertices).1
  have hZb : ∫ ω, ∑ x ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1) ∂μ ≤ C₃ * L ^ d := by
    have h := (hmom (d + 1) U.toIntegerCube.vertices).2
    rw [U.card_toIntegerCube_vertices, hV, ← hC₃] at h
    exact h
  have hI1 : Integrable (fun ω => (d : ℝ) * ∑ j, cubeOmega p ω U (Pi.single j 1) + a₁) μ :=
    hfs.add (integrable_const _)
  have hI2 : Integrable (fun ω => (d : ℝ) * ∑ j, cubeOmega p ω U (Pi.single j 1) + a₁ +
      a₂ * faceSizeSqSum ω U) μ := hI1.add (hFSi.const_mul _)
  have hI3 : Integrable (fun ω => (d : ℝ) * ∑ j, cubeOmega p ω U (Pi.single j 1) + a₁ +
      a₂ * faceSizeSqSum ω U + a₃ * marginSizeSum ω U) μ := hI2.add (hMi.const_mul _)
  refine ⟨fun ω => (d : ℝ) * ∑ j, cubeOmega p ω U (Pi.single j 1) + a₁ +
      a₂ * faceSizeSqSum ω U + a₃ * marginSizeSum ω U +
      a₄ * ∑ x ∈ U.toIntegerCube.vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1),
    hI3.add (hZi.const_mul _), ?_, ?_⟩
  · filter_upwards [ae_partitionEvent hd hpc] with ω hP
    have hY := cubeComparisonError_le ω U
    have hYe : (d : ℝ) ^ 3 * S * (1 / (3 : ℝ) ^ U.scale + (2 * d *
        (U.toIntegerCube.size : ℝ) ^ (d - 1) + faceSizeSqSum ω U) / (2 * U.latticeVolume) +
        3 ^ d * (1 / √((3 : ℝ) ^ U.scale) + √((3 : ℝ) ^ U.scale) *
          (d * marginSizeSum ω U / U.latticeVolume))) =
        a₁ + a₂ * faceSizeSqSum ω U + a₃ * marginSizeSum ω U := by
      rw [hsize]
      change (d : ℝ) ^ 3 * S * (1 / L + (2 * d * L ^ (d - 1) + faceSizeSqSum ω U) /
        (2 * L ^ d) + 3 ^ d * (1 / t + t * (d * marginSizeSum ω U / L ^ d))) = _
      rw [ha₁, ha₂, ha₃, hu]
      ring
    have hYle : (d : ℝ) ^ 3 * S * cubeComparisonError ω U ≤
        a₁ + a₂ * faceSizeSqSum ω U + a₃ * marginSizeSum ω U := by
      rw [← hYe]
      exact mul_le_mul_of_nonneg_left hY (by positivity)
    have hZ0 : 0 ≤ a₄ * ∑ x ∈ U.toIntegerCube.vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1) :=
      mul_nonneg ha₄0 (Finset.sum_nonneg fun x _ => pow_nonneg (stoppingSize_nonneg _ _) _)
    by_cases hres : PartitionResolved ω U
    · have h1 := cubeRho_le_of_resolved hd0 p hP hres hS0 hS
      linarith
    · have hnot : ¬ (PartitionEvent ω ∧ PartitionResolved ω U) := fun h => hres h.2
      have h1 := cubeRho_le_zero_of_not hd hpc hnot
      have hZ1 := one_le_sum_size_div_of_not_resolved hP hres
      have hZe : ∑ x ∈ U.toIntegerCube.vertices,
          (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / (3 * 3 ^ U.scale)) ^ (d + 1) =
          (∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) /
              (3 * L) ^ (d + 1) := by
        rw [Finset.sum_div]
        simp only [div_pow]
        rfl
      have hfo : (d : ℝ) * ∑ j, cubeOmega p ω U (Pi.single j 1) = -(d * c) := by
        rw [Finset.sum_congr rfl fun j _ => cubeOmega_eq_of_not hnot (Pi.single j 1), hc]
        simp only [neg_neg, Finset.sum_neg_distrib]
        ring
      have hY0 : 0 ≤ a₁ + a₂ * faceSizeSqSum ω U + a₃ * marginSizeSum ω U :=
        (mul_nonneg (by positivity) (cubeComparisonError_nonneg ω U)).trans hYle
      have hdc : d * c ≤ a₄ * ∑ x ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1) := by
        have e : a₄ * ∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1) =
            d * c * ((∑ x ∈ U.toIntegerCube.vertices,
              TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) /
                (3 * L) ^ (d + 1)) := by
          rw [ha₄]
          ring
        rw [e]
        refine le_mul_of_one_le_right (by positivity) ?_
        rw [← hZe]
        exact hZ1
      linarith
  · rw [integral_add hI3 (hZi.const_mul _), integral_add hI2 (hMi.const_mul _),
      integral_add hI1 (hFSi.const_mul _), integral_add hfs (integrable_const _), integral_const,
      probReal_univ, one_smul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun j _ => hf j]
    have h1 := hω n
    have h2 : a₂ * ∫ ω, faceSizeSqSum ω U ∂μ ≤ a₂ * (C₁ * L ^ (d - 1)) := by
      rw [← hsize]
      exact mul_le_mul_of_nonneg_left hFSb ha₂0
    have h3 : a₃ * ∫ ω, marginSizeSum ω U ∂μ ≤ a₃ * (C₂ * L ^ (d - 1)) :=
      mul_le_mul_of_nonneg_left hMb ha₃0
    have h4 := mul_le_mul_of_nonneg_left hZb ha₄0
    have hT1 : a₁ ≤ d ^ 3 * S * (1 + d + 3 ^ d) * u := by
      have hq : 2 * d * L ^ (d - 1) / (2 * L ^ d) = d * (1 / L) := by
        rw [hLd]
        field_simp
      rw [ha₁, hq]
      have k1 := mul_le_mul_of_nonneg_left hLu (Nat.cast_nonneg d)
      have k : 1 / L + d * (1 / L) + 3 ^ d * u ≤ (1 + d + 3 ^ d) * u := by linarith
      exact (mul_le_mul_of_nonneg_left k (by positivity : (0 : ℝ) ≤ d ^ 3 * S)).trans_eq
        (by ring)
    have hT2 : a₂ * (C₁ * L ^ (d - 1)) ≤ d ^ 3 * S * (C₁ / 2) * u := by
      have e : a₂ * (C₁ * L ^ (d - 1)) = d ^ 3 * S * (C₁ / 2) * (1 / L) := by
        rw [ha₂, hLd]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hLu (by positivity)
    have hT3 : a₃ * (C₂ * L ^ (d - 1)) = d ^ 3 * S * 3 ^ d * (d * C₂) * u := by
      have htL : t / L = u := by
        rw [hu, ← htt]
        field_simp
      rw [ha₃, hLd, ← htL]
      field_simp
    have hT4 : a₄ * (C₃ * L ^ d) ≤ d * c * C₃ * u := by
      have e : a₄ * (C₃ * L ^ d) = d * c * C₃ * (1 / L) * (L ^ (d + 1) / (3 * L) ^ (d + 1)) := by
        rw [ha₄, pow_succ L d]
        field_simp
      have hk : L ^ (d + 1) / (3 * L) ^ (d + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact pow_le_pow_left₀ hL0.le (by linarith) _
      rw [e]
      have hdc0 : 0 ≤ d * c * C₃ * (1 / L) := by positivity
      calc d * c * C₃ * (1 / L) * (L ^ (d + 1) / (3 * L) ^ (d + 1))
          ≤ d * c * C₃ * (1 / L) * 1 := mul_le_mul_of_nonneg_left hk hdc0
        _ ≤ d * c * C₃ * u := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hLu (by positivity)
    have hK : (d : ℝ) * (K₁ * l₁ ^ n) ≤ d * K₁ * r ^ n := by
      have := mul_le_mul_of_nonneg_left hlr (by positivity : (0 : ℝ) ≤ d * K₁)
      linarith
    have hfinal : (d : ℝ) * ∑ j, ∫ ω, cubeOmega p ω U (Pi.single j 1) ∂μ ≤ d * (K₁ * l₁ ^ n) :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
    have hur' : (d ^ 3 * S * (1 + d + C₁ / 2 + 3 ^ d * (1 + d * C₂)) + d * c * C₃) * u ≤
        (d ^ 3 * S * (1 + d + C₁ / 2 + 3 ^ d * (1 + d * C₂)) + d * c * C₃) * r ^ n :=
      mul_le_mul_of_nonneg_left hur (by positivity)
    linarith [hfinal, hK, hT1, h2, hT2, h3, hT3, h4, hT4, hur']

end Rigidity.Percolation
