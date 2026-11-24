import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth
import PercolationClusterHomogenization.External.CorrectorQuantitative
import PercolationClusterHomogenization.Proofs.Regularity.ClusterOrderOne
import PercolationClusterHomogenization.Proofs.Regularity.InfiniteClusterBalls
import LatticeProb.External.SupercriticalBondCorrectorInput

/-!
# Regularity of order one at the origin from the mesoscopic estimate at degree two

Armstrong and Dario (arXiv:1609.09431v2), Lemma 7.3, prove the mesoscopic estimate (7.18): there
are `s, δ > 0`, a random scale `𝒳 ≤ O_s(C)` and, for each `k`, a constant `C(k)` such that for
`R ≥ 2 𝒳`, `u ∈ 𝒜(𝒞_∞ ∩ B_R)` and `r ∈ [𝒳, R / 2]`,
`inf_{w ∈ Ā_k} |B_r|^{-1/2} ‖u - w‖_{L²(𝒞_∞ ∩ B_r)} ≤
  C (r / R)^{k+1} inf_{w ∈ Ā_k} |B_R|^{-1/2} ‖u - w‖_{L²(𝒞_∞ ∩ B_R)} +
  C r^{-δ} (r / R) |B_R|^{-1/2} ‖u‖_{L²(𝒞_∞ ∩ B_R)}`.
`ArmstrongDarioMesoscopicDegreeTwo` is this statement at `k = 2` for bond percolation, at the
origin, with `Ā_2` the harmonic quadratic polynomials (`clusterHarmonicQuadratic`; the homogenized
matrix is `σ² I / 2`, §1.1 of the source) and `|B_r| = r^d` (`clusterBallVolumeL2`); the Lebesgue
measure `ω_d r^d` gives the same statement, the factor `ω_d^{-1/2}` appearing on both sides.

`armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo` proves Theorem 2 (iii) at `k = 1`,
`Rigidity.External.ArmstrongDarioOrderOneOrigin`, from this estimate, the quantitative bound on the
first-order correctors `Rigidity.External.CorrectorQuantitativeInput` (with exponent `1/2`) and the
existence of the corrected planes in `LatticeProb.External.SupercriticalBondCorrectorInput`, by the
endpoint iteration `exists_forall_le_of_orderOneEndpoint`: the corrected planes of slope `eᵢ`,
normalized at a vertex of `𝒞_∞ ∩ B_𝒳`, lift the affine functions with relative error at most
`C t^{-1/2}` on `B_t`, and the density of the infinite cluster in cubes
(`Rigidity.Proofs.S2.cluster_density_concentration`) gives the comparison of the sizes of polynomials
with the normalized norms. The source deduces Theorem 2 from Lemma 7.3 by the argument of
Armstrong, Kuusi and Mourrat, Proposition 3.1, which lifts the polynomials of degree two; the
endpoint iteration lifts only the affine functions.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ} {ω : Configuration d}

/-- The normalization `r^{-d/2} ‖f‖_{L²(C ∩ B_r)}` of Armstrong–Dario, Lemma 7.3. -/
noncomputable def clusterBallVolumeL2 (C : OpenComponent ω) (r : ℝ) (f : C → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ componentEuclideanBall C 0 r, f x ^ 2) / r ^ d)

theorem clusterBallVolumeL2_eq (C : OpenComponent ω) {r : ℝ} (hr : 0 ≤ r) (f : C → ℝ) :
    clusterBallVolumeL2 C r f =
      Real.sqrt (((componentEuclideanBall C 0 r).card : ℝ) / r ^ d) * componentBallL2 C 0 r f := by
  unfold clusterBallVolumeL2 componentBallL2
  rw [← Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _))]
  congr 1
  rcases Nat.eq_zero_or_pos (componentEuclideanBall C 0 r).card with h0 | h0
  · rw [Finset.card_eq_zero.1 h0]
    simp
  · have : ((componentEuclideanBall C 0 r).card : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp

/-- **Passage from the normalization of Lemma 7.3 to the normalized norms**: under the volume
comparison of the cluster balls, (7.18) for `clusterBallVolumeL2` gives it for `componentBallL2`
with the constant multiplied by `√K`. -/
theorem ballExcess_le_of_clusterBallVolumeL2 (C : OpenComponent ω) {X R K A₀ δ v r : ℝ}
    {w : C → ℝ} (hK : 0 ≤ K) (hvol : ClusterBallVolumeComparison C 0 X R K) (hXv : X ≤ v)
    (hvr : v ≤ r) (hrR : r ≤ R) (hv0 : 0 < v) (hcard : 0 < (componentEuclideanBall C 0 v).card)
    (h : (⨅ q : clusterHarmonicQuadratic C, clusterBallVolumeL2 C v (w - q)) ≤
      A₀ * (v / r) ^ 3 * (⨅ q : clusterHarmonicQuadratic C, clusterBallVolumeL2 C r (w - q)) +
        A₀ * v ^ (-δ) * (v / r) * clusterBallVolumeL2 C r w) :
    ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) v w ≤
      Real.sqrt K * max A₀ 1 * (v / r) ^ 3 *
          ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) r w +
        Real.sqrt K * max A₀ 1 * v ^ (-δ) * (v / r) * componentBallSeminorm C 0 r w := by
  have hr0 : 0 < r := hv0.trans_le hvr
  set N := componentBallSeminorm C 0 with hN
  set P := clusterHarmonicQuadratic C with hP
  set c : ℝ → ℝ := fun t => Real.sqrt (((componentEuclideanBall C 0 t).card : ℝ) / t ^ d) with hc
  have hinf : ∀ t, 0 ≤ t → (⨅ q : P, clusterBallVolumeL2 C t (w - q)) = c t * ballExcess N P t w := by
    intro t ht
    rw [ballExcess, Real.mul_iInf_of_nonneg (Real.sqrt_nonneg _)]
    exact iInf_congr fun q => by rw [clusterBallVolumeL2_eq C ht, hN, componentBallSeminorm_apply]
  rw [hinf v hv0.le, hinf r hr0.le, clusterBallVolumeL2_eq C hr0.le] at h
  set Dv := ballExcess N P v w
  set Dr := ballExcess N P r w
  set Nr := componentBallL2 C 0 r w
  have hDr : 0 ≤ Dr := ballExcess_nonneg _ _ _ _
  have hNr : 0 ≤ Nr := componentBallL2_nonneg _ _ _ _
  have hcv : 0 < c v := by
    apply Real.sqrt_pos.2
    exact div_pos (by exact_mod_cast hcard) (by positivity)
  have hcr : c r ≤ Real.sqrt K * c v := by
    have hcount := hvol v r hXv hvr hrR
    have h1 : ((componentEuclideanBall C 0 r).card : ℝ) / r ^ d ≤
        K * (((componentEuclideanBall C 0 v).card : ℝ) / v ^ d) := by
      rw [div_le_iff₀ (by positivity)]
      calc ((componentEuclideanBall C 0 r).card : ℝ) ≤
            K * (r / v) ^ d * ((componentEuclideanBall C 0 v).card : ℝ) := hcount
        _ = K * (((componentEuclideanBall C 0 v).card : ℝ) / v ^ d) * r ^ d := by
            rw [div_pow]; field_simp
    calc c r ≤ Real.sqrt (K * (((componentEuclideanBall C 0 v).card : ℝ) / v ^ d)) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt K * c v := Real.sqrt_mul hK _
  have hA : A₀ ≤ max A₀ 1 := le_max_left _ _
  have hA1 : 0 ≤ max A₀ 1 := zero_le_one.trans (le_max_right _ _)
  have hvr0 : 0 ≤ v / r := div_nonneg hv0.le hr0.le
  have hδv : 0 ≤ v ^ (-δ) := Real.rpow_nonneg hv0.le _
  have hcr0 : 0 ≤ c r := Real.sqrt_nonneg _
  have h1 : A₀ * (v / r) ^ 3 * (c r * Dr) ≤ max A₀ 1 * (v / r) ^ 3 * (Real.sqrt K * c v * Dr) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hA (by positivity))
      (mul_le_mul_of_nonneg_right hcr hDr) (mul_nonneg hcr0 hDr) (by positivity)
  have h2 : A₀ * v ^ (-δ) * (v / r) * (c r * Nr) ≤
      max A₀ 1 * v ^ (-δ) * (v / r) * (Real.sqrt K * c v * Nr) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hδv) hvr0)
      (mul_le_mul_of_nonneg_right hcr hNr) (mul_nonneg hcr0 hNr) (by positivity)
  have h3 : c v * Dv ≤ c v * (Real.sqrt K * max A₀ 1 * (v / r) ^ 3 * Dr +
      Real.sqrt K * max A₀ 1 * v ^ (-δ) * (v / r) * Nr) := by
    have e : c v * (Real.sqrt K * max A₀ 1 * (v / r) ^ 3 * Dr +
        Real.sqrt K * max A₀ 1 * v ^ (-δ) * (v / r) * Nr) =
        max A₀ 1 * (v / r) ^ 3 * (Real.sqrt K * c v * Dr) +
          max A₀ 1 * v ^ (-δ) * (v / r) * (Real.sqrt K * c v * Nr) := by ring
    rw [e]
    linarith only [h, h1, h2]
  rw [hN, componentBallSeminorm_apply]
  exact le_of_mul_le_mul_left h3 hcv

theorem sum_single_mul (i : Fin d) (f : Fin d → ℝ) :
    ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * f j = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

end Rigidity.Proofs.Regularity
