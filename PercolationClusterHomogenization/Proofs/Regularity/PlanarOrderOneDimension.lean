import PercolationClusterHomogenization.Proofs.Regularity.OrderOneLift
import PercolationClusterHomogenization.Proofs.Regularity.PlanarAffineApproximationHolds

/-!
# The mesoscopic estimate of degree two in the plane

The statement `MesoscopicDegreeTwoPlanarInput` of Lemma 7.3 of Armstrong and Dario, (7.18) at
`k = 2`, in the plane, and the lift `(a, ξ) ↦ a + Σ ξᵢ gᵢ` as a linear map.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in the plane**: the statement of
`ArmstrongDarioMesoscopicDegreeTwo` for `d = 2`. -/
def MesoscopicDegreeTwoPlanarInput : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
  ∃ s C₀ δ : ℝ, 0 < s ∧ 0 < C₀ ∧ 0 < δ ∧
  ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s C₀ ∧
  ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
      (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
        (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
          w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
        componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
      ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
        (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
            clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) ≤
          C * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
              clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w)) +
            C * r ^ (-δ) * (r / R) * clusterBallVolumeL2 (uniqueInfiniteComponent h) R u

theorem mesoscopicDegreeTwoPlanarInput_of_mesoscopicDegreeTwo
    (h : ArmstrongDarioMesoscopicDegreeTwo) : MesoscopicDegreeTwoPlanarInput :=
  h 2 le_rfl

/-- The lift `(a, ξ) ↦ a + Σ ξᵢ gᵢ` as a linear map. -/
noncomputable def clusterLiftLinear {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (g : Fin d → C → ℝ) : (ℝ × EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (C → ℝ) where
  toFun := clusterLiftMap C g
  map_add' := map_add (clusterLiftMap C g)
  map_smul' c ℓ := by
    funext x
    show c * ℓ.1 + ∑ i, (c • ℓ.2) i * g i x = c * (ℓ.1 + ∑ i, ℓ.2 i * g i x)
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.smul_apply, smul_eq_mul, mul_assoc]

end Rigidity.Proofs.Regularity
