import PercolationClusterHomogenization.Proofs.Density.IntegratedEnergySeries

/-!
# Exponential moments of averaged planar influences

The sum of the independent-copy averaged squared influences satisfies the exponential-moment
convention for stochastic bounds.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The sum of squared resampling influences averaged over an independent configuration. -/
noncomputable def planarConditionalInfluenceEnergy (p : unitInterval) (m : ℕ) (k : Vertex 2)
    (ω : Configuration 2) : ℝ :=
  ∑' e : Bond 2, ∫ η : Configuration 2,
    |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p)

end Rigidity.Proofs.S2
