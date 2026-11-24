import PercolationClusterHomogenization.Proofs.Density.RescaleExponentialMoment

/-!
# Planar density resampling energy with a unit exponential moment

The resampling energy obeys the exponential-moment convention for stochastic bounds, uniformly
at inverse-volume scale.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The total squared influence of the normalized triadic cluster density. -/
noncomputable def planarDensityResamplingEnergy (m : ℕ) (k : Vertex 2)
    (q : Configuration 2 × Configuration 2) : ℝ :=
  ∑' e : Bond 2,
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ)| ^ 2

end Rigidity.Proofs.S2
