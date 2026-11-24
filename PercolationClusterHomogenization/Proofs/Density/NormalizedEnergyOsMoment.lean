import PercolationClusterHomogenization.Proofs.Density.RescaleExponentialMoment

/-!
# The resampling energy of the normalized planar density

`planarDensityResamplingEnergy`: the total squared influence of the normalized triadic cluster
density in the plane.
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
