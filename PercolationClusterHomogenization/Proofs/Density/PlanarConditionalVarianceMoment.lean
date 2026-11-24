import LatticeProb.Prob.EfronSteinCountable
import PercolationClusterHomogenization.Proofs.Density.BernoulliRealEncoding
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityBounds
import PercolationClusterHomogenization.Proofs.Density.ConditionalInfluenceExponential

/-!
# The centered planar density in the real encoding

`planarDensityRealObservable`: the centered planar cluster density in the real Bernoulli product
encoding of the configuration.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External

/-- Centered planar density in the real Bernoulli product encoding. -/
noncomputable def planarDensityRealObservable (p : unitInterval) (m : ℕ) (k : Vertex 2)
    (ω : Bond 2 → ℝ) : ℝ :=
  (infiniteClusterCount (triadicCube 2 m k) (bernoulliRealConfiguration ω) : ℝ) /
    ((triadicCube 2 m k).ncard : ℝ) - theta 2 p

end Rigidity.Proofs.S2
