import PercolationClusterHomogenization.Proofs.Density.ClusterDensityMean

/-!
# Boundedness of cluster-density fluctuations

The normalized infinite-cluster count is between zero and one. This supplies the finitely many
initial scales in stretched-exponential density estimates.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {p : unitInterval}

/-- The normalized cluster-density fluctuation has absolute value at most one. -/
theorem abs_centered_clusterDensity_le_one (p : unitInterval) (m : ℕ) (k : Vertex d)
    (ω : Configuration d) :
    |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((triadicCube d m k).ncard : ℝ) - theta d p| ≤ 1 := by
  classical
  have hden : 0 < ((triadicCube d m k).ncard : ℝ) := by
    rw [ncard_triadicCube]
    positivity
  have hcard : infiniteClusterCount (triadicCube d m k) ω ≤ (triadicCube d m k).ncard := by
    rw [infiniteClusterCount_triadicCube, ncard_triadicCube, ← card_triadicCubeFinset m k]
    exact Finset.card_filter_le _ _
  have hcount : (infiniteClusterCount (triadicCube d m k) ω : ℝ) ≤
      ((triadicCube d m k).ncard : ℝ) := by exact_mod_cast hcard
  have hlo : 0 ≤ (infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((triadicCube d m k).ncard : ℝ) := by positivity
  have hhi : (infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((triadicCube d m k).ncard : ℝ) ≤ 1 := (div_le_one hden).2 hcount
  rw [abs_le]
  constructor <;> linarith [theta_nonneg d p, theta_le_one d p]

end Rigidity.Proofs.S2
