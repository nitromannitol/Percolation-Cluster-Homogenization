import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationInputs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderOneOriginInputs
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarTheoremOneHolds
import PercolationClusterHomogenization.Proofs.Cluster.PlanarMinimalScales

/-!
# Lemma 7.1 and Theorem 2 (iii) at `k = 0` in dimension two

For `p_c(2) < p < 1` and with no further hypothesis: the minimal scales of the planar partition and
Theorem 1 in the forms used for Lemma 7.1 (`planarMinimalScalesTwo_holds`,
`planarHomogenizationErrorTwo_holds`), the estimates on squares of the proof of Lemma 7.1
(`planarSquareEstimatesTwo_holds`), Lemma 7.1 of Armstrong and Dario
(`planarHarmonicApproximationTwo_holds`) and the order-zero regularity, Theorem 2 (iii) at `k = 0`
(`armstrongDarioOrderZeroTwo_holds`).
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb.Percolation Rigidity.External

/-- The minimal scales of the planar partition, in the form used for Lemma 7.1, for `p > p_c(2)`. -/
theorem planarMinimalScalesTwo_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarMinimalScalesTwo p :=
  Rigidity.Proofs.Cluster.planarMinimalScales_holds hpc

/-- Theorem 1 in dimension two, in the form used for Lemma 7.1, for `p > p_c(2)` and `p' > 2`. -/
theorem planarHomogenizationErrorTwo_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {p' : ℝ} (hp' : 2 < p') :
    PlanarHomogenizationErrorTwo p p' :=
  Rigidity.Dirichlet.planarHomogenizationError_holds hpc hp'

/-- **The estimates on squares of the proof of Lemma 7.1**, for `p_c(2) < p < 1`, with no further
hypothesis. -/
theorem planarSquareEstimatesTwo_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : PlanarSquareEstimatesTwo p :=
  planarSquareEstimatesTwo_of_parts
    (planarHarmonicDistTwo_of_homogenizationError hpc hp1 (planarMinimalScalesTwo_holds hpc)
      fun _ hp' => planarHomogenizationErrorTwo_holds hpc hp')
    (planarCoarseComparisonTwo_of_minimalScales hpc hp1 (planarMinimalScalesTwo_holds hpc))
    (planarCoarseBoundTwo_of_minimalScales hpc hp1 (planarMinimalScalesTwo_holds hpc))

/-- **Armstrong–Dario, Lemma 7.1, in dimension two**, with no hypothesis. -/
theorem planarHarmonicApproximationTwo_holds : PlanarHarmonicApproximationTwo :=
  planarHarmonicApproximationTwo_of_inputs (fun _ hpc _ => planarMinimalScalesTwo_holds hpc)
    fun _ hpc _ _ hp' => planarHomogenizationErrorTwo_holds hpc hp'

/-- **Armstrong–Dario, Theorem 2 (iii) for `k = 0`, in dimension two**, with no hypothesis. -/
theorem armstrongDarioOrderZeroTwo_holds : ArmstrongDarioOrderZeroTwo :=
  armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation planarHarmonicApproximationTwo_holds

end Rigidity.Proofs.Regularity
