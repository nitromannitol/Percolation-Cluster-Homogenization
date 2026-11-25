import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorInput
import PercolationClusterHomogenization.Proofs.Regularity.CorrectorSublinearFromRegularity

/-!
# Theorem 2 (iii) at `k = 1` and (1.18) with a minimal scale in every dimension

With the qualitative corrector input proved in every dimension
(`GeneralDim.supercriticalBondCorrectorInput_holds`), the regularity of order one at the origin of
Armstrong and Dario (arXiv:1609.09431v2, Theorem 2 (iii) at `k = 1`,
`Rigidity.External.ArmstrongDarioOrderOneOrigin`) and the sublinearity (1.18) with a minimal scale
of class `O_s` (`CorrectorSublinearL2At`) hold in every dimension `d ≥ 2` with no hypothesis, by
`armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput` and
`correctorSublinearL2At_of_correctedPlanes`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in every dimension `d ≥ 2`**,
with no hypothesis. -/
theorem armstrongDarioOrderOneOrigin_holds : ArmstrongDarioOrderOneOrigin :=
  armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput
    GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Armstrong–Dario, (1.18), with a minimal scale of class `O_s`**, in every dimension `d ≥ 2`,
with no hypothesis. -/
theorem correctorSublinearL2At_holds {d : ℕ} [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : CorrectorSublinearL2At d p :=
  correctorSublinearL2At_of_correctedPlanes hd hpc hp1 (by
    filter_upwards [GeneralDim.correctedPlaneExistence_holds hd p hpc hp1] with ω hω h q _
    exact hω h q)

end Rigidity.Proofs.Regularity
