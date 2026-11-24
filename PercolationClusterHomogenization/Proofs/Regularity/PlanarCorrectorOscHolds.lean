import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorOsc
import LatticeProb.External.GreenColumnExistence
import LatticeProb.External.GreenQuantitative
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.External.SupercriticalBondUniquenessInput
import LatticeProb.Graph.CarneVaropoulos
import LatticeProb.Graph.HeatVanishing
import LatticeProb.Graph.OnDiagonal
import LatticeProb.Network.FiniteEnergyVoltage
import LatticeProb.Network.FirstPassage
import LatticeProb.Network.Flow
import LatticeProb.Network.VoltageConnected
import LatticeProb.Prob.Percolation.ContinuumGreen
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.GreenColumnEvent
import LatticeProb.Prob.Percolation.LSSThinIsIncreasing
import LatticeProb.Prob.Percolation.LatticeBondErgodicity
import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.LatticeClusterL2
import LatticeProb.Prob.Percolation.LatticeLocalGradient
import LatticeProb.Prob.Percolation.LatticeOrderZeroApproximation
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import LatticeProb.Prob.Percolation.LatticeUniqueClusterEvent
import LatticeProb.Prob.Percolation.MeasurableRootedPlane
import LatticeProb.Prob.Percolation.OpenComponentTranslation
import LatticeProb.Prob.Percolation.OpenGraphTranslation
import LatticeProb.Prob.Percolation.RootedCorrectedPlaneBorel
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable
import LatticeProb.Prob.Strassen.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Connected.Basic
import PercolationClusterHomogenization.Proofs.Lattice.ConfigurationExtension
import PercolationClusterHomogenization.Proofs.Planar.WindingNumber
import PercolationClusterHomogenization.External.CorrectorQuantitative
import PercolationClusterHomogenization.External.PlanarInputs
import PercolationClusterHomogenization.Percolation.TriadicExceptionalSupremum
import PercolationClusterHomogenization.Percolation.TriadicStableAncestors
import PercolationClusterHomogenization.Proofs.Partition.AlmostSure
import PercolationClusterHomogenization.Proofs.Partition.Paths
import PercolationClusterHomogenization.Proofs.Partition.Translation
import PercolationClusterHomogenization.Proofs.Percolation.PlanarAnchorTranslation
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMuMeasurable
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuStationarity
import PercolationClusterHomogenization.Proofs.Percolation.PlanarPartition
import PercolationClusterHomogenization.Proofs.Percolation.PlanarTranslation
import PercolationClusterHomogenization.Proofs.Percolation.PlanarWindows
import PercolationClusterHomogenization.Proofs.Percolation.SupercriticalUniqueness
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationHolds
import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderOneDimension
import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderOneOriginInputs
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityBounds
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityFromDarioGu
import PercolationClusterHomogenization.Proofs.Planar.PlanarCrossingEvents
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSubaddOsMain

/-!
# Proposition 5.2 for `ν` in the form `O_s` in dimension two

`planarNuSubaddOsTwo_holds`: the part on `ν` of Proposition 5.2 of Armstrong and Dario in the form
`O_s`, for `p > p_c(2)`, from `Rigidity.Proofs.Cluster.planar_subadd_os`.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb.Percolation Rigidity.External

/-- **Armstrong–Dario, Proposition 5.2 for `ν` in the form `O_s`, in dimension two**, for
`p > p_c(2)`: the part on `ν` of `planar_subadd_os`, with `Z_V` the error `planarSubaddErr p V`. -/
theorem planarNuSubaddOsTwo_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarNuSubaddOsTwo p := by
  obtain ⟨r, α, C, hr, hα, hC, h⟩ := Rigidity.Proofs.Cluster.planar_subadd_os hpc
  exact ⟨r, α, C, hr, hα, hC, fun V => ⟨Rigidity.Proofs.Cluster.planarSubaddErr p V, (h V).1,
    (h V).2.1, (h V).2.2.1, fun ω ξ => ((h V).2.2.2 ω 0 ξ).2⟩⟩

end Rigidity.Proofs.Regularity
