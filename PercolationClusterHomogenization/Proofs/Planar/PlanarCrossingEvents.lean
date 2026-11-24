import LatticeProb.Network.Flow
import PercolationClusterHomogenization.Proofs.Planar.WindingNumber
import PercolationClusterHomogenization.External.WellConnected
import PercolationClusterHomogenization.Proofs.Lattice.ChemicalDistance
import PercolationClusterHomogenization.Proofs.Planar.LoopFromCrossings
import PercolationClusterHomogenization.Proofs.Percolation.KestenCrossing
import LatticeProb.Prob.Percolation.LSSThinInstantiation
import LatticeProb.Prob.Percolation.LSSThinIsIncreasing
import LatticeProb.Prob.Strassen.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PercolationClusterHomogenization.External.KestenCrossing
import PercolationClusterHomogenization.Proofs.Percolation.PlanarBoxGeometry

/-!
# A union bound

A union over a finite index set of sets of measure at most `f` has measure at most `|S| f`.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S3
open scoped ENNReal

namespace Rigidity.Proofs.Section5

/-- A union over a finite index set of sets of measure at most `f` has measure at most `|S| f`. -/
theorem measure_biUnion_le_card_mul {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Finset ι) (A : ι → Set α) {f : ℝ} (h : ∀ i ∈ S, μ (A i) ≤ ENNReal.ofReal f) :
    μ (⋃ i ∈ S, A i) ≤ ENNReal.ofReal (S.card * f) := by
  calc μ (⋃ i ∈ S, A i) ≤ ∑ i ∈ S, μ (A i) := measure_biUnion_finset_le S A
    _ ≤ ∑ _i ∈ S, ENNReal.ofReal f := Finset.sum_le_sum h
    _ = ENNReal.ofReal (S.card * f) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

end Rigidity.Proofs.Section5
