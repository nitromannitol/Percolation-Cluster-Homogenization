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
# Crossing events at dyadic scales

`CrossingGood ω L w H N` collects the crossings and well-connected cubes which the flow
construction of `CrossingFlow.lean` uses inside `[-L, L]²`: open horizontal crossings of all the
rectangles `[-L, L] × [r, r + w]`, open vertical crossings of all the rectangles
`[c, c + w] × [-L, L]`, `-L ≤ r, c ≤ L`, and for every centre `z ∈ [-L, L]²` open crossings of the
rectangles `[z₀, z₀ + w] × [z₁, z₁ + H]` (vertically) and `[z₀, z₀ + H] × [z₁, z₁ + w]`
(horizontally) and well-connectedness of the cube `z + Q_N`.

Kesten's rectangle crossing estimate and planar well-connectedness bound the probability of the
complement by a union bound. With `L = 4^m`, `w = m²`, `H = 2^m (m² + 1)` and `N = m^q`, `q s ≥ 2`,
these bounds are summable in `m`, so the event holds for all large `m`, almost surely.
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
