import LatticeProb.Prob.Percolation.LSSThinInstantiation
import LatticeProb.Prob.Percolation.LSSThinIsIncreasing
import LatticeProb.Prob.Strassen.Defs
import PercolationClusterHomogenization.Proofs.Planar.WindingNumber
import PercolationClusterHomogenization.External.KestenCrossing
import PercolationClusterHomogenization.External.WellConnected

/-!
# Site percolation on the renormalized planar lattice

The open subgraph of a site configuration of `ℤ²`, the event that a site lies in an infinite open
cluster, and the statement that this event is measurable.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- The open subgraph of a site configuration `η` of the renormalized lattice `ℤ²`: two nearest
neighbours are adjacent when both are open. -/
def siteOpenGraph (η : PlanarCarrier → Bool) : SimpleGraph PlanarCarrier where
  Adj z w := |z.1 - w.1| + |z.2 - w.2| = 1 ∧ η z = true ∧ η w = true
  symm := ⟨fun z w h => ⟨by rw [abs_sub_comm w.1, abs_sub_comm w.2]; exact h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun z h => by simp at h⟩

/-- The site `z` of the renormalized lattice lies in an infinite open cluster of `η`. -/
def InInfiniteSiteCluster (η : PlanarCarrier → Bool) (z : PlanarCarrier) : Prop :=
  η z = true ∧ {w | (siteOpenGraph η).Reachable z w}.Infinite

/-- Step `step:5.21-cluster-measurable`: the event that a site lies in an infinite open cluster
is measurable. -/
def InfiniteClusterMeasurableStep : Prop :=
  ∀ z : PlanarCarrier, MeasurableSet {η : PlanarCarrier → Bool | InInfiniteSiteCluster η z}

end Rigidity.Steps.Section5
