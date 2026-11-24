/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/ProductMeasure/FiniteInterpolationMeasure.lean, Apache License 2.0;
   changes: the module path is PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure in place of OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure, and the module paths of local imports are changed in the same way; the import of OAI.Probability.CriticalPercolation.Criticality.FiniteInterpolationUniform (not copied here) is replaced by the imports of the copied modules it reaches,
   namely PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper, PercolationClusterHomogenization.Vendor.CriticalPercolation.Clusters.ClusterTail, PercolationClusterHomogenization.Vendor.CriticalPercolation.Entropy.BinaryLaw, PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.ExpectClosedFlip, PercolationClusterHomogenization.Vendor.CriticalPercolation.Modular.WeightedCauchy, PercolationClusterHomogenization.Vendor.CriticalPercolation.Model, PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.Delta, PercolationClusterHomogenization.Vendor.CriticalPercolation.Exploration.SearchTree, PercolationClusterHomogenization.Vendor.CriticalPercolation.Exploration.ClosedFresh, PercolationClusterHomogenization.Vendor.CriticalPercolation.GraphGeometry.Link, PercolationClusterHomogenization.Vendor.CriticalPercolation.GraphGeometry.VertexBall, PercolationClusterHomogenization.Vendor.CriticalPercolation.Clusters.ClusterObject, PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.Density;
   the unused declarations `finite_interpolation_measure` (they need modules not copied here) are omitted; a module docstring is added; in proofs, `Set.mem_ofPred_eq` is replaced by `Set.mem_setOf_eq`; statements of the declarations kept are unchanged. -/
import Mathlib
import PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import PercolationClusterHomogenization.Vendor.CriticalPercolation.Clusters.ClusterTail
import PercolationClusterHomogenization.Vendor.CriticalPercolation.Entropy.BinaryLaw
import PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.ExpectClosedFlip
import PercolationClusterHomogenization.Vendor.CriticalPercolation.Modular.WeightedCauchy
import PercolationClusterHomogenization.Vendor.CriticalPercolation.Model
import PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.Delta
import PercolationClusterHomogenization.Vendor.CriticalPercolation.Exploration.SearchTree
import PercolationClusterHomogenization.Vendor.CriticalPercolation.Exploration.ClosedFresh
import PercolationClusterHomogenization.Vendor.CriticalPercolation.GraphGeometry.Link
import PercolationClusterHomogenization.Vendor.CriticalPercolation.GraphGeometry.VertexBall
import PercolationClusterHomogenization.Vendor.CriticalPercolation.Clusters.ClusterObject
import PercolationClusterHomogenization.Vendor.CriticalPercolation.ProductMeasure.Density

/-!
# Finite Interpolation Measure

Results on finite interpolation measure for Bernoulli percolation on bond graphs.
-/

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*} [Fintype E]

lemma prob_eq_real (q : E → unitInterval) (A : Set (Set E)) :
    FiniteProduct.prob (fun e => bitWeight (q e)) (fun ω => ω ∈ A) = (law q).real A := by
  rw [real_eq_expect_indicator]
  unfold FiniteProduct.prob
  rfl

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoClusterEvent (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩ G.clusterTail u s ∩ G.clusterTail v s

lemma measurableSet_twoClusterEvent [Countable V] [Countable E] (u v : V) (s : ℕ) :
    MeasurableSet (G.twoClusterEvent u v s) := by
  exact ((G.measurable_reachable u v).setOf.compl.inter
    (G.measurableSet_clusterTail u s)).inter (G.measurableSet_clusterTail v s)

lemma clusterTail_iff_card [Fintype V] (ω : Set E) (u : V) (s : ℕ) :
    ω ∈ G.clusterTail u s ↔ s ≤ (G.cluster ω u).toFinset.card := by
  constructor
  · rintro ⟨K,hK,hsub,hs⟩
    exact hs.trans (by simpa only [Set.ncard_eq_toFinset_card'] using Set.ncard_le_ncard hsub)
  · intro hs
    exact ⟨G.cluster ω u, Set.toFinite _, Set.Subset.rfl, by simpa only [Set.ncard_eq_toFinset_card'] using hs⟩

lemma twoClusterEvent_iff_endpoint [Fintype V] (ω : Set E) (u v : V) (s : ℕ) :
    ω ∈ G.twoClusterEvent u v s ↔ BinaryLaw.endpointEvent G u v s ω := by
  simp only [twoClusterEvent, Set.mem_inter_iff, Set.mem_setOf_eq,
    clusterTail_iff_card, BinaryLaw.endpointEvent, and_assoc]

lemma finite_endpoint_prob [Fintype V] [Fintype E] (p : unitInterval) (u v : V) (s : ℕ) :
    FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
      (BinaryLaw.endpointEvent G u v s) = (G.law p).real (G.twoClusterEvent u v s) := by
  rw [law, ← BernoulliProduct.law_const, ← BernoulliProduct.prob_eq_real]
  congr 1
  funext ω
  exact propext (G.twoClusterEvent_iff_endpoint ω u v s).symm

end BondGraph
end CriticalPercolation
end
end
end

end OAI
