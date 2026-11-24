import LatticeProb.External.SupercriticalBondUniquenessInput
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.GreenColumnHarmonic
import LatticeProb.Prob.Percolation.GreenDifferenceBounds
import LatticeProb.Prob.Percolation.GreenLocalizationGeometry
import LatticeProb.Prob.Percolation.GreenQuantitativeField
import LatticeProb.Prob.Percolation.LatticeClusterBall
import LatticeProb.Prob.Percolation.LatticeOrderZeroGradient
import LatticeProb.Prob.Percolation.MeasurableRootedPlane
import LatticeProb.Prob.Percolation.NeighborRadialScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PercolationClusterHomogenization.Proofs.Lattice.ConfigurationExtension
import PercolationClusterHomogenization.External.WellConnected
import LatticeProb.Graph.Zd

/-!
# Sums over the lattice neighbours

The sum of a function over the lattice neighbours of a vertex is the sum over the `2d` directions,
and the Laplacian on a cluster is a sum over the lattice neighbours.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Proofs.S3

open LatticeProb LatticeProb.Percolation Rigidity.Section3 Classical

variable {d : ℕ}

/-! ### The faces of `L(Q_N)` as the starting points of the outward edges -/

section Faces

variable [NeZero d] {N : ℕ}

end Faces

/-! ### The divergence identity -/

/-! ### The discrete normal derivative of a harmonic function -/

/-- The sum of `f` over the lattice neighbours of `x` is the sum over the `2d` directions. -/
theorem sum_lattice_neighborFinset_eq_nbrSum [NeZero d] (f : Vertex d → ℝ) (x : Vertex d) :
    ∑ y ∈ (lattice d).neighborFinset x, f y = nbrSum f x := by
  have hw := Graph.Zd.walkOp_eq f x
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    positivity
  rw [Graph.walkOp, LatticeProb.walkOp, Graph.Zd.degree_eq] at hw
  push_cast at hw
  exact (div_left_inj' hd0).mp hw

/-- The Laplacian on a cluster as a sum over the lattice neighbours. -/
theorem componentLaplacian_eq_sum_lattice {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (x : Vertex d) (hx : x ∈ C.supp) :
    componentLaplacian C u ⟨x, hx⟩ = ∑ z ∈ (lattice d).neighborFinset x,
      if (openGraph ω).Adj x z then extend C u z - extend C u x else 0 := by
  rw [← Finset.sum_filter]
  have hset : ((lattice d).neighborFinset x).filter (fun z => (openGraph ω).Adj x z) =
      ((componentGraph C).neighborFinset ⟨x, hx⟩).map (Function.Embedding.subtype _) := by
    ext z
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_map,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨-, hz⟩
      exact ⟨⟨z, C.mem_supp_of_adj_mem_supp hx hz⟩, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨openGraph_le ω hy, hy⟩
  rw [hset, Finset.sum_map, componentLaplacian]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [extend, hx]

end Rigidity.Proofs.S3
