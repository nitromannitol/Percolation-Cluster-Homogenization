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
# `step:3.2-divergence`: the divergence identity on `L(Q_N)`

Step `step:3.2-divergence` of Proposition 3.2 (eq. (divergence-theorem-flux) of the corrected
draft). For a function `f` on oriented pairs of vertices which is antisymmetric and whose sum over
the `2d` neighbours of every vertex vanishes, the sum of `f` over the oriented edges leaving
`L(Q_N)` vanishes: summing the vanishing neighbour sums over `L(Q_N)`, direction by direction, the
edges with both endpoints in `L(Q_N)` cancel in pairs (`x ↦ x - e_i` is a bijection between the
two orientations), and the outward edges in direction `±e_i` start exactly at the points of the
corresponding face: `center(Q_N)` for `+e₁`, `left(Q_N)` for `-e₁`, and the sides `x_j = ±N` for
`±e_j`, `j ≠ 1`.

The discrete normal derivative `edgeDifference C u` of a function `u` on a cluster is antisymmetric,
and its neighbour sum at a vertex of the cluster is minus the Laplacian of `u` there, so the
identity applies to harmonic functions.
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
