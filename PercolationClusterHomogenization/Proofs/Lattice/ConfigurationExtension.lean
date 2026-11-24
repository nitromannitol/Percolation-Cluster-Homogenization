import LatticeProb.Prob.Percolation.LatticeClusterLipschitz
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-!
# The extension by zero of a function on a cluster

`extend C u` is the function on `ℤᵈ` equal to `u` on the vertices of the component `C` and to `0`
elsewhere.
-/

open MeasureTheory LatticeProb.Percolation Classical

namespace Rigidity.Section3

variable {d : ℕ}

/-- A function on a component, extended by zero to every vertex of the lattice. -/
noncomputable def extend {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ) :
    Vertex d → ℝ :=
  fun z => if h : z ∈ C.supp then u ⟨z, h⟩ else 0

end Rigidity.Section3
