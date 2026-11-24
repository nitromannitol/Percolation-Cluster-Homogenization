import LatticeProb.Prob.Percolation.LatticeClusterLipschitz
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-! Statements of the numbered results of Section 3 (Lipschitz harmonic functions). The cited
literature inputs that each proof uses are added as explicit hypotheses of the final theorems;
these definitions are the statements themselves.

* Convention: the statements (`…Stmt`) omit the regime `p_c(d) < p < 1`; the composed theorems
  (`Rigidity/Proofs/Assembly`) carry it as hypotheses `criticalProbability d < p` and `p < 1`.
* "With positive probability", for an event that quantifies over corrected planes (not shown
  measurable), is stated in the inner-measure form of Section 5c: the event contains a measurable
  event of positive probability (Proposition 3.2). -/

open MeasureTheory LatticeProb.Percolation Classical

namespace Rigidity.Section3

variable {d : ℕ}

/-- A function on a component, extended by zero to every vertex of the lattice. -/
noncomputable def extend {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ) :
    Vertex d → ℝ :=
  fun z => if h : z ∈ C.supp then u ⟨z, h⟩ else 0

end Rigidity.Section3
