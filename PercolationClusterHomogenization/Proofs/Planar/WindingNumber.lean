import LatticeProb.Prob.Percolation.ContinuumGreen
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeClusterBall
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Segment

/-!
# Cubes, complex coordinates and winding numbers in the plane

The cube `Q_r = {x : |x|_∞ ≤ r}` of `ℤ²`, the embedding of `ℤ²` into `ℂ`, and the winding number
around the origin of a closed lattice path avoiding it.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Section5

variable {ω : Configuration 2}

/-- The cube `Q_r = {x : |x|_∞ ≤ r}`. -/
def cube (r : ℕ) : Set (Vertex 2) := {x | ∀ i, |x i| ≤ (r : ℤ)}

/-- The point `x` of `ℤ²` as a complex number. -/
def toComplex (x : Vertex 2) : ℂ := ⟨x 0, x 1⟩

/-- The winding number around the origin of the closed lattice path `γ 0, γ 1, …, γ n, γ 0`
avoiding the origin: the sum of the angle increments `arg (γ(i+1) / γ(i)) ∈ (-π, π]` over `2π`. -/
noncomputable def windingNumber {n : ℕ} (γ : Fin (n + 1) → Vertex 2) : ℝ :=
  (∑ i : Fin (n + 1), Complex.arg (toComplex (γ (i + 1)) / toComplex (γ i))) / (2 * Real.pi)

end Rigidity.Section5
