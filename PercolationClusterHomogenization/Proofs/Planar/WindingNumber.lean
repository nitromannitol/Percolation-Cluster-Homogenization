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

/-! Statements of the numbered results of Section 5.3.1-5.3.2 (unbounded level sets and
large biconnected components of the potential, d = 2).

These results live in the standing context of Sections 5.3-5.4: the event `Σ f = 0`,
`|supp u_f| = ∞`, on which `u_f` decays to zero. They are stated for every `u` with `-Δu = f` on
`𝒞_∞` and `u → 0` at infinity (the potential normalized at infinity, see `Section5Statements`)
whose support is infinite. Graph notions (paths, connected and biconnected sets, components) are
those of `𝒞_∞` restricted to the set in question; "disjoint" paths are vertex-disjoint; `Q_r` is
the cube of radius `r`.

Convention: like every `...Stmt` of the draft, the statements below omit the paper's standing
assumption `p_c(d) < p < 1` (corrected draft L66, L231); the composed theorems in
`Rigidity/Proofs/Assembly` carry it as hypotheses (`criticalProbability 2 < p`, `p < 1`, or the
part of it they use). -/

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
