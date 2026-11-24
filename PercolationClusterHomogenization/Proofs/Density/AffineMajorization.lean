import LatticeProb.External.GreenQuantitative
import LatticeProb.Prob.Percolation.ContinuumGreen
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeClusterL2
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import PercolationClusterHomogenization.External.CorrectorQuantitative

/-!
# Proposition 2.6, step:2.6-expansion: affine majorization

`AffineMajorizationStep` (paper L617-620, proof step `step:2.6-expansion`): under the density
estimate (H4) at the scale `X`, for
`r ≥ X ∨ R₀`, the `L̲²(𝒞 ∩ B_r(x))` norm of an affine function `b + η · (· - x)` majorizes
`c₁ r |η|₁`.

Proof. Replacing `(b, η)` by `(-b, -η)` we may assume `b ≥ 0`. Let `p = x + (r / 2|η|) η` and
let `z` be the lattice point obtained by rounding `p`, so that `|z - p| ≤ d + 1`. For `r ≥ R₀`,
the ball `B_{r/100}(z)` lies in `B_r(x)`, the affine function is at least `|η| r / 4` on it, and by
(H4) it carries at least `c r^d` vertices of the cluster; the ball `B_r(x)` carries at most
`5^d r^d` lattice points (`card_componentEuclideanBall_le`), and `|η|₁² ≤ (d + 1) |η|²`.

The file also records the elementary properties of the normalized `L̲²` norm `componentBallL2`
used in the slope estimate: the triangle inequality (`componentBallL2_add_le`) and the bound by
the supremum (`componentBallL2_le_of_abs_le`).
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

variable {d : ℕ} {ω : Configuration d}

/-! ### The normalized `L̲²` norm on a component ball -/

/-- The triangle inequality for the normalized `L̲²` norm on a component ball. -/
theorem componentBallL2_add_le (C : OpenComponent ω) (x : Vertex d) (r : ℝ) (f h : C → ℝ) :
    componentBallL2 C x r (fun z => f z + h z) ≤
      componentBallL2 C x r f + componentBallL2 C x r h := by
  unfold componentBallL2
  set s := componentEuclideanBall C x r
  have hN : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_div' _ hN, Real.sqrt_div' _ hN, Real.sqrt_div' _ hN, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hB : 0 ≤ ∑ z ∈ s, f z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  have hH : 0 ≤ ∑ z ∈ s, h z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s f h
  have hexp : ∑ z ∈ s, (f z + h z) ^ 2 =
      ∑ z ∈ s, f z ^ 2 + 2 * ∑ z ∈ s, f z * h z + ∑ z ∈ s, h z ^ 2 := by
    have : ∀ z, (f z + h z) ^ 2 = f z ^ 2 + 2 * (f z * h z) + h z ^ 2 := fun z => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg (∑ z ∈ s, f z ^ 2))
    (Real.sqrt_nonneg (∑ z ∈ s, h z ^ 2)))]
  apply Real.sqrt_le_sqrt
  rw [hexp, add_sq, Real.sq_sqrt hB, Real.sq_sqrt hH]
  nlinarith

/-- The normalized `L̲²` norm is even. -/
theorem componentBallL2_neg (C : OpenComponent ω) (x : Vertex d) (r : ℝ) (f : C → ℝ) :
    componentBallL2 C x r (fun z => -f z) = componentBallL2 C x r f := by
  simp only [componentBallL2, neg_sq]

/-! ### Affine majorization -/

end Rigidity.Proofs.S2
