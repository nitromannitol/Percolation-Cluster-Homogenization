import LatticeProb.Prob.Percolation.LatticeAnnularSup
import PercolationClusterHomogenization.Proofs.Density.AffineMajorization
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import LatticeProb.Prob.Percolation.LatticeRadialScale
import LatticeProb.Prob.FiniteTailMax

/-!
# Proposition 2.6: the deterministic core

`GreenGradientCoreStep` (step:2.6-expansion, paper L554-655). Write `R = |x - y|₂ / 2` and
`u = G(·, y) - K - Ḡ(x - y)`, harmonic in the interior of `𝒞 ∩ B_R(x)`.

* The large-scale `C^{1,1}` regularity (H2) at `R` gives a slope `ξ` and a constant `a`, and
  `GreenOscillationStep` bounds `‖u‖_{L̲²(B_R(x))} ≤ A₂ R^{2-d}`, so that
  `‖u - ∑ᵢ ξᵢ ℓᵢ - a‖_{L̲²(B_r(x))} ≤ Cr A₂ r² R^{-d}` for `r ∈ [X, R/2]`.
* `SlopeEstimateStep` then gives `|ξ - ∇Ḡ(x - y)|₁ ≤ A₁ R^{1/2 - d + δ/4}`.
* At the scale `X`, the value of `v = u - ∑ᵢ ξᵢ ℓᵢ - a` at a vertex of `B_X(x)` is at most
  `#B_X ‖v‖_{L̲²(B_X(x))} ≤ 5^d X^{d+2} Cr A₂ R^{-d}`, and the forward differences of the
  corrected planes are bounded by `1 + Cc X^{δ/4}` by (H3). Since
  `D_j G(x) - ∑ᵢ D_j ℓᵢ(x) ∂ᵢḠ = D_j v(x) + ∑ᵢ (ξᵢ - ∂ᵢḠ) D_j ℓᵢ(x)`, the threshold
  `|x - y|₁ ≥ A X^{2d+4}` (so that `X^{d+2} ≤ R^{1/2}`) gives the bound `A |x - y|₁^{1/2-d+δ}`.

This replaces the Caccioppoli inequality and the two-scale `L²` bound of the paper by the
pointwise bound of a function on a finite ball by its normalized `L²` norm at the minimal scale.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

variable {d : ℕ} {ω : Configuration d}

/-- A value on the cluster ball is at most the number of its vertices times the normalized `L²`
norm. -/
theorem abs_le_card_mul_componentBallL2 (C : OpenComponent ω) (x : Vertex d) (r : ℝ) (v : C → ℝ)
    {z : C} (hz : z ∈ componentEuclideanBall C x r) :
    |v z| ≤ ((componentEuclideanBall C x r).card : ℝ) * componentBallL2 C x r v := by
  set n : ℝ := ((componentEuclideanBall C x r).card : ℝ) with hn
  set S : ℝ := ∑ w ∈ componentEuclideanBall C x r, v w ^ 2 with hS
  have hn1 : 1 ≤ n := by
    rw [hn]; exact_mod_cast Finset.card_pos.mpr ⟨z, hz⟩
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun w _ => sq_nonneg _
  have hvS : v z ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun w => v w ^ 2) (fun w _ => sq_nonneg _) hz
  have hL2 : componentBallL2 C x r v ^ 2 = S / n := by
    unfold componentBallL2
    rw [Real.sq_sqrt (div_nonneg hS0 (by linarith))]
  have hL0 := componentBallL2_nonneg C x r v
  have hsq : |v z| ^ 2 ≤ (n * componentBallL2 C x r v) ^ 2 := by
    rw [sq_abs, mul_pow, hL2]
    have : n ^ 2 * (S / n) = n * S := by field_simp
    rw [this]
    nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hsq

end Rigidity.Proofs.S2
