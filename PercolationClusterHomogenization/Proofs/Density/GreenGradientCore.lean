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
# Values on a cluster ball and the normalized `L²` norm

A value of a function on a cluster ball is at most the number of vertices of the ball times the
normalized `L̲²` norm of the function on the ball.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation

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
