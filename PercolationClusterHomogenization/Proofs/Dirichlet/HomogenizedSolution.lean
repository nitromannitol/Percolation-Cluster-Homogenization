import PercolationClusterHomogenization.Proofs.Dirichlet.LemmaSixThreeInner

/-!
# The homogenized solution for the conductance `σ I`

For the constant conductance `σ > 0` on the edges of `ℤᵈ`, the solution of the discrete Dirichlet
problem on a lattice cube is harmonic for the discrete Laplacian
(`condLaplacian_constCond_one_eq_zero`), and its energy for the unit conductance is at most that
of its datum (`innerEdgeEnergy_constCond_one_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The Laplacian of a constant conductance is proportional to the conductance. -/
theorem condLaplacian_constCond_smul (σ : ℝ) (u : Vertex d → ℝ) (x : Vertex d) :
    condLaplacian (constCond fun _ => σ) u x =
      σ * condLaplacian (constCond fun _ => (1 : ℝ)) u x := by
  unfold condLaplacian constCond
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The homogenized solution is harmonic for the discrete Laplacian.** -/
theorem condLaplacian_constCond_one_eq_zero (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) {x : Vertex d} (hx : x ∈ cubeInterior Q) :
    condLaplacian (constCond fun _ => (1 : ℝ))
      (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w) x = 0 := by
  have h := condLaplacian_dirichletSolution (d := d) hd (constCond fun _ => σ)
    (fun _ => hσ) (cubeInterior Q) w x hx
  rw [condLaplacian_constCond_smul] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hσ.ne'
  · exact h

/-- **The energy of the homogenized solution is at most that of the datum.** -/
theorem innerEdgeEnergy_constCond_one_le (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) :
    innerEdgeEnergy (constCond fun _ => (1 : ℝ)) Q
        (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w) ≤
      ∑ x ∈ Q.vertices, ∑ j : Fin d,
        (if x + unit j ∈ Q.vertices then (w (x + unit j) - w x) ^ 2 else 0) := by
  have h := sum_sq_inner_grad_dirichletSolution_le (d := d) hd (fun _ => σ) hσ
    (fun _ => ⟨le_rfl, le_rfl⟩) Q w
  rw [div_self hσ.ne', one_mul] at h
  rw [innerEdgeEnergy_eq_sum_ite]
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp [constCond]
  · rfl

end Rigidity.Dirichlet
