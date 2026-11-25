import PercolationClusterHomogenization.Proofs.Dirichlet.HomogenizedSolution

/-!
# The sums of the increments of a function over the edges inside a lattice cube

`innerSqSum Q w` and `innerRpowSum Q w t` are the sums of the squared and of the `t`-th powers of
the increments of `w` over the edges inside the lattice cube `Q` of `ℤᵈ`; the homogenized solution
has at most the energy of its datum (`innerSqSum_dirichletSolution_le`). These are the normalized
sums `S₂`, `S_t` of the datum in the error chain of Section 6 of Armstrong and Dario. The
elementary bounds of powers of `K = 3^k` used to bound the errors of the chain by powers of `K^{-c₀}`
(`rpow_le_mul_rpow_neg_of_le_div_pow`, `one_div_le_rpow_neg`, `sqrt_one_div_le_rpow_neg`,
`sq_le_mul_rpow_neg`) are collected here.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The sum of the squared increments of `w` over the edges inside `Q`. -/
noncomputable def innerSqSum (Q : IntegerCube d) (w : Vertex d → ℝ) : ℝ :=
  ∑ y ∈ Q.vertices, ∑ j : Fin d, (if y + unit j ∈ Q.vertices then (w (y + unit j) - w y) ^ 2 else 0)

/-- The sum of the `t`-th powers of the increments of `w` over the edges inside `Q`. -/
noncomputable def innerRpowSum (Q : IntegerCube d) (w : Vertex d → ℝ) (t : ℝ) : ℝ :=
  ∑ y ∈ Q.vertices, ∑ j : Fin d,
    (if y + unit j ∈ Q.vertices then |w (y + unit j) - w y| ^ t else 0)

theorem innerSqSum_nonneg (Q : IntegerCube d) (w : Vertex d → ℝ) : 0 ≤ innerSqSum Q w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem innerRpowSum_nonneg (Q : IntegerCube d) (w : Vertex d → ℝ) (t : ℝ) :
    0 ≤ innerRpowSum Q w t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The homogenized solution has at most the energy of its datum on the edges inside `Q`. -/
theorem innerSqSum_dirichletSolution_le (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) :
    innerSqSum Q (dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w) ≤
      innerSqSum Q w := by
  have := sum_sq_inner_grad_dirichletSolution_le (d := d) hd (fun _ => σ) hσ
    (fun _ => ⟨le_rfl, le_rfl⟩) Q w
  rwa [div_self hσ.ne', one_mul] at this

theorem origin_vertices_subset_succ' (m : ℕ) :
    (⟨m, 0⟩ : TriadicCube d).vertices ⊆ (⟨m + 1, 0⟩ : TriadicCube d).vertices :=
  (⟨m, 0⟩ : TriadicCube d).vertices_subset_parent

theorem le_add_mul_of_div_le {a b c L : ℝ} (hL : 0 < L) (h : a / L ≤ b / L + c) :
    a ≤ b + L * c := by
  rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne'] at h
  linarith

theorem le_add_add_mul_of_div_le {a b c d L : ℝ} (hL : 0 < L) (h : a / L ≤ b / L + c / L + d) :
    a ≤ b + (c + L * d) := by
  rw [div_le_iff₀ hL, add_mul, add_mul, div_mul_cancel₀ _ hL.ne', div_mul_cancel₀ _ hL.ne'] at h
  linarith

theorem three_pow_mul_eq (a k : ℕ) : (3 : ℝ) ^ (a * k) = ((3 : ℝ) ^ k) ^ a := by
  rw [mul_comm, pow_mul]

theorem rpow_le_mul_rpow_neg_of_le_div_pow {K x c e : ℝ} {n : ℕ} (hK : 1 ≤ K) (hx : 0 ≤ x)
    (hc : 0 ≤ c) (he : 0 ≤ e) (h : x ≤ c / K ^ n) :
    x ^ e ≤ c ^ e * K ^ (-((n : ℝ) * e)) := by
  have hK0 : 0 < K := by linarith
  calc x ^ e ≤ (c / K ^ n) ^ e := Real.rpow_le_rpow hx h he
    _ = c ^ e * K ^ (-((n : ℝ) * e)) := by
      rw [Real.div_rpow hc (by positivity), Real.rpow_neg hK0.le, Real.rpow_mul hK0.le,
        Real.rpow_natCast, div_eq_mul_inv]

theorem rpow_neg_le_rpow_neg {K a b : ℝ} (hK : 1 ≤ K) (h : b ≤ a) : K ^ (-a) ≤ K ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le hK (neg_le_neg h)

theorem one_div_le_rpow_neg {K c : ℝ} (hK : 1 ≤ K) (hc : c ≤ 1) : 1 / K ≤ K ^ (-c) := by
  rw [one_div, ← Real.rpow_neg_one K]
  exact rpow_neg_le_rpow_neg hK hc

theorem sqrt_one_div_le_rpow_neg {K c : ℝ} (hK : 1 ≤ K) (hc : c ≤ 1 / 2) :
    √(1 / K) ≤ K ^ (-c) := by
  have hK0 : 0 < K := by linarith
  rw [show (1 : ℝ) / K = K⁻¹ from one_div K, Real.sqrt_eq_rpow, Real.inv_rpow hK0.le,
    ← Real.rpow_neg hK0.le]
  exact rpow_neg_le_rpow_neg hK hc

theorem rpow_two_div_mul_rpow {M a t : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (ht : 0 < t) :
    (a * M ^ t) ^ (2 / t) = a ^ (2 / t) * M ^ 2 := by
  rw [Real.mul_rpow ha (Real.rpow_nonneg hM _), ← Real.rpow_mul hM,
    show t * (2 / t) = 2 by field_simp, Real.rpow_two]

theorem sq_le_mul_rpow_neg {K L c₀ : ℝ} (hK : 1 ≤ K) (hc₀ : c₀ ≤ 14) (hKL : K ^ 8 ≤ 3 ^ 7 * L) :
    K ^ 2 ≤ 3 ^ 14 * L ^ 2 * K ^ (-c₀) := by
  have hK0 : 0 < K := by linarith
  have hKc : K ^ c₀ * K ^ (-c₀) = 1 := by
    rw [Real.rpow_neg hK0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hK0 _).ne']
  have h14 : K ^ c₀ ≤ K ^ 14 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hK (by push_cast; linarith)
  have h16 : K ^ 2 * K ^ 14 ≤ 3 ^ 14 * L ^ 2 := by
    rw [← pow_add]
    calc K ^ (2 + 14) = (K ^ 8) ^ 2 := by ring
      _ ≤ (3 ^ 7 * L) ^ 2 := by gcongr
      _ = 3 ^ 14 * L ^ 2 := by ring
  calc K ^ 2 = K ^ 2 * K ^ c₀ * K ^ (-c₀) := by rw [mul_assoc, hKc, mul_one]
    _ ≤ 3 ^ 14 * L ^ 2 * K ^ (-c₀) :=
      mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left h14 (by positivity)).trans h16)
        (Real.rpow_nonneg hK0.le _)

end Rigidity.Dirichlet
