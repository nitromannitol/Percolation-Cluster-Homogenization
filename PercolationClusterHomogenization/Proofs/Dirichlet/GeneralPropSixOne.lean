import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralLemmaSixThree
import PercolationClusterHomogenization.Proofs.Dirichlet.PropSixOne

/-!
# Proposition 6.1 of Armstrong and Dario in every dimension

Let `u` be harmonic on `C_*(□_m)` at the vertices whose lattice neighbours lie in `□_m`, `u_h` the
solution of the discrete homogenized problem with the datum `w̃ = cubeDatum` (equal to `u` on
`C_*(□_m) ∩ ∂□_m`), and `v` a function equal to `u_h` off the interior of `□_m` (in the source, the
patch of Lemma 6.3). Modify `u` off the cluster to `u' = u` on `C_*(□_m)` and `u' = v` elsewhere.
Then `u'` is harmonic for the cluster conductance on the interior of `□_m`, `v = u'` off the
interior, and `v − u'` vanishes off the vertices of `C_*(□_m)` whose lattice neighbours lie in
`□_m`, so the Poincaré inequality on the cluster (`exists_cube_sum_sq_le_of_eq_zero`) applies to
`v − u'`. With the energy comparisons `E_ā(u_h) ≤ E(u) + δ₁` (Lemma 6.2) and
`E(v) ≤ E_ā(u_h) + δ₂` (Lemma 6.3 (ii)) and `Σ_{C_*} (v − u_h)² ≤ δ₃` (Lemma 6.3 (iii)), the error
chain of the lattice Proposition 6.1 (`sum_sq_sub_le_of_inner_energy_chain`) gives
`Σ_{C_*(□_m)} (u − u_h)² ≤ 2 P (δ₁ + δ₂) + 2 δ₃`, with `P` the Poincaré constant
(`cube_sum_sq_sub_uhom_le`). The planar form is `planar_sum_sq_sub_uhom_le`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- The lattice neighbours of a vertex of the interior of the lattice cube of a triadic cube lie
in the cube. -/
theorem TriadicCube.isLatticeInterior_of_mem_cubeInterior {U : TriadicCube d} {x : Vertex d}
    (hx : x ∈ cubeInterior U.toIntegerCube) : U.IsLatticeInterior x := by
  intro y hy
  have hb := (Finset.mem_filter.1 hx).2
  rw [← U.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
  intro i
  have h1 := hb i
  obtain ⟨l, hl | hl⟩ := Graph.Zd.adj_iff.mp hy <;> subst hl <;>
  · simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_apply]
    split_ifs <;> constructor <;> omega

/-- **Armstrong and Dario, Proposition 6.1**, in every dimension, from the energy comparisons of
Lemmas 6.2 and 6.3 and the Poincaré inequality on the cluster. -/
theorem cube_sum_sq_sub_uhom_le (hd : 0 < d) {K₀ : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : ∀ (ω : Configuration d), PartitionEvent ω → ∀ (U : TriadicCube d)
      (k : ℕ), k ≤ U.scale →
      (∀ x ∈ U.parent.vertices, (partitionCube ω x).scale ≤ k) →
      ∀ f : Vertex d → ℝ,
      (∀ x, ¬(x ∈ crossingClusterVertices ω U ∧ U.IsLatticeInterior x) → f x = 0) →
      ∑ x ∈ crossingClusterVertices ω U, f x ^ 2 ≤
        (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k)) * K₀ * ((3 : ℝ) ^ k) ^ (2 * d) *
          ((3 : ℝ) ^ (U.scale + 1)) ^ 2 *
          ∑ z ∈ crossingClusterVertices ω U, ∑ j : Fin d,
            (if z + unit j ∈ crossingClusterVertices ω U ∧ (openGraph ω).Adj z (z + unit j) then
              (f (z + unit j) - f z) ^ 2 else 0))
    (hP : PartitionEvent ω) {m k₀ : ℕ} (hk₀m : k₀ ≤ m)
    (hk₀ : ∀ x ∈ (⟨m + 1, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k₀)
    (hU : PartitionResolved ω ⟨m, 0⟩) {σ : ℝ} {u : Vertex d → ℝ}
    (hu : (fun x : ↥(crossingClusterVertices ω ⟨m, 0⟩) => u x) ∈ cubeHarmonic ω ⟨m, 0⟩)
    {v : Vertex d → ℝ}
    (hv : ∀ x, x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube →
      v x = dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) (cubeDatum hd hP m hU u) x)
    {δ₁ δ₂ δ₃ : ℝ}
    (h₁ : innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) (cubeDatum hd hP m hU u)) ≤
      innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube d).toIntegerCube u + δ₁)
    (h₂ : innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube d).toIntegerCube v ≤
      innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) (cubeDatum hd hP m hU u)) + δ₂)
    (h₃ : ∑ x ∈ crossingClusterVertices ω ⟨m, 0⟩, (v x - dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) (cubeDatum hd hP m hU u) x) ^ 2 ≤
      δ₃) :
    ∑ x ∈ crossingClusterVertices ω ⟨m, 0⟩, (u x - dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) (cubeDatum hd hP m hU u) x) ^ 2 ≤
      2 * ((1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
          ((3 : ℝ) ^ (m + 1)) ^ 2 * ((δ₁ + δ₂) / 1)) + 2 * δ₃ := by
  set U : TriadicCube d := ⟨m, 0⟩
  set Q := U.toIntegerCube
  set C := crossingClusterVertices ω U
  set uh := dirichletSolution (constCond fun _ => σ) (cubeInterior Q) (cubeDatum hd hP m hU u)
  set c := cubeCond ω U
  set u' : Vertex d → ℝ := fun x => if x ∈ C then u x else v x with hu'
  have hu'C : ∀ x ∈ C, u' x = u x := fun x hx => by simp only [hu', if_pos hx]
  have hE : innerEdgeEnergy c Q u' = innerEdgeEnergy c Q u := by
    unfold innerEdgeEnergy
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    by_cases hc : c (x, j) = 0
    · rw [hc, zero_mul, zero_mul]
    · have hcl : x ∈ C ∧ x + unit j ∈ C := by
        by_contra h
        apply hc
        unfold c cubeCond
        rw [if_neg]
        exact fun h' => h ⟨h'.1, h'.2.1⟩
      rw [hu'C _ hcl.1, hu'C _ hcl.2]
  have hharm : (fun x : ↥C => u' x) ∈ cubeHarmonic ω U := by
    have e : (fun x : ↥C => u' x) = fun x : ↥C => u x := funext fun x => hu'C x.1 x.2
    rw [e]
    exact hu
  have hlap : ∀ x ∈ cubeInterior Q, condLaplacian c u' x = 0 := fun x hx =>
    condLaplacian_cubeCond_eq_zero hharm (TriadicCube.isLatticeInterior_of_mem_cubeInterior hx)
  have hvu : ∀ x, x ∉ cubeInterior Q → v x = u' x := by
    intro x hx
    by_cases hxC : x ∈ C
    · rw [hu'C x hxC, hv x hx]
      change dirichletSolution _ _ (cubeDatum hd hP m hU u) x = u x
      rw [dirichletSolution_eq_of_not_mem _ _ _ hx]
      unfold cubeDatum
      exact boundaryInterpolation_of_mem _ _ (Finset.mem_filter.2 ⟨hxC, hx⟩)
    · simp only [hu', if_neg hxC]
  have hscaleU : ∀ x ∈ U.parent.vertices, (partitionCube ω x).scale ≤ k₀ := fun x hx => hk₀ x hx
  set f : Vertex d → ℝ := fun x => v x - u' x with hf
  have hf0 : ∀ x, ¬(x ∈ C ∧ U.IsLatticeInterior x) → f x = 0 := by
    intro x hx
    simp only [hf]
    by_cases hxC : x ∈ C
    · have hxi : x ∉ cubeInterior Q := fun h =>
        hx ⟨hxC, TriadicCube.isLatticeInterior_of_mem_cubeInterior h⟩
      rw [hvu x hxi, sub_self]
    · simp only [hu', if_neg hxC, sub_self]
  have hpoinc := hK₀ ω hP U k₀ hk₀m hscaleU f hf0
  have hCQ : C ⊆ Q.vertices := Finset.filter_subset _ _
  have hedges : ∑ z ∈ C, ∑ j : Fin d,
      (if z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2
        else 0) =
      ∑ x ∈ Q.vertices, ∑ j : Fin d,
        (if innerCond c Q (x, j) = 0 then 0 else ((v - u') (x + unit j) - (v - u') x) ^ 2) := by
    rw [← Finset.sum_subset hCQ]
    · refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun j _ => ?_
      unfold innerCond
      by_cases h : z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j)
      · have hcz : c (z, j) = 1 := by
          unfold c cubeCond
          exact if_pos ⟨hz, h.1, h.2⟩
        rw [if_pos h, if_pos (hCQ h.1), hcz, if_neg one_ne_zero]
        rfl
      · rw [if_neg h]
        have hcz : c (z, j) = 0 := by
          unfold c cubeCond
          rw [if_neg]
          exact fun h' => h ⟨h'.2.1, h'.2.2⟩
        rw [hcz, ite_self, if_pos rfl]
    · intro x _ hxC
      refine Finset.sum_eq_zero fun j _ => ?_
      have hcx : innerCond c Q (x, j) = 0 := by
        unfold innerCond c cubeCond
        split_ifs with h1 h2
        · exact absurd h2.1 hxC
        · rfl
        · rfl
      rw [if_pos hcx]
  rw [hedges] at hpoinc
  have h3d : (1 : ℝ) < 3 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have hP0 : 0 ≤ (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
      ((3 : ℝ) ^ (m + 1)) ^ 2 := by
    have : (0 : ℝ) ≤ 3 ^ d / (3 ^ d - 1) := div_nonneg (by positivity) (by linarith)
    positivity
  have hfin := sum_sq_sub_le_of_inner_energy_chain c (lam := 1) one_pos
    (fun e => cubeCond_eq_zero_or U e) Q hlap hvu hP0
    (h₁.trans_eq (by rw [hE])) h₂ C hpoinc h₃
  calc ∑ x ∈ C, (u x - uh x) ^ 2 = ∑ x ∈ C, (u' x - uh x) ^ 2 :=
        Finset.sum_congr rfl fun x hx => by rw [hu'C x hx]
    _ ≤ _ := hfin

end Rigidity.Dirichlet
