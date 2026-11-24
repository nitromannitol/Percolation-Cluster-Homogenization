import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaChain

/-!
# Measurability of the flatness errors, in every dimension

A random function on the vertices of an integer cube whose differences across the lattice edges of
the cube are measurable has measurable differences between any two vertices of the cube: walk
from one to the other coordinate by coordinate (`measurable_sub_of_edges`). The flatness error of
Lemma 5.8 is unchanged when a constant is added to the function, so it is a measurable function of
these differences (`measurable_cubeFlatnessError_of_edges`). For the coarsened minimizers of `μ`
and the coarsened maximizers of `ν` the differences across the edges are measurable
(`measurable_cubeMuMinimizer_edge`, `measurable_cubeNuSolution_edge`), hence so are their flatness
errors (`measurable_cubeFlatnessError_cubeMuMinimizer`,
`measurable_cubeFlatnessError_cubeNuSolution`). These are the flatness terms of the proof of
Lemma 5.9 of Armstrong and Dario, display (5.41).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (finsetMean affineFun)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The `ℓ¹` distance between two vertices. -/
def vertexL1Dist (x y : Vertex d) : ℕ := ∑ i, (y i - x i).natAbs

/-- **Differences along lattice paths in a cube.** If the differences of a random function across
the lattice edges of an integer cube are measurable, so is the difference between any two of its
vertices. -/
theorem measurable_sub_of_edges (Q : IntegerCube d) {F : Ω → Vertex d → ℝ}
    (hF : ∀ z ∈ Q.vertices, ∀ i : Fin d, z + unit i ∈ Q.vertices →
      Measurable fun ω => F ω (z + unit i) - F ω z) :
    ∀ x ∈ Q.vertices, ∀ y ∈ Q.vertices, Measurable fun ω => F ω y - F ω x := by
  suffices h : ∀ k : ℕ, ∀ x ∈ Q.vertices, ∀ y ∈ Q.vertices, vertexL1Dist x y = k →
      Measurable fun ω => F ω y - F ω x from fun x hx y hy => h _ x hx y hy rfl
  intro k
  induction k with
  | zero =>
    intro x _ y _ hk
    have hxy : x = y := by
      funext i
      have h0 : (y i - x i).natAbs = 0 := by
        have := Finset.single_le_sum (f := fun j => (y j - x j).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
        unfold vertexL1Dist at hk
        omega
      omega
    subst hxy
    simp only [sub_self]
    exact measurable_const
  | succ k ih =>
    intro x hx y hy hk
    have hne : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      have : vertexL1Dist x y = 0 := by
        unfold vertexL1Dist
        exact Finset.sum_eq_zero fun i _ => by rw [h i, sub_self, Int.natAbs_zero]
      omega
    obtain ⟨i, hi⟩ := hne
    rw [IntegerCube.mem_vertices] at hx hy
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · -- step up in the coordinate `i`
      set x' := x + unit i with hx'
      have hx'Q : x' ∈ Q.vertices := by
        rw [IntegerCube.mem_vertices]
        intro j
        change Q.corner j ≤ x j + (unit i : Vertex d) j ∧ x j + (unit i : Vertex d) j <
          Q.corner j + (Q.size : ℤ)
        by_cases hji : j = i
        · subst hji
          rw [unit_apply_self]
          have := hx j
          have := hy j
          omega
        · rw [unit_apply_ne hji, add_zero]
          exact hx j
      have hd : vertexL1Dist x' y = k := by
        have e : ∀ j, (y j - x' j).natAbs =
            if j = i then (y j - x j).natAbs - 1 else (y j - x j).natAbs := by
          intro j
          change (y j - (x j + (unit i : Vertex d) j)).natAbs = _
          by_cases hji : j = i
          · subst hji
            rw [unit_apply_self, if_pos rfl]
            omega
          · rw [unit_apply_ne hji, add_zero, if_neg hji]
        unfold vertexL1Dist at hk ⊢
        have h1 := Finset.add_sum_erase Finset.univ (fun j => (y j - x j).natAbs)
          (Finset.mem_univ i)
        have h2 := Finset.add_sum_erase Finset.univ (fun j => (y j - x' j).natAbs)
          (Finset.mem_univ i)
        have h3 : ∑ j ∈ Finset.univ.erase i, (y j - x' j).natAbs =
            ∑ j ∈ Finset.univ.erase i, (y j - x j).natAbs :=
          Finset.sum_congr rfl fun j hj => by rw [e j, if_neg (Finset.ne_of_mem_erase hj)]
        have h4 : (y i - x' i).natAbs = (y i - x i).natAbs - 1 := by rw [e i, if_pos rfl]
        have h5 : 1 ≤ (y i - x i).natAbs := by omega
        omega
      have h1 := ih x' hx'Q y ((IntegerCube.mem_vertices Q y).2 hy) hd
      have h2 := hF x ((IntegerCube.mem_vertices Q x).2 hx) i hx'Q
      have e : (fun ω => F ω y - F ω x) =
          fun ω => (F ω y - F ω x') + (F ω (x + unit i) - F ω x) := by
        funext ω
        rw [hx']
        ring
      rw [e]
      exact h1.add h2
    · -- step down in the coordinate `i`
      set x' := x - unit i with hx'
      have hx'Q : x' ∈ Q.vertices := by
        rw [IntegerCube.mem_vertices]
        intro j
        change Q.corner j ≤ x j - (unit i : Vertex d) j ∧ x j - (unit i : Vertex d) j <
          Q.corner j + (Q.size : ℤ)
        by_cases hji : j = i
        · subst hji
          rw [unit_apply_self]
          have := hx j
          have := hy j
          omega
        · rw [unit_apply_ne hji, sub_zero]
          exact hx j
      have hd : vertexL1Dist x' y = k := by
        have e : ∀ j, (y j - x' j).natAbs =
            if j = i then (y j - x j).natAbs - 1 else (y j - x j).natAbs := by
          intro j
          change (y j - (x j - (unit i : Vertex d) j)).natAbs = _
          by_cases hji : j = i
          · subst hji
            rw [unit_apply_self, if_pos rfl]
            omega
          · rw [unit_apply_ne hji, sub_zero, if_neg hji]
        unfold vertexL1Dist at hk ⊢
        have h1 := Finset.add_sum_erase Finset.univ (fun j => (y j - x j).natAbs)
          (Finset.mem_univ i)
        have h2 := Finset.add_sum_erase Finset.univ (fun j => (y j - x' j).natAbs)
          (Finset.mem_univ i)
        have h3 : ∑ j ∈ Finset.univ.erase i, (y j - x' j).natAbs =
            ∑ j ∈ Finset.univ.erase i, (y j - x j).natAbs :=
          Finset.sum_congr rfl fun j hj => by rw [e j, if_neg (Finset.ne_of_mem_erase hj)]
        have h4 : (y i - x' i).natAbs = (y i - x i).natAbs - 1 := by rw [e i, if_pos rfl]
        have h5 : 1 ≤ (y i - x i).natAbs := by omega
        omega
      have h1 := ih x' hx'Q y ((IntegerCube.mem_vertices Q y).2 hy) hd
      have hxx : x' + unit i = x := by rw [hx', sub_add_cancel]
      have h2 := hF x' hx'Q i (by rw [hxx]; exact (IntegerCube.mem_vertices Q x).2 hx)
      rw [hxx] at h2
      have e : (fun ω => F ω y - F ω x) =
          fun ω => (F ω y - F ω x') - (F ω x - F ω x') := by
        funext ω
        ring
      rw [e]
      exact h1.sub h2

/-- The flatness error is unchanged when a constant is subtracted from the function. -/
theorem cubeFlatnessError_sub_const (U : TriadicCube d) (w : Vertex d → ℝ) (c : ℝ)
    (ξ : Fin d → ℝ) :
    cubeFlatnessError U (fun x => w x - c) ξ = cubeFlatnessError U w ξ := by
  unfold cubeFlatnessError finsetMean
  have hc : (0 : ℝ) < U.toIntegerCube.vertices.card := by
    rw [U.card_toIntegerCube_vertices]
    exact U.latticeVolume_pos
  have e : ((U.toIntegerCube.vertices.card : ℝ))⁻¹ * ∑ y ∈ U.toIntegerCube.vertices,
      (w y - c - affineFun ξ y) = ((U.toIntegerCube.vertices.card : ℝ))⁻¹ *
        ∑ y ∈ U.toIntegerCube.vertices, (w y - affineFun ξ y) - c := by
    have : ∑ y ∈ U.toIntegerCube.vertices, (w y - c - affineFun ξ y) =
        ∑ y ∈ U.toIntegerCube.vertices, (w y - affineFun ξ y) -
          (U.toIntegerCube.vertices.card : ℝ) * c := by
      calc ∑ y ∈ U.toIntegerCube.vertices, (w y - c - affineFun ξ y)
          = ∑ y ∈ U.toIntegerCube.vertices, ((w y - affineFun ξ y) - c) :=
            Finset.sum_congr rfl fun y _ => by ring
        _ = ∑ y ∈ U.toIntegerCube.vertices, (w y - affineFun ξ y) -
            ∑ _y ∈ U.toIntegerCube.vertices, c := Finset.sum_sub_distrib _ _
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [this, mul_sub, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **Measurability of the flatness error.** If the differences of a random function across the
lattice edges of `U` are measurable, its flatness error is measurable. -/
theorem measurable_cubeFlatnessError_of_edges (U : TriadicCube d) {F : Ω → Vertex d → ℝ}
    (hF : ∀ z ∈ U.toIntegerCube.vertices, ∀ i : Fin d, z + unit i ∈ U.toIntegerCube.vertices →
      Measurable fun ω => F ω (z + unit i) - F ω z) (ξ : Fin d → ℝ) :
    Measurable fun ω => cubeFlatnessError U (F ω) ξ := by
  set x₀ := U.toIntegerCube.corner with hx₀
  have hx₀U : x₀ ∈ U.toIntegerCube.vertices := by
    rw [IntegerCube.mem_vertices]
    intro i
    have : 0 < (U.toIntegerCube.size : ℤ) := by
      change (0 : ℤ) < ((3 ^ U.scale : ℕ) : ℤ)
      positivity
    exact ⟨le_rfl, by linarith⟩
  have hdiff := measurable_sub_of_edges U.toIntegerCube hF x₀ hx₀U
  have e : (fun ω => cubeFlatnessError U (F ω) ξ) =
      fun ω => cubeFlatnessError U (fun x => F ω x - F ω x₀) ξ := by
    funext ω
    rw [cubeFlatnessError_sub_const]
  rw [e]
  unfold cubeFlatnessError finsetMean
  refine measurable_const.mul (Finset.measurable_sum _ fun x hx => ?_)
  refine ((((hdiff x hx).sub measurable_const).sub (measurable_const.mul
    (Finset.measurable_sum _ fun y hy => (hdiff y hy).sub measurable_const)))).pow_const 2

variable {p : unitInterval}

/-- The flatness error of the coarsened minimizer of `μ` is measurable. -/
theorem measurable_cubeFlatnessError_cubeMuMinimizer (hd : 0 < d) (U : TriadicCube d)
    (q ξ : Fin d → ℝ) :
    Measurable fun ω => cubeFlatnessError U
      (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) ξ :=
  measurable_cubeFlatnessError_of_edges U
    (F := fun ω x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x))
    (fun _ hz _ hzi => measurable_cubeMuMinimizer_edge hd U q hz hzi) ξ

/-- The flatness error of the coarsened maximizer of `ν` is measurable. -/
theorem measurable_cubeFlatnessError_cubeNuSolution (hd : 0 < d) (U : TriadicCube d)
    (p' ξ : Fin d → ℝ) :
    Measurable fun ω => cubeFlatnessError U
      (fun x => cubeExtend ω U (cubeNuSolution ω U p') (partitionAnchor ω x)) ξ :=
  measurable_cubeFlatnessError_of_edges U
    (F := fun ω x => cubeExtend ω U (cubeNuSolution ω U p') (partitionAnchor ω x))
    (fun _ hz _ hzi => measurable_cubeNuSolution_edge hd U p' hz hzi) ξ

end Rigidity.Percolation
