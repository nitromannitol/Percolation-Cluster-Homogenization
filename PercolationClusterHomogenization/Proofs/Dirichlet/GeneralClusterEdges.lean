import PercolationClusterHomogenization.Proofs.Dirichlet.TiledEnergy
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeSubcubes

/-!
# The cluster of a triadic cube of `ℤᵈ` as a conductance on the lattice edges

For a triadic cube `U` of `ℤᵈ`, the cluster conductance `c_U(x, k)` is `1` on the open edges
`(x, x + e_k)` with both endpoints in the crossing cluster `C_*(U)` and `0` elsewhere. The lattice
objects of the Dirichlet problem for `c_U` are the cluster objects of `U`:

* the open neighbours of `x` in a finite set `S` are among `x ± e_k`, so
  `Σ_{y ∈ S, y ∼ x} g(y)` is the sum of the terms at the `2d` lattice neighbours in `S`
  (`sum_openAdj_eq_sum_unit`);
* the Laplacian of `c_U` is minus the Laplacian of the cluster (`condLaplacian_cubeCond`), so
  functions harmonic on `C_*(U)` at the vertices whose lattice neighbours lie in `U` are
  `c_U`-harmonic there (`condLaplacian_cubeCond_eq_zero`);
* the Dirichlet form of the cluster of a cube `T` is the sum of the squared increments over the
  open edges of `C_*(T)` (`cubeForm_eq_sum_edges`); for a resolved `T ⊆ U` it is at most the
  energy density of `c_U` summed over `T` (`cubeForm_le_sum_cubeEnergy`), and the energy density
  of `c_U` summed over `U` is the energy of `c_U` on the edges inside `U`
  (`sum_cubeEnergy_eq_innerEdgeEnergy`).

This is the general-dimensional form of `PlanarClusterEdges.lean`; in dimension `d` the cluster of
a subcube lies in the cluster of the cube only for resolved subcubes, on the partition event
(`crossingClusterVertices_subset_of_resolved`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

theorem unit_apply_eq_ite (k i : Fin d) : (unit k : Vertex d) i = if i = k then 1 else 0 := by
  simp only [unit, Pi.single_apply]

theorem add_unit_injective (x : Vertex d) {k l : Fin d} (h : x + unit k = x + unit l) : k = l := by
  have h1 : x k + (unit k : Vertex d) k = x k + (unit l : Vertex d) k := congrFun h k
  rw [unit_apply_eq_ite, unit_apply_eq_ite, if_pos rfl] at h1
  by_contra hkl
  rw [if_neg hkl] at h1
  omega

theorem sub_unit_injective (x : Vertex d) {k l : Fin d} (h : x - unit k = x - unit l) : k = l := by
  have h1 : x k - (unit k : Vertex d) k = x k - (unit l : Vertex d) k := congrFun h k
  rw [unit_apply_eq_ite, unit_apply_eq_ite, if_pos rfl] at h1
  by_contra hkl
  rw [if_neg hkl] at h1
  omega

theorem add_unit_ne_sub_unit (x : Vertex d) (k l : Fin d) : x + unit k ≠ x - unit l := by
  intro h
  have h1 : x k + (unit k : Vertex d) k = x k - (unit l : Vertex d) k := congrFun h k
  rw [unit_apply_eq_ite, unit_apply_eq_ite, if_pos rfl] at h1
  split_ifs at h1 <;> omega

/-- A lattice neighbour is one of the `2d` vertices `x ± e_k`, and only one. -/
theorem ite_adj_eq_sum_unit (x y : Vertex d) (b : ℝ)
    (hb : ¬(nearestNeighborGraph d).Adj x y → b = 0) :
    b = ∑ k : Fin d, ((if y = x + unit k then b else 0) + (if y = x - unit k then b else 0)) := by
  by_cases hadj : (nearestNeighborGraph d).Adj x y
  · obtain ⟨l, hl | hl⟩ := Graph.Zd.adj_iff.mp hadj
    · subst hl
      rw [Finset.sum_eq_single l]
      · rw [if_pos rfl, if_neg (add_unit_ne_sub_unit x l l), add_zero]
      · intro k _ hkl
        rw [if_neg (fun h => hkl (add_unit_injective x h).symm),
          if_neg (add_unit_ne_sub_unit x l k), add_zero]
      · intro h
        exact absurd (Finset.mem_univ l) h
    · subst hl
      rw [Finset.sum_eq_single l]
      · rw [if_neg (fun h => add_unit_ne_sub_unit x l l h.symm), if_pos rfl, zero_add]
      · intro k _ hkl
        rw [if_neg (fun h => add_unit_ne_sub_unit x k l h.symm),
          if_neg (fun h => hkl (sub_unit_injective x h).symm), add_zero]
      · intro h
        exact absurd (Finset.mem_univ l) h
  · rw [hb hadj]
    simp

/-- **Open neighbours in a finite set are among the `2d` lattice neighbours.** -/
theorem sum_openAdj_eq_sum_unit (S : Finset (Vertex d)) (x : Vertex d) (g : Vertex d → ℝ) :
    ∑ y ∈ S, (if (openGraph ω).Adj x y then g y else 0) =
      ∑ k : Fin d, ((if x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k) then g (x + unit k)
          else 0) +
        (if x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k) then g (x - unit k) else 0)) := by
  have hpt : ∀ y, (if (openGraph ω).Adj x y then g y else 0) = ∑ k : Fin d,
      ((if y = x + unit k then (if (openGraph ω).Adj x y then g y else 0) else 0) +
        (if y = x - unit k then (if (openGraph ω).Adj x y then g y else 0) else 0)) :=
    fun y => ite_adj_eq_sum_unit x y _ fun h => if_neg fun h' => h (openGraph_le ω h')
  rw [Finset.sum_congr rfl fun y _ => hpt y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_and, ite_and]

/-- **Reindexing by a unit step.** -/
theorem sum_sub_unit_eq_sum_add_unit (S : Finset (Vertex d)) (k : Fin d) (h : Vertex d → ℝ) :
    ∑ x ∈ S, (if x - unit k ∈ S then h (x - unit k) else 0) =
      ∑ z ∈ S, (if z + unit k ∈ S then h z else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun x => x - unit k) (fun z => z + unit k) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.2, by rw [sub_add_cancel]; exact hx.1⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.2, by rw [add_sub_cancel_right]; exact hz.1⟩
  · intro x _
    exact sub_add_cancel x (unit k)
  · intro z _
    exact add_sub_cancel_right z (unit k)
  · intro x _
    rfl

/-- **Edges counted from both endpoints.** For a symmetric function of the open edges of a finite
set `S`, the sum over ordered pairs of open neighbours is twice the sum over the edges
`(x, x + e_k)`. -/
theorem sum_sum_openAdj_eq_two_mul_sum_unit (S : Finset (Vertex d))
    (f : Vertex d → Vertex d → ℝ) (hf : ∀ x y, f x y = f y x) :
    ∑ x ∈ S, ∑ y ∈ S, (if (openGraph ω).Adj x y then f x y else 0) =
      2 * ∑ x ∈ S, ∑ k : Fin d,
        (if x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k) then f x (x + unit k) else 0) := by
  set A : Vertex d → Fin d → ℝ := fun x k =>
    if x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k) then f x (x + unit k) else 0 with hA
  set B : Vertex d → Fin d → ℝ := fun x k =>
    if x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k) then f x (x - unit k) else 0 with hB
  have h1 : ∀ x, ∑ y ∈ S, (if (openGraph ω).Adj x y then f x y else 0) =
      ∑ k, A x k + ∑ k, B x k := by
    intro x
    rw [sum_openAdj_eq_sum_unit S x (f x), ← Finset.sum_add_distrib]
  have h2 : ∀ k, ∑ x ∈ S, B x k = ∑ x ∈ S, A x k := by
    intro k
    have e : ∀ x, B x k = if x - unit k ∈ S then
        (if (openGraph ω).Adj (x - unit k) (x - unit k + unit k) then
          f (x - unit k) (x - unit k + unit k) else 0) else 0 := by
      intro x
      simp only [hB, sub_add_cancel]
      by_cases h1 : x - unit k ∈ S
      · by_cases h2 : (openGraph ω).Adj x (x - unit k)
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2.symm, hf]
        · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg (fun h => h2 h.symm)]
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
    simp only [e]
    rw [sum_sub_unit_eq_sum_add_unit S k (fun z => if (openGraph ω).Adj z (z + unit k) then
      f z (z + unit k) else 0)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [hA, ite_and]
  calc ∑ x ∈ S, ∑ y ∈ S, (if (openGraph ω).Adj x y then f x y else 0)
      = ∑ x ∈ S, ∑ k, A x k + ∑ k, ∑ x ∈ S, B x k := by
        rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, Finset.sum_comm (s := S)
          (t := Finset.univ) (f := fun x k => B x k)]
    _ = ∑ x ∈ S, ∑ k, A x k + ∑ k, ∑ x ∈ S, A x k := by
        simp only [h2]
    _ = 2 * ∑ x ∈ S, ∑ k, A x k := by
        rw [Finset.sum_comm (s := Finset.univ) (t := S) (f := fun k x => A x k)]
        ring

/-- **The Dirichlet form of the cluster on the open edges.** -/
theorem cubeForm_eq_sum_edges (U : TriadicCube d) (u : Vertex d → ℝ) :
    cubeForm ω U (fun x => u x) (fun x => u x) =
      ∑ x ∈ crossingClusterVertices ω U, ∑ k : Fin d,
        (if x + unit k ∈ crossingClusterVertices ω U ∧ (openGraph ω).Adj x (x + unit k) then
          (u (x + unit k) - u x) ^ 2 else 0) := by
  set S := crossingClusterVertices ω U
  rw [cubeForm_apply]
  have hinner : ∀ x : ↥S, ∑ y : ↥S, cubeFormTerm ω (fun x => u x) (fun x => u x) x y =
      ∑ y ∈ S, (if (openGraph ω).Adj x.1 y then (u x.1 - u y) ^ 2 else 0) := by
    intro x
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [cubeFormTerm]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun x _ => hinner x]
  rw [Finset.sum_coe_sort S (fun x => ∑ y ∈ S, if (openGraph ω).Adj x y then (u x - u y) ^ 2
    else 0)]
  rw [sum_sum_openAdj_eq_two_mul_sum_unit S (fun x y => (u x - u y) ^ 2) (fun x y => by ring),
    ← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- The cluster conductance of a triadic cube: `1` on the open edges with both endpoints in
`C_*(U)`, `0` elsewhere. -/
noncomputable def cubeCond (ω : Configuration d) (U : TriadicCube d) (e : Edge d) : ℝ :=
  if e.1 ∈ crossingClusterVertices ω U ∧ e.1 + unit e.2 ∈ crossingClusterVertices ω U ∧
      (openGraph ω).Adj e.1 (e.1 + unit e.2) then 1 else 0

theorem cubeCond_eq_zero_or (U : TriadicCube d) (e : Edge d) :
    cubeCond ω U e = 0 ∨ 1 ≤ cubeCond ω U e := by
  unfold cubeCond
  split_ifs
  · exact Or.inr le_rfl
  · exact Or.inl rfl

theorem cubeCond_nonneg (U : TriadicCube d) (e : Edge d) : 0 ≤ cubeCond ω U e := by
  unfold cubeCond
  split_ifs <;> norm_num

theorem cubeCond_le_one (U : TriadicCube d) (e : Edge d) : cubeCond ω U e ≤ 1 := by
  unfold cubeCond
  split_ifs <;> norm_num

/-- **The Laplacian of the cluster conductance** is minus the Laplacian of the cluster. -/
theorem condLaplacian_cubeCond (U : TriadicCube d) (u : Vertex d → ℝ) (x : Vertex d) :
    condLaplacian (cubeCond ω U) u x =
      if x ∈ crossingClusterVertices ω U then
        -∑ y ∈ crossingClusterVertices ω U, (if (openGraph ω).Adj x y then u y - u x else 0)
      else 0 := by
  set S := crossingClusterVertices ω U
  unfold condLaplacian cubeCond
  by_cases hx : x ∈ S
  · rw [if_pos hx, sum_openAdj_eq_sum_unit S x (fun y => u y - u x), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [sub_add_cancel]
    by_cases h1 : x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k)
    · rw [if_pos ⟨hx, h1⟩, if_pos h1]
      by_cases h2 : x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k)
      · rw [if_pos ⟨h2.1, hx, h2.2.symm⟩, if_pos h2]
        ring
      · rw [if_neg (fun h => h2 ⟨h.1, h.2.2.symm⟩), if_neg h2]
        ring
    · rw [if_neg (fun h => h1 h.2), if_neg h1]
      by_cases h2 : x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k)
      · rw [if_pos ⟨h2.1, hx, h2.2.symm⟩, if_pos h2]
        ring
      · rw [if_neg (fun h => h2 ⟨h.1, h.2.2.symm⟩), if_neg h2]
        ring
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [sub_add_cancel]
    rw [if_neg (fun h => hx h.1), if_neg (fun h => hx h.2.1)]
    ring

/-- **Harmonic functions on the cluster are harmonic for the cluster conductance.** If `u`
restricted to `C_*(U)` is in `A_*(U)`, then `u` is `c_U`-harmonic at every vertex of `U` whose
lattice neighbours lie in `U`. -/
theorem condLaplacian_cubeCond_eq_zero {U : TriadicCube d} {u : Vertex d → ℝ}
    (hu : (fun x : ↥(crossingClusterVertices ω U) => u x) ∈ cubeHarmonic ω U) {x : Vertex d}
    (hx : U.IsLatticeInterior x) : condLaplacian (cubeCond ω U) u x = 0 := by
  rw [condLaplacian_cubeCond]
  split_ifs with hxS
  · have h := (mem_cubeHarmonic.1 hu) ⟨x, hxS⟩ hx
    rw [cubeLaplacianAt_apply] at h
    rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)
      (fun y => if (openGraph ω).Adj x y then u y - u x else 0)]
    rw [h, neg_zero]
  · rfl

/-- The energy density of the cluster conductance. -/
noncomputable def cubeEnergy (ω : Configuration d) (U : TriadicCube d) (u : Vertex d → ℝ)
    (y : Vertex d) : ℝ :=
  ∑ k : Fin d, cubeCond ω U (y, k) * (u (y + unit k) - u y) ^ 2

theorem cubeEnergy_nonneg (U : TriadicCube d) (u : Vertex d → ℝ) (y : Vertex d) :
    0 ≤ cubeEnergy ω U u y :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (cubeCond_nonneg U _) (sq_nonneg _)

/-- **The energy density summed over `U` is the energy of the edges inside `U`.** -/
theorem sum_cubeEnergy_eq_innerEdgeEnergy (U : TriadicCube d) (u : Vertex d → ℝ) :
    ∑ y ∈ U.toIntegerCube.vertices, cubeEnergy ω U u y =
      innerEdgeEnergy (cubeCond ω U) U.toIntegerCube u := by
  unfold cubeEnergy innerEdgeEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with h
  · rfl
  · have : cubeCond ω U (y, k) = 0 := by
      unfold cubeCond
      rw [if_neg]
      rintro ⟨-, h2, -⟩
      exact h (Finset.mem_filter.1 h2).1
    rw [this, zero_mul]

/-- **The Dirichlet form of a resolved subcube** is at most the energy density of the larger cube
summed over the subcube. -/
theorem cubeForm_le_sum_cubeEnergy (hd : 0 < d) (hP : PartitionEvent ω) {T U : TriadicCube d}
    (hT : PartitionResolved ω T) (hTU : T.vertices ⊆ U.vertices) (hscale : T.scale ≤ U.scale)
    (u : Vertex d → ℝ) :
    cubeForm ω T (fun x => u x) (fun x => u x) ≤
      ∑ y ∈ T.toIntegerCube.vertices, cubeEnergy ω U u y := by
  rw [cubeForm_eq_sum_edges]
  have hsub := crossingClusterVertices_subset_of_resolved hd hP hT hTU hscale
  have hTsub : crossingClusterVertices ω T ⊆ T.toIntegerCube.vertices := Finset.filter_subset _ _
  refine (Finset.sum_le_sum fun x hx => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hTsub fun y _ _ => cubeEnergy_nonneg U u y)
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h1 : x + unit k ∈ crossingClusterVertices ω T ∧ (openGraph ω).Adj x (x + unit k)
  · have hc : cubeCond ω U (x, k) = 1 := by
      unfold cubeCond
      exact if_pos ⟨hsub hx, hsub h1.1, h1.2⟩
    rw [if_pos h1, hc, one_mul]
  · rw [if_neg h1]
    exact mul_nonneg (cubeCond_nonneg U _) (sq_nonneg _)

end Rigidity.Dirichlet
