import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralMuTest
import PercolationClusterHomogenization.Proofs.Dirichlet.BoundaryLayer

/-!
# The cluster of a cube of `ℤᵈ` and the clusters of its tiles

Let `U` be resolved by the partition and `T ⊆ U` a resolved triadic cube. A vertex `x` of
`C_*(U)` is joined inside `C_*(U)` to the anchor of its partition cube `□_𝒫(x)` through the parent
of `□_𝒫(x)` and the cube of side `2s − 1` around `x`, `s = 3^{s(x)}`
(`reachable_partitionAnchor_of_mem_crossingCluster`), hence inside the cube of radius `3s` around
`x`. If this cube lies in `T`, then `x ∈ C_*(T)`, the anchor being in `C_*(T)`
(`mem_crossingClusterVertices_of_far`). So the vertices of `C_*(U) ∩ T` outside `C_*(T)` lie in
the boundary layer of `T` of width `3^{k+1} + 1` when all partition cubes have scale at most `k`
(`sdiff_crossingClusterVertices_subset_cubeLayer`), and there are at most
`2d (3^{k+1} + 1) side(T)^{d−1}` of them (`card_sdiff_crossingClusterVertices_le`). This is the
bound `|(C_*(□_m) ∩ (y + □_n)) \ C_*(y + □_n)| ≤ |∂_𝒫(y + □_n)|` in Step 1 of the proof of Armstrong and
Dario, Lemma 6.3, in every dimension; the planar form, for the cluster of the planar partition, is
`card_sdiff_clusterVertices_le`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- **A vertex far from the boundary of a resolved subcube is in the cluster of the subcube.** -/
theorem mem_crossingClusterVertices_of_far (hd : 0 < d) (hP : PartitionEvent ω)
    {U T : TriadicCube d} (hU : PartitionResolved ω U) (hT : PartitionResolved ω T)
    {x : Vertex d} (hx : x ∈ crossingClusterVertices ω U)
    (hfar : ∀ y ∈ cubeAt x (3 ^ ((partitionCube ω x).scale + 1)), y ∈ T.vertices) :
    x ∈ crossingClusterVertices ω T := by
  have hxC := mem_crossingClusterVertices.1 hx
  have hxU := U.crossingCluster_subset ω hxC
  have hpath := reachable_partitionAnchor_of_mem_crossingCluster hd hP hxU (hU x hxU) hxC
  have hreg : U.crossingCluster ω ∩ ((partitionCube ω x).parent.vertices ∪
      cubeAt x (3 ^ (partitionCube ω x).scale - 1)) ⊆ T.vertices := by
    rintro y ⟨-, hy⟩
    refine hfar y ?_
    rcases hy with h | h
    · exact parent_union_cubeAt_subset hP x (Or.inl h)
    · have hle : 3 ^ (partitionCube ω x).scale - 1 ≤ 3 ^ ((partitionCube ω x).scale + 1) :=
        (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
      simp only [cubeAt, Set.mem_setOf_eq] at h ⊢
      exact fun i => (h i).trans (by exact_mod_cast hle)
  have hxT : x ∈ T.vertices := hfar x fun i => by simp
  obtain ⟨root, hroot, hra⟩ := partitionAnchor_mem_crossingCluster_of_resolved hd hP hT hxT
  exact mem_crossingClusterVertices.2
    ⟨root, hroot, hra.trans (reachable_openIn_mono hreg hpath).symm⟩

/-- **The vertices of `C_*(U) ∩ T` outside `C_*(T)` lie in a boundary layer of `T`.** -/
theorem sdiff_crossingClusterVertices_subset_cubeLayer (hd : 0 < d) (hP : PartitionEvent ω)
    {U T : TriadicCube d} (hU : PartitionResolved ω U) (hT : PartitionResolved ω T) {k : ℕ}
    (hk : ∀ x ∈ U.vertices, (partitionCube ω x).scale ≤ k) :
    (crossingClusterVertices ω U).filter (fun x => x ∈ T.vertices) \
        crossingClusterVertices ω T ⊆
      cubeLayer T.toIntegerCube (3 ^ (k + 1) + 1) := by
  intro x hx
  obtain ⟨hxF, hxT⟩ := Finset.mem_sdiff.1 hx
  obtain ⟨hxU, hxTv⟩ := Finset.mem_filter.1 hxF
  have hxTc : x ∈ T.toIntegerCube.vertices := (T.mem_toIntegerCube_vertices x).2 hxTv
  refine Finset.mem_filter.2 ⟨hxTc, ?_⟩
  by_contra hnot
  push Not at hnot
  apply hxT
  refine mem_crossingClusterVertices_of_far hd hP hU hT hxU fun y hy => ?_
  have hxUv := U.crossingCluster_subset ω (mem_crossingClusterVertices.1 hxU)
  have hsk : (3 : ℤ) ^ ((partitionCube ω x).scale + 1) ≤ 3 ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by have := hk x hxUv; omega)
  rw [← T.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
  intro i
  have h1 := hnot i
  have h2 := hy i
  rw [abs_le] at h2
  push_cast at h1 h2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The number of vertices of `C_*(U) ∩ T` outside `C_*(T)`** is at most
`2d (3^{k+1} + 1) side(T)^{d−1}`. -/
theorem card_sdiff_crossingClusterVertices_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U T : TriadicCube d} (hU : PartitionResolved ω U) (hT : PartitionResolved ω T) {k : ℕ}
    (hk : ∀ x ∈ U.vertices, (partitionCube ω x).scale ≤ k) :
    (((crossingClusterVertices ω U).filter (fun x => x ∈ T.vertices) \
        crossingClusterVertices ω T).card : ℝ) ≤
      2 * d * ((3 ^ (k + 1) + 1 : ℕ) : ℝ) * ((3 ^ T.scale : ℕ) : ℝ) ^ (d - 1) := by
  have hsub := sdiff_crossingClusterVertices_subset_cubeLayer hd hP hU hT hk
  have h := (Finset.card_le_card hsub).trans (card_cubeLayer_le T.toIntegerCube (3 ^ (k + 1) + 1))
  have hs : T.toIntegerCube.size = 3 ^ T.scale := rfl
  rw [hs] at h
  exact_mod_cast h

end Rigidity.Dirichlet
