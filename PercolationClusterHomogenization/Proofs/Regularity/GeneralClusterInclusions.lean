import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicApproximationCubes
import PercolationClusterHomogenization.Proofs.Partition.Paths
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeEnergy

/-!
# The crossing clusters of the triadic cubes and the infinite cluster in every dimension

The proofs of Lemmas 7.1 and 7.3 of Armstrong and Dario (arXiv:1609.09431v2) use two inclusions
between the clusters `C_*(□_j)` of the triadic cubes and the infinite cluster `𝒞_∞`, valid above
the minimal scale: `C_*(□_j) ⊆ 𝒞_∞`, and `𝒞_∞ ∩ □_m ⊆ C_*(□_{m + 1})` ("due to the definition of
`𝒳`", proof of Lemma 7.3). For the partition into good cubes in every dimension:

* if the cube `U` is resolved and meets an infinite open cluster `C`, then `C_*(U) ⊆ C`
  (`mem_supp_of_mem_crossingClusterVertices`): a vertex of `C ∩ U` is joined to the anchor of its
  partition cube, which lies in `C_*(U)`, and `C_*(U)` is connected;
* if the partition cubes of the vertices of `□_m` have scale at most `m - 2`, every vertex of an
  infinite open cluster in `□_m` lies in `C_*(□_{m + 1})` (`mem_crossingClusterVertices_succ`): it
  is joined to the anchor of its partition cube inside the cube of radius `3^{s+1}` around it,
  which lies in `□_{m + 1}`, and the anchor lies in `C_*(□_{m + 1})`.

The planar forms are `mem_supp_of_mem_clusterVertices` and `mem_clusterVertices_succ`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

variable {d : ℕ} {ω : Configuration d}

/-- **The crossing cluster of a resolved cube lies in the infinite cluster it meets.** -/
theorem mem_supp_of_mem_crossingClusterVertices (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) {x₀ : Vertex d} (hx₀U : x₀ ∈ U.vertices) (hx₀C : x₀ ∈ C.supp)
    {y : Vertex d} (hy : y ∈ crossingClusterVertices ω U) : y ∈ C.supp := by
  have hC : (openGraph ω).connectedComponentMk x₀ = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx₀C
  have hx₀inf : ((openGraph ω).connectedComponentMk x₀).supp.Infinite := by rw [hC]; exact hinf
  have h1 : (openGraph ω).Reachable x₀ (partitionAnchor ω x₀) := by
    refine (reachable_partitionAnchor_of_infinite hd hP hx₀inf).mono ?_
    intro a b h
    exact h.1
  have hanc : partitionAnchor ω x₀ ∈ U.crossingCluster ω :=
    crossingCluster_partitionCube_subset hd hP hx₀U (hU x₀ hx₀U)
      (partitionAnchor_mem_crossingCluster hP x₀)
  obtain ⟨W, -⟩ := joinedWithin_crossingClusterVertices hd hP hU
    (mem_crossingClusterVertices.1 hy) hanc
  have hr : (openGraph ω).Reachable y x₀ := W.reachable.trans h1.symm
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, ← hC]
  exact SimpleGraph.ConnectedComponent.eq.2 hr

/-- **A vertex of an infinite cluster in `□_m` lies in `C_*(□_{m + 1})`** when the partition
cubes of the vertices of `□_m` have scale at most `m - 2`. -/
theorem mem_crossingClusterVertices_succ (hd : 0 < d) (hP : PartitionEvent ω)
    (C : OpenComponent ω) (hinf : C.supp.Infinite) {m : ℕ}
    (hsize : ∀ x ∈ triadicCubeFinset d m 0, (partitionCube ω x).scale + 2 ≤ m) {x : Vertex d}
    (hx : x ∈ triadicCubeFinset d m 0) (hxC : x ∈ C.supp) :
    x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩ := by
  have hC : (openGraph ω).connectedComponentMk x = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hxC
  have hxinf : ((openGraph ω).connectedComponentMk x).supp.Infinite := by rw [hC]; exact hinf
  set Q := partitionCube ω x with hQdef
  have hs : Q.scale + 2 ≤ m := hsize x hx
  have hxm := mem_cubeFinset_iff_int.1 hx
  -- the cube of radius `3^{s+1}` around `x` lies in `□_{m + 1}`
  have hsub : Q.parent.vertices ∪ cubeAt x (3 ^ Q.scale / 2) ⊆
      (⟨m + 1, 0⟩ : TriadicCube d).vertices := by
    intro y hy
    have hy' := parent_union_cubeAt_subset hP x hy
    rw [mem_triadicCube_zero_iff']
    intro i
    have hyi : |y i - x i| ≤ ((3 ^ (Q.scale + 1) : ℕ) : ℤ) := hy' i
    have hpow : (3 : ℤ) * 3 ^ (Q.scale + 1) ≤ 3 ^ m := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hcast : (((3 ^ (Q.scale + 1) : ℕ) : ℤ)) = (3 : ℤ) ^ (Q.scale + 1) := by norm_num
    rw [hcast] at hyi
    have hm1 : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
    rw [hm1]
    have hxi := hxm i
    have ha := abs_sub_abs_le_abs_sub (y i) (x i)
    have hb := abs_nonneg (x i)
    have hpos : (0 : ℤ) ≤ 3 ^ (Q.scale + 1) := by positivity
    linarith
  have hreach : (openIn ω (⟨m + 1, 0⟩ : TriadicCube d).vertices).Reachable x
      (partitionAnchor ω x) :=
    reachable_openIn_mono hsub (reachable_partitionAnchor_of_infinite hd hP hxinf)
  have hxm1 : x ∈ (⟨m + 1, 0⟩ : TriadicCube d).vertices := by
    rw [mem_triadicCube_zero_iff']
    intro i
    have := hxm i
    have h3 : (3 : ℤ) ^ m ≤ 3 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨root, hroot, hra⟩ := crossingCluster_partitionCube_subset hd hP hxm1
    (show Q.scale ≤ (⟨m + 1, 0⟩ : TriadicCube d).scale from by
      show Q.scale ≤ m + 1
      omega)
    (partitionAnchor_mem_crossingCluster hP x)
  exact mem_crossingClusterVertices.2 ⟨root, hroot, hra.trans hreach.symm⟩

end Rigidity.Proofs.Regularity
