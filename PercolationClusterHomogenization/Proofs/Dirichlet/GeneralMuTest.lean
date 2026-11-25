import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralClusterEdges
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeEnergyBounds

/-!
# Testing a harmonic function in `μ` on a subcube of `ℤᵈ`

Let `U` be a triadic cube of `ℤᵈ`, `u` harmonic on `C_*(U)` at the vertices whose lattice
neighbours lie in `U`, and `T ⊆ U` a triadic cube resolved by the partition. On the partition
event, `C_*(T) ⊆ C_*(U)`, and `u` restricted to `C_*(T)` is harmonic on `C_*(T)` at the vertices
whose lattice neighbours lie in `T` (an open neighbour of such a vertex lies in `T` and is joined to
it, hence lies in `C_*(T)`), so it is a competitor in the definition of `μ(T, q)` (Armstrong and
Dario, Definition 4.1). Its Dirichlet form is at most the energy density of the cluster conductance
of `U` summed over `T`, and its coarse pairing is the pairing of `q` with the increments of the
coarsened function `u(z̄(□_𝒫(·)))` over the edges inside `T`. This is the test of Step 1 of the
proof of Lemma 6.2 of the source (display (6.9)), in every dimension (`cubeMu_le_test`); the
planar form is `planarMu_le_test`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

theorem TriadicCube.isLatticeInterior_mono {T U : TriadicCube d} (hTU : T.vertices ⊆ U.vertices)
    {x : Vertex d} (hx : T.IsLatticeInterior x) : U.IsLatticeInterior x :=
  fun y hy => hTU (hx y hy)

/-- **Restriction to a resolved subcube preserves harmonicity.** -/
theorem restrict_mem_cubeHarmonic (hd : 0 < d) (hP : PartitionEvent ω) {T U : TriadicCube d}
    (hTU : T.vertices ⊆ U.vertices) (hT : PartitionResolved ω T) (hscale : T.scale ≤ U.scale)
    {u : Vertex d → ℝ}
    (hu : (fun x : ↥(crossingClusterVertices ω U) => u x) ∈ cubeHarmonic ω U) :
    (fun x : ↥(crossingClusterVertices ω T) => u x) ∈ cubeHarmonic ω T := by
  have hsub := crossingClusterVertices_subset_of_resolved hd hP hT hTU hscale
  rw [mem_cubeHarmonic]
  intro x hx
  have hxU : x.1 ∈ crossingClusterVertices ω U := hsub x.2
  have hU := (mem_cubeHarmonic.1 hu) ⟨x.1, hxU⟩ (TriadicCube.isLatticeInterior_mono hTU hx)
  rw [cubeLaplacianAt_apply] at hU ⊢
  have hU' : ∑ y ∈ crossingClusterVertices ω U,
      (if (openGraph ω).Adj x.1 y then u y - u x.1 else 0) = 0 := by
    rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)
      (fun y => if (openGraph ω).Adj x.1 y then u y - u x.1 else 0)]
    exact hU
  suffices h : ∑ y ∈ crossingClusterVertices ω T,
      (if (openGraph ω).Adj x.1 y then u y - u x.1 else 0) = 0 by
    rw [← Finset.sum_coe_sort (crossingClusterVertices ω T)
      (fun y => if (openGraph ω).Adj x.1 y then u y - u x.1 else 0)] at h
    exact h
  refine (Finset.sum_subset hsub
    (f := fun y => if (openGraph ω).Adj x.1 y then u y - u x.1 else 0)
    fun y _ hyT => ?_).trans hU'
  rw [if_neg]
  intro hadj
  apply hyT
  have hyT' : y ∈ T.vertices := hx y (openGraph_le ω hadj)
  exact mem_crossingClusterVertices.2
    (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 x.2) hyT' hadj)

/-- **The coarse pairing of a function on the lattice** restricted to the cluster is the pairing
of `q` with the increments of the coarsened function over the edges inside `T`. -/
theorem cubeCoarsePairing_restrict (hd : 0 < d) (hP : PartitionEvent ω) {T : TriadicCube d}
    (hT : PartitionResolved ω T) (q : Fin d → ℝ) (u : Vertex d → ℝ) :
    cubeCoarsePairing ω T q (fun x : ↥(crossingClusterVertices ω T) => u x) =
      ∑ i : Fin d, q i * ∑ x ∈ T.toIntegerCube.vertices,
        (if x + unit i ∈ T.toIntegerCube.vertices then
          u (partitionAnchor ω (x + unit i)) - u (partitionAnchor ω x) else 0) := by
  have hA : ∀ z ∈ T.toIntegerCube.vertices,
      cubeExtend ω T (fun x : ↥(crossingClusterVertices ω T) => u x) (partitionAnchor ω z) =
        u (partitionAnchor ω z) := by
    intro z hz
    have hzT := (T.mem_toIntegerCube_vertices z).1 hz
    exact cubeExtend_apply_of_mem _
      (mem_crossingClusterVertices.2 (partitionAnchor_mem_crossingCluster_of_resolved hd hP hT hzT))
  rw [cubeCoarsePairing_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  split_ifs with h
  · rw [hA _ h, hA _ hx]
  · rw [mul_zero]

/-- **The `μ` test on a resolved subcube** (Armstrong and Dario, display (6.9)), in every
dimension. -/
theorem cubeMu_le_test (hd : 0 < d) (hP : PartitionEvent ω) {T U : TriadicCube d}
    (hTU : T.vertices ⊆ U.vertices) (hT : PartitionResolved ω T) (hscale : T.scale ≤ U.scale)
    {u : Vertex d → ℝ}
    (hu : (fun x : ↥(crossingClusterVertices ω U) => u x) ∈ cubeHarmonic ω U) (q : Fin d → ℝ) :
    cubeMu ω T q ≤
      (∑ y ∈ T.toIntegerCube.vertices, cubeEnergy ω U u y) / T.latticeVolume / 2 -
        ∑ i : Fin d, q i * ((∑ x ∈ T.toIntegerCube.vertices,
          (if x + unit i ∈ T.toIntegerCube.vertices then
            u (partitionAnchor ω (x + unit i)) - u (partitionAnchor ω x) else 0)) /
              T.latticeVolume) := by
  have hvol := T.latticeVolume_pos
  have h1 := cubeMu_le hd hP hT q (restrict_mem_cubeHarmonic hd hP hTU hT hscale hu)
  have h2 := cubeForm_le_sum_cubeEnergy hd hP hT hTU hscale u
  rw [cubeCoarsePairing_restrict hd hP hT q u] at h1
  refine h1.trans ?_
  have e : ∑ i : Fin d, q i * ((∑ x ∈ T.toIntegerCube.vertices,
      (if x + unit i ∈ T.toIntegerCube.vertices then
        u (partitionAnchor ω (x + unit i)) - u (partitionAnchor ω x) else 0)) /
          T.latticeVolume) =
      (∑ i : Fin d, q i * ∑ x ∈ T.toIntegerCube.vertices,
        (if x + unit i ∈ T.toIntegerCube.vertices then
          u (partitionAnchor ω (x + unit i)) - u (partitionAnchor ω x) else 0)) /
            T.latticeVolume := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  set X := ∑ i : Fin d, q i * ∑ x ∈ T.toIntegerCube.vertices,
    (if x + unit i ∈ T.toIntegerCube.vertices then
      u (partitionAnchor ω (x + unit i)) - u (partitionAnchor ω x) else 0)
  set E := ∑ y ∈ T.toIntegerCube.vertices, cubeEnergy ω U u y
  rw [show E / T.latticeVolume / 2 - X / T.latticeVolume = (E / 2 - X) / T.latticeVolume by ring]
  exact div_le_div_of_nonneg_right (by linarith) hvol.le

end Rigidity.Dirichlet
