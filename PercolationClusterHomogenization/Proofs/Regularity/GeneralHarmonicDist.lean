import PercolationClusterHomogenization.Proofs.Regularity.GeneralGradNormBound
import PercolationClusterHomogenization.Proofs.Regularity.GeneralHomogenizedGradient
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicComparison

/-!
# The harmonic approximation (7.7) of the coarsened function on one triadic cube

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Steps 1 and 2, in every dimension
`d`, at one scale. With `w` harmonic for the lattice Laplacian on the interior of the lattice cube
`□_{i+3}` and `[u]_𝒫(y) = u(z̄(y))`, `z̄(y)` the anchor of the partition cube of `y`,
`Σ_{□_{i+2}} ([u]_𝒫 - w)² ≤ 2 δ^d Σ_{C_*(□_{i+3})} (u - w)² + 2 |□_{i+2}| (d δ G)²`
(`sum_sq_coarse_sub_homogenized_le_cube`), where `δ` bounds the sides of the partition cubes and
`G` the gradient of `w` (`abs_grad_le_of_cubeInterior_cube`): each anchor is counted at most
`δ^d` times (`sum_partitionAnchor_le_cube`), and `|w(z̄(y)) - w(y)| ≤ d δ G` along a staircase
(`abs_sub_partitionAnchor_homogenized_le_cube`). With the energy and error bounds of Theorem 1 at
the scale `i + 3` this gives `cubeL2_coarse_sub_homogenized_sq_le`. The planar forms are
`sum_sq_coarse_sub_homogenized_le` and `squareL2_coarse_sub_homogenized_sq_le`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Dirichlet Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical

variable {d : ℕ} {ω : Configuration d}

theorem latticeLaplacian_eq_neg_condLaplacian_cube (f : Vertex d → ℝ) (x : Vertex d) :
    latticeLaplacian f x = -condLaplacian (constCond fun _ => (1 : ℝ)) f x := by
  simp only [latticeLaplacian, condLaplacian, constCond, one_mul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The cube `□_{i+2}` lies in the interior of the lattice cube `□_{i+3}`. -/
theorem mem_cubeInterior_of_mem_cubeFinset {i : ℕ} {y : Vertex d}
    (hy : y ∈ triadicCubeFinset d (i + 2) 0) :
    y ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube := by
  unfold cubeInterior
  rw [Finset.mem_filter, IntegerCube.mem_vertices]
  have hc := two_mul_toIntegerCube_corner_add_cube (d := d) (i + 3)
  have hs := cast_toIntegerCube_size_zero_cube (d := d) (i + 3)
  have h3 : (3 : ℤ) ^ (i + 3) = 3 * 3 ^ (i + 2) := by ring
  have hpos : (1 : ℤ) ≤ 3 ^ (i + 2) := one_le_pow₀ (by norm_num)
  have hy' := mem_cubeFinset_iff_int.1 hy
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have h1 := hc k
    have h2 := hy' k
    have h4 := le_abs_self (y k)
    have h5 := neg_abs_le (y k)
    rw [hs]
    generalize |y k| = a at h2 h4 h5
    generalize (3 : ℤ) ^ (i + 2) = T at h2 h3 hpos
    generalize (3 : ℤ) ^ (i + 3) = T' at h1 h3 ⊢
    constructor <;> omega
  · have h1 := hc k
    have h2 := hy' k
    have h4 := le_abs_self (y k)
    have h5 := neg_abs_le (y k)
    rw [hs]
    generalize |y k| = a at h2 h4 h5
    generalize (3 : ℤ) ^ (i + 2) = T at h2 h3 hpos
    generalize (3 : ℤ) ^ (i + 3) = T' at h1 h3 ⊢
    constructor <;> omega

theorem mem_cubeLatticeHarmonic_of_cubeInterior {i : ℕ} {w : Vertex d → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) :
    w ∈ cubeLatticeHarmonic d (i + 2) := by
  intro y hy
  rw [latticeLaplacian_eq_neg_condLaplacian_cube,
    hw y (mem_cubeInterior_of_mem_cubeFinset hy), neg_zero]

/-- The restriction to `C_*(U)` of a function harmonic on the cluster at the lattice-interior
vertices of `C_*(U)` lies in `A_*(U)`. -/
theorem extend_mem_cubeHarmonic {U : TriadicCube d} (C : OpenComponent ω) {u : C → ℝ}
    (hsub : ∀ x ∈ crossingClusterVertices ω U, x ∈ C.supp)
    (hharm : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ crossingClusterVertices ω U →
      U.IsLatticeInterior x → componentLaplacian C u ⟨x, hx⟩ = 0) :
    (fun x : ↥(crossingClusterVertices ω U) => Rigidity.Section3.extend C u x) ∈
      cubeHarmonic ω U := by
  rw [mem_cubeHarmonic]
  intro x hint
  have hxC := hsub x.1 x.2
  have h0 := hharm x.1 hxC x.2 hint
  rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C u x.1 hxC, ← Finset.sum_filter] at h0
  rw [cubeLaplacianAt_apply]
  have e1 : ∑ y : ↥(crossingClusterVertices ω U), (if (openGraph ω).Adj x.1 y.1 then
      Rigidity.Section3.extend C u y - Rigidity.Section3.extend C u x else 0) =
      ∑ y ∈ crossingClusterVertices ω U, (if (openGraph ω).Adj x.1 y then
        Rigidity.Section3.extend C u y - Rigidity.Section3.extend C u x.1 else 0) := by
    rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)]
  rw [e1, ← Finset.sum_filter]
  have hset : (crossingClusterVertices ω U).filter (fun y => (openGraph ω).Adj x.1 y) =
      ((lattice d).neighborFinset x.1).filter (fun y => (openGraph ω).Adj x.1 y) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨-, hy⟩
      exact ⟨openGraph_le ω hy, hy⟩
    · rintro ⟨-, hy⟩
      exact ⟨mem_crossingClusterVertices_of_adj x.2 (hint y (openGraph_le ω hy)) hy, hy⟩
  rw [hset]
  exact h0

set_option maxHeartbeats 400000 in
/-- **The anchors on `□_{i+2}`**: the sum over `□_{i+2}` of a nonnegative function at the anchors
is at most `δ^d` times its sum over `C_*(□_{i+3})`. -/
theorem sum_partitionAnchor_le_cube (hd : 0 < d) (hP : PartitionEvent ω) {i : ℕ}
    (hres : PartitionResolved ω ⟨i + 3, 0⟩) {φ : Vertex d → ℝ} (hφ : ∀ z, 0 ≤ φ z) {δ : ℝ}
    (hδ : ∀ y ∈ triadicCubeFinset d (i + 3) 0, (3 : ℝ) ^ (partitionCube ω y).scale ≤ δ) :
    ∑ y ∈ triadicCubeFinset d (i + 2) 0, φ (partitionAnchor ω y) ≤
      δ ^ d * ∑ z ∈ crossingClusterVertices ω ⟨i + 3, 0⟩, φ z := by
  have hsub : (triadicCubeFinset d (i + 2) 0).image (partitionAnchor ω) ⊆
      crossingClusterVertices ω ⟨i + 3, 0⟩ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    have hyU : y ∈ (⟨i + 3, 0⟩ : TriadicCube d).vertices :=
      mem_cubeFinset_iff_vertices.1 (mem_cubeFinset_mono (by omega) hy)
    exact mem_crossingClusterVertices.2
      (partitionAnchor_mem_crossingCluster_of_resolved hd hP hres hyU)
  rw [Finset.sum_comp]
  have hcount : ∀ z ∈ (triadicCubeFinset d (i + 2) 0).image (partitionAnchor ω),
      (((triadicCubeFinset d (i + 2) 0).filter fun y => partitionAnchor ω y = z).card : ℝ) ≤
        δ ^ d := by
    intro z hz
    have hzU := hsub hz
    have hzsq : z ∈ triadicCubeFinset d (i + 3) 0 :=
      mem_cubeFinset_of_mem_crossingClusterVertices hzU
    have hle : ((triadicCubeFinset d (i + 2) 0).filter fun y => partitionAnchor ω y = z) ⊆
        (partitionCube ω z).toIntegerCube.vertices := by
      intro y hy
      obtain ⟨-, hyz⟩ := Finset.mem_filter.1 hy
      have hzQ : z ∈ (partitionCube ω y).vertices := by
        rw [← hyz]
        exact partitionAnchor_mem hP y
      rw [TriadicCube.mem_toIntegerCube_vertices, partitionCube_eq_of_mem hP hzQ]
      exact mem_partitionCube hP y
    have hcard := Finset.card_le_card hle
    rw [IntegerCube.card_vertices_eq] at hcard
    have h1 : (((triadicCubeFinset d (i + 2) 0).filter fun y =>
        partitionAnchor ω y = z).card : ℝ) ≤
          (((partitionCube ω z).toIntegerCube.size ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
    have h2 : (((partitionCube ω z).toIntegerCube.size ^ d : ℕ) : ℝ) =
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ d := by
      change (((3 ^ (partitionCube ω z).scale : ℕ) ^ d : ℕ) : ℝ) = _
      push_cast; rfl
    rw [h2] at h1
    exact h1.trans (pow_le_pow_left₀ (by positivity) (hδ z hzsq) d)
  calc ∑ z ∈ (triadicCubeFinset d (i + 2) 0).image (partitionAnchor ω),
        ((triadicCubeFinset d (i + 2) 0).filter fun y => partitionAnchor ω y = z).card • φ z
      ≤ ∑ z ∈ (triadicCubeFinset d (i + 2) 0).image (partitionAnchor ω), δ ^ d * φ z :=
        Finset.sum_le_sum fun z hz => by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hcount z hz) (hφ z)
    _ = δ ^ d * ∑ z ∈ (triadicCubeFinset d (i + 2) 0).image (partitionAnchor ω), φ z :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ δ ^ d * ∑ z ∈ crossingClusterVertices ω ⟨i + 3, 0⟩, φ z := by
        have hδ0 : 0 ≤ δ := by
          obtain ⟨y, hy⟩ : (triadicCubeFinset d (i + 3) 0).Nonempty :=
            ⟨0, mem_cubeFinset_iff_int.2 fun k => by simp⟩
          exact (by positivity : (0 : ℝ) ≤ 3 ^ (partitionCube ω y).scale).trans (hδ y hy)
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hφ z) (by positivity)

/-- The coordinates of two vertices of a triadic cube differ by less than its side. -/
theorem abs_sub_lt_side_of_mem {Q : TriadicCube d} {x y : Vertex d} (hx : x ∈ Q.vertices)
    (hy : y ∈ Q.vertices) (k : Fin d) : |x k - y k| < 3 ^ Q.scale := by
  have h1 : |2 * (x k - Q.side * Q.index k)| < Q.side := hx k
  have h2 : |2 * (y k - Q.side * Q.index k)| < Q.side := hy k
  rw [abs_mul, abs_two] at h1 h2
  have hs : Q.side = 3 ^ Q.scale := rfl
  have := abs_sub_le (x k) (Q.side * Q.index k) (y k)
  rw [abs_sub_comm (Q.side * Q.index k) (y k)] at this
  rw [← hs]
  linarith

/-- **The homogenized solution at the anchors**: for `w` harmonic on the interior of `□_{i+3}`,
partition cubes of scale at most `i` on `□_{i+2}` with sides at most `δ`, and `T ≥ 1` with
`2 d (T + 2) + 2 T + 3 ≤ 16 · 3^i`, `|w(z̄(y)) - w(y)| ≤ d δ G` for `y ∈ □_{i+2}`, `G` the
interior gradient bound of `abs_grad_le_of_cubeInterior_cube`. -/
theorem abs_sub_partitionAnchor_homogenized_le_cube (hd : 0 < d) (hP : PartitionEvent ω)
    {i T : ℕ} (hT : 0 < T)
    (hTi : 2 * (((d * (T + 2) : ℕ) : ℤ)) + 2 * (T : ℤ) + 3 ≤ 16 * 3 ^ i) {w : Vertex d → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0)
    {δ : ℝ} {y : Vertex d} (hy : y ∈ triadicCubeFinset d (i + 2) 0)
    (hδ : (3 : ℝ) ^ (partitionCube ω y).scale ≤ δ) (hsmall : (partitionCube ω y).scale ≤ i) :
    |w (partitionAnchor ω y) - w y| ≤ d * δ * (2 ^ d * (√((10 * (d : ℝ)) ^ d) /
      √((T : ℝ) ^ d)) * √(innerEdgeEnergy (constCond fun _ => (1 : ℝ))
        (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube w)) := by
  set Q := partitionCube ω y with hQ
  have hyQ : y ∈ Q.vertices := mem_partitionCube hP y
  have haQ : partitionAnchor ω y ∈ Q.vertices := partitionAnchor_mem hP y
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) *
      √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube
        w) := ⟨_, rfl⟩
  rw [← hG]
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hsc : (3 : ℤ) ^ Q.scale ≤ 3 ^ i := pow_le_pow_right₀ (by norm_num) hsmall
  have h32 : (3 : ℤ) ^ (i + 2) = 9 * 3 ^ i := by ring
  have h33 : (3 : ℤ) ^ (i + 3) = 27 * 3 ^ i := by ring
  have hbound := abs_sub_le_of_grad_le_cube w y (partitionAnchor ω y) (G := G) fun p hp l => by
    rw [hG]
    refine abs_grad_le_of_cubeInterior_cube hd hT hw (fun k => ?_) l
    have a1 := hp k
    have a2 := (mem_cubeFinset_iff_int.1 hy) k
    have a3 := abs_sub_lt_side_of_mem hyQ haQ k
    have b1 := le_abs_self (y k)
    have b2 := neg_abs_le (y k)
    have b5 := le_abs_self (y k - partitionAnchor ω y k)
    have b6 := neg_abs_le (y k - partitionAnchor ω y k)
    rw [h32] at a2
    rw [h33]
    rcases abs_cases (p k) with ⟨hpk, _⟩ | ⟨hpk, _⟩ <;> rw [hpk] <;>
    generalize |y k| = c1 at a2 b1 b2 <;>
    generalize |y k - partitionAnchor ω y k| = c3 at a3 b5 b6
    <;> generalize (3 : ℤ) ^ Q.scale = S at a3 hsc
    <;> generalize (3 : ℤ) ^ i = T' at hsc a2 hTi ⊢
    <;> generalize (((d * (T + 2) : ℕ) : ℤ)) = D at hTi ⊢
    <;> rcases min_cases (y k) (partitionAnchor ω y k) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
    rcases max_cases (y k) (partitionAnchor ω y k) with ⟨hM, _⟩ | ⟨hM, _⟩ <;>
    rw [hm, hM] at a1 <;> omega
  have hlen : (((∑ k, |partitionAnchor ω y k - y k|) : ℤ) : ℝ) ≤ d * (3 : ℝ) ^ Q.scale := by
    have e : ∀ k, |partitionAnchor ω y k - y k| ≤ 3 ^ Q.scale := by
      intro k
      have := abs_sub_lt_side_of_mem haQ hyQ k
      linarith
    have hZ : (∑ k, |partitionAnchor ω y k - y k| : ℤ) ≤ ∑ _k : Fin d, (3 : ℤ) ^ Q.scale :=
      Finset.sum_le_sum fun k _ => e k
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hZ
    have : ((∑ k, |partitionAnchor ω y k - y k| : ℤ) : ℝ) ≤
        (((d : ℤ) * 3 ^ Q.scale : ℤ) : ℝ) := by exact_mod_cast hZ
    simpa using this
  calc |w (partitionAnchor ω y) - w y|
      ≤ (((∑ k, |partitionAnchor ω y k - y k|) : ℤ) : ℝ) * G := hbound
    _ ≤ d * (3 : ℝ) ^ Q.scale * G := mul_le_mul_of_nonneg_right hlen hG0
    _ ≤ d * δ * G := by gcongr

/-- **The coarsened function against the homogenized solution on `□_{i+2}`**. -/
theorem sum_sq_coarse_sub_homogenized_le_cube (hd : 0 < d) (hP : PartitionEvent ω)
    (C : OpenComponent ω) (u : C → ℝ) {i T : ℕ} (hT : 0 < T)
    (hTi : 2 * (((d * (T + 2) : ℕ) : ℤ)) + 2 * (T : ℤ) + 3 ≤ 16 * 3 ^ i)
    (hres : PartitionResolved ω ⟨i + 3, 0⟩) {w : Vertex d → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) {δ : ℝ}
    (hδ : ∀ y ∈ triadicCubeFinset d (i + 3) 0, (3 : ℝ) ^ (partitionCube ω y).scale ≤ δ)
    (hsmall : ∀ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCube ω y).scale ≤ i) :
    ∑ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCoarse C u y - w y) ^ 2 ≤
      2 * δ ^ d * ∑ z ∈ crossingClusterVertices ω ⟨i + 3, 0⟩,
          (Rigidity.Section3.extend C u z - w z) ^ 2 +
        2 * ((3 : ℝ) ^ (i + 2)) ^ d * (d * δ * (2 ^ d * (√((10 * (d : ℝ)) ^ d) /
          √((T : ℝ) ^ d)) * √(innerEdgeEnergy (constCond fun _ => (1 : ℝ))
            (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube w))) ^ 2 := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = d * δ * (2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) *
      √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube
        w)) := ⟨_, rfl⟩
  rw [← hG]
  have hpt : ∀ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCoarse C u y - w y) ^ 2 ≤
      2 * (Rigidity.Section3.extend C u (partitionAnchor ω y) - w (partitionAnchor ω y)) ^ 2 +
        2 * G ^ 2 := by
    intro y hy
    have hyU : y ∈ triadicCubeFinset d (i + 3) 0 := mem_cubeFinset_mono (by omega) hy
    have hb := abs_sub_partitionAnchor_homogenized_le_cube hd hP hT hTi hw hy (hδ y hyU)
      (hsmall y hy)
    rw [← hG] at hb
    have hb2 : (w (partitionAnchor ω y) - w y) ^ 2 ≤ G ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have e : partitionCoarse C u y - w y =
        (Rigidity.Section3.extend C u (partitionAnchor ω y) - w (partitionAnchor ω y)) +
          (w (partitionAnchor ω y) - w y) := by
      unfold partitionCoarse; ring
    rw [e]
    nlinarith [sq_nonneg ((Rigidity.Section3.extend C u (partitionAnchor ω y) -
      w (partitionAnchor ω y)) - (w (partitionAnchor ω y) - w y))]
  have hA := sum_partitionAnchor_le_cube hd hP hres
    (φ := fun z => (Rigidity.Section3.extend C u z - w z) ^ 2) (fun z => sq_nonneg _) hδ
  calc ∑ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCoarse C u y - w y) ^ 2
      ≤ ∑ y ∈ triadicCubeFinset d (i + 2) 0,
          (2 * (Rigidity.Section3.extend C u (partitionAnchor ω y) -
            w (partitionAnchor ω y)) ^ 2 + 2 * G ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * ∑ y ∈ triadicCubeFinset d (i + 2) 0,
          (Rigidity.Section3.extend C u (partitionAnchor ω y) - w (partitionAnchor ω y)) ^ 2 +
        2 * ((3 : ℝ) ^ (i + 2)) ^ d * G ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
          card_triadicCubeFinset_real]
        ring
    _ ≤ 2 * (δ ^ d * ∑ z ∈ crossingClusterVertices ω ⟨i + 3, 0⟩,
          (Rigidity.Section3.extend C u z - w z) ^ 2) + 2 * ((3 : ℝ) ^ (i + 2)) ^ d * G ^ 2 := by
        gcongr
    _ = _ := by ring

/-- The sum of squares from the error bound of Theorem 1. -/
theorem sum_sq_le_of_homogenizationError_cube {m : ℕ} {S X : ℝ} (hS : 0 ≤ S)
    (h : (3 : ℝ) ^ (-(m : ℝ)) * √(S / ((3 : ℝ) ^ m) ^ d) ≤ X) :
    S ≤ ((3 : ℝ) ^ m) ^ d * ((3 : ℝ) ^ m) ^ 2 * X ^ 2 := by
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_mul_le_iff₀ h3] at h
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)] at hsq
  calc S ≤ (3 ^ m * X) ^ 2 * ((3 : ℝ) ^ m) ^ d := hsq
    _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **(7.7) on one cube** in terms of the gradient norm `M` of Theorem 1: for `w` harmonic on the
interior of `□_{i+3}` with the energy and error bounds of Theorem 1 at the scale `i + 3`,
`‖[u]_𝒫 - w‖²_{L̲²(□_{i+2})} ≤
  (2 δ^d 3^d (3^{i+3})² C² P² + 2 d² δ² 4^d (10 d)^d (3^{i+3})^d T^{-d} C) M²`,
`P = 3^{-α(i+3)}`. -/
theorem cubeL2_coarse_sub_homogenized_sq_le (hd : 0 < d) (hP : PartitionEvent ω)
    (C : OpenComponent ω) (u : C → ℝ) {i T : ℕ} (hT : 0 < T)
    (hTi : 2 * (((d * (T + 2) : ℕ) : ℤ)) + 2 * (T : ℤ) + 3 ≤ 16 * 3 ^ i)
    (hres : PartitionResolved ω ⟨i + 3, 0⟩) {w : Vertex d → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ y ∈ triadicCubeFinset d (i + 3) 0, (3 : ℝ) ^ (partitionCube ω y).scale ≤ δ)
    (hsmall : ∀ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCube ω y).scale ≤ i)
    {Ch P M : ℝ}
    (hE : innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube
      w / ((3 : ℝ) ^ (i + 3)) ^ d ≤ Ch * M ^ 2)
    (hL : (3 : ℝ) ^ (-((i + 3 : ℕ) : ℝ)) * √((∑ x ∈ crossingClusterVertices ω ⟨i + 3, 0⟩,
        (Rigidity.Section3.extend C u x - w x) ^ 2) / ((3 : ℝ) ^ (i + 3)) ^ d) ≤ Ch * P * M) :
    cubeL2 d (i + 2) (fun y => partitionCoarse C u y - w y) ^ 2 ≤
      (2 * δ ^ d * 3 ^ d * ((3 : ℝ) ^ (i + 3)) ^ 2 * Ch ^ 2 * P ^ 2 +
        2 * (d : ℝ) ^ 2 * δ ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
          (((3 : ℝ) ^ (i + 3)) ^ d / (T : ℝ) ^ d) * Ch) * M ^ 2 := by
  have hB := sum_sq_coarse_sub_homogenized_le_cube hd hP C u hT hTi hres hw hδ hsmall
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ x ∈ crossingClusterVertices ω ⟨i + 3, 0⟩,
      (Rigidity.Section3.extend C u x - w x) ^ 2 := ⟨_, rfl⟩
  rw [← hSdef] at hB hL
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS := sum_sq_le_of_homogenizationError_cube hS0 hL
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = innerEdgeEnergy (constCond fun _ => (1 : ℝ))
      (⟨i + 3, 0⟩ : TriadicCube d).toIntegerCube w := ⟨_, rfl⟩
  rw [← hIdef] at hB hE
  have hI0 : 0 ≤ I := by
    rw [hIdef]; unfold innerEdgeEnergy
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (by simp [constCond]) (sq_nonneg _)
  set N3 : ℝ := ((3 : ℝ) ^ (i + 3)) ^ d with hN3
  set N2 : ℝ := ((3 : ℝ) ^ (i + 2)) ^ d with hN2
  have hN3pos : 0 < N3 := by positivity
  have hN2pos : 0 < N2 := by positivity
  have hN32 : N3 = 3 ^ d * N2 := by
    rw [hN3, hN2, ← mul_pow, pow_succ]; ring
  have hI : I ≤ N3 * (Ch * M ^ 2) := by
    rwa [div_le_iff₀ hN3pos, mul_comm] at hE
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTd : (0 : ℝ) < (T : ℝ) ^ d := by positivity
  have hG : (d * δ * (2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) * √I)) ^ 2 ≤
      (d : ℝ) ^ 2 * δ ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d * (N3 / (T : ℝ) ^ d) *
        (Ch * M ^ 2) := by
    have hs1 : (√((10 * (d : ℝ)) ^ d)) ^ 2 = (10 * (d : ℝ)) ^ d := Real.sq_sqrt (by positivity)
    have hs2 : (√((T : ℝ) ^ d)) ^ 2 = (T : ℝ) ^ d := Real.sq_sqrt hTd.le
    have hs3 : (√I) ^ 2 = I := Real.sq_sqrt hI0
    have h4 : ((2 : ℝ) ^ d) ^ 2 = 4 ^ d := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hdiv : I / (T : ℝ) ^ d ≤ N3 / (T : ℝ) ^ d * (Ch * M ^ 2) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hI hTd.le
    calc (d * δ * (2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) * √I)) ^ 2
        = (d : ℝ) ^ 2 * δ ^ 2 * ((2 : ℝ) ^ d) ^ 2 * (√((10 * (d : ℝ)) ^ d)) ^ 2 *
            ((√I) ^ 2 / (√((T : ℝ) ^ d)) ^ 2) := by ring
      _ = (d : ℝ) ^ 2 * δ ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d * (I / (T : ℝ) ^ d) := by
          rw [h4, hs1, hs2, hs3]
      _ ≤ (d : ℝ) ^ 2 * δ ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
            (N3 / (T : ℝ) ^ d * (Ch * M ^ 2)) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  unfold cubeL2
  rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)),
    div_le_iff₀ hN2pos]
  have hδd : 0 ≤ δ ^ d := pow_nonneg hδ0 d
  calc ∑ y ∈ triadicCubeFinset d (i + 2) 0, (partitionCoarse C u y - w y) ^ 2
      ≤ 2 * δ ^ d * S + 2 * N2 *
          (d * δ * (2 ^ d * (√((10 * (d : ℝ)) ^ d) / √((T : ℝ) ^ d)) * √I)) ^ 2 := hB
    _ ≤ 2 * δ ^ d * (N3 * ((3 : ℝ) ^ (i + 3)) ^ 2 * (Ch * P * M) ^ 2) +
          2 * N2 * ((d : ℝ) ^ 2 * δ ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d * (N3 / (T : ℝ) ^ d) *
            (Ch * M ^ 2)) := by
        gcongr
    _ = (2 * δ ^ d * 3 ^ d * ((3 : ℝ) ^ (i + 3)) ^ 2 * Ch ^ 2 * P ^ 2 +
          2 * (d : ℝ) ^ 2 * δ ^ 2 * 4 ^ d * (10 * (d : ℝ)) ^ d *
            (N3 / (T : ℝ) ^ d) * Ch) * M ^ 2 * N2 := by
        rw [hN32]; ring

end Rigidity.Proofs.Regularity
