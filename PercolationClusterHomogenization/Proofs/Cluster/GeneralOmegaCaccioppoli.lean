import PercolationClusterHomogenization.Proofs.Cluster.GeneralFlatnessMu
import PercolationClusterHomogenization.Proofs.Cluster.Caccioppoli

/-!
# The Caccioppoli inequality from `□_{n+1}` to `□_n` on the clusters of `ℤ^d`

For a resolved cube `□_{n+1}` and a resolved cube `□_n` (on the partition event), `n ≥ 1`, and a
function `w` on `C_*(□_{n+1})` harmonic at its lattice-interior vertices, the Caccioppoli
inequality (Armstrong and Dario, Lemma 3.5) on the lattice-interior vertices of `C_*(□_{n+1})`,
whose open edges leave this set only at distance at least `3ⁿ - 1` from `□_n`, gives for every
constant `c`

`B_{□_n}(w|_{□_n}, w|_{□_n}) ≤ 8d (3ⁿ - 1)⁻² ∑_{x ∈ C_*(□_{n+1})} (w(x) - c)²`

(`cubeForm_restrict_le_caccioppoli`): the second inequality of display (5.39) of Armstrong and
Dario, in every dimension. The two-dimensional version is
`Rigidity.Percolation.clusterForm_restrict_le_caccioppoli`.
-/

open LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

theorem mem_vertices_originCube_iff {m : ℕ} {x : Vertex d} :
    x ∈ (⟨m, 0⟩ : TriadicCube d).vertices ↔ ∀ i, |2 * x i| < (3 : ℤ) ^ m := by
  change (∀ i, |2 * (x i - (3 : ℤ) ^ m * (0 : Vertex d) i)| < (3 : ℤ) ^ m) ↔ _
  simp

/-- The vertices of `□_n` are lattice-interior to `□_{n+1}`. -/
theorem isLatticeInterior_of_mem_central {n : ℕ} {x : Vertex d}
    (hx : x ∈ (⟨n, 0⟩ : TriadicCube d).vertices) :
    (⟨n + 1, 0⟩ : TriadicCube d).IsLatticeInterior x := by
  intro y hy
  rw [mem_vertices_originCube_iff] at hx ⊢
  intro i
  have h1 := hx i
  have h2 := abs_sub_le_one_of_nearestNeighbor_adj hy i
  have h3 : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at h2
  constructor <;> nlinarith

/-- A vertex of `□_n` is at sup-distance at least `3ⁿ - 1` from every vertex within distance two
of a vertex outside `□_{n+1}`. -/
theorem le_supDist_of_far_general {n : ℕ} {x z y y' : Vertex d}
    (hx : x ∈ (⟨n, 0⟩ : TriadicCube d).vertices) (hzy : ∀ i, |z i - y i| ≤ 1)
    (hyy' : ∀ i, |y i - y' i| ≤ 1) (hy' : y' ∉ (⟨n + 1, 0⟩ : TriadicCube d).vertices) :
    (3 : ℝ) ^ n - 1 ≤ (Rigidity.Proofs.Cluster.supDist x z : ℝ) := by
  rw [mem_vertices_originCube_iff] at hx hy'
  push Not at hy'
  obtain ⟨i, hi⟩ := hy'
  have h1 := hx i
  have h2 := hzy i
  have h3 := hyy' i
  set N : ℤ := 3 ^ n with hN
  have hN1 : (1 : ℤ) ≤ N := one_le_pow₀ (by norm_num)
  rw [pow_succ, ← hN] at hi
  have key : N - 1 ≤ ((x i - z i).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    rw [abs_lt] at h1
    rw [abs_le] at h2 h3
    rcases le_abs'.1 hi with h | h <;> rcases abs_cases (x i - z i) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
      omega
  have hle : (x i - z i).natAbs ≤ Rigidity.Proofs.Cluster.supDist x z :=
    Rigidity.Proofs.Cluster.natAbs_le_supDist x z i
  have key' : (N : ℝ) - 1 ≤ ((x i - z i).natAbs : ℝ) := by
    have h := Int.cast_le (R := ℝ) |>.mpr key
    rw [Int.cast_natCast, Int.cast_sub, Int.cast_one] at h
    exact h
  have hle' : ((x i - z i).natAbs : ℝ) ≤ (Rigidity.Proofs.Cluster.supDist x z : ℝ) := by
    exact_mod_cast hle
  have hNr : (N : ℝ) = (3 : ℝ) ^ n := by rw [hN]; push_cast; rfl
  rw [← hNr]
  linarith

/-- The interior part of the cluster of `□_{n+1}`. -/
noncomputable def interiorCluster (ω : Configuration d) (U : TriadicCube d) : Finset (Vertex d) :=
  (crossingClusterVertices ω U).filter fun x => U.IsLatticeInterior x

/-- The interior vertices of `C_*(□_{n+1})` leave this set by an open edge only far from `□_n`. -/
theorem caccioppoli_dist_general {n : ℕ} :
    ∀ x ∈ crossingClusterVertices ω ⟨n, 0⟩, ∀ z ∈ interiorCluster ω ⟨n + 1, 0⟩,
      (∃ y, (openGraph ω).Adj z y ∧ y ∉ interiorCluster ω ⟨n + 1, 0⟩) →
      (3 : ℝ) ^ n - 1 ≤ (Rigidity.Proofs.Cluster.supDist x z : ℝ) := by
  rintro x hx z hz ⟨y, hzy, hyU'⟩
  obtain ⟨hzC, hzint⟩ := Finset.mem_filter.1 hz
  have hyU : y ∈ (⟨n + 1, 0⟩ : TriadicCube d).vertices := hzint y (openGraph_le ω hzy)
  have hyC : y ∈ crossingClusterVertices ω ⟨n + 1, 0⟩ :=
    mem_crossingClusterVertices.2 (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 hzC)
      hyU hzy)
  have hyint : ¬ (⟨n + 1, 0⟩ : TriadicCube d).IsLatticeInterior y :=
    fun h => hyU' (Finset.mem_filter.2 ⟨hyC, h⟩)
  unfold TriadicCube.IsLatticeInterior at hyint
  push Not at hyint
  obtain ⟨y', hyy', hy'⟩ := hyint
  have hxV : x ∈ (⟨n, 0⟩ : TriadicCube d).vertices :=
    (TriadicCube.mem_toIntegerCube_vertices _ x).1 (Finset.filter_subset _ _ hx)
  exact le_supDist_of_far_general hxV (fun i => abs_sub_le_one_of_openGraph_adj hzy i)
    (fun i => abs_sub_le_one_of_nearestNeighbor_adj hyy' i) hy'

/-- Harmonicity at the interior vertices, in the form of the Caccioppoli inequality. -/
theorem caccioppoli_harm_general {U : TriadicCube d} {w : CubeFun ω U}
    (hw : w ∈ cubeHarmonic ω U) (c : ℝ) :
    ∀ x ∈ interiorCluster ω U, (∀ y, (openGraph ω).Adj x y → y ∈ interiorCluster ω U) →
      openLaplacian ω (fun y => cubeExtend ω U w y - c) x = 0 := by
  intro x hx _
  obtain ⟨hxC, hxint⟩ := Finset.mem_filter.1 hx
  rw [openLaplacian_sub_const]
  refine openLaplacian_cubeExtend_eq_zero hw hxC hxint fun y hy => ?_
  exact mem_crossingClusterVertices.2 (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 hxC)
    (hxint y (openGraph_le ω hy)) hy)

/-- The Dirichlet form on `C_*(V)` of the restriction is at most the sum of the squared gradients
on the vertices of `C_*(V)` inside a larger set. -/
theorem cubeForm_restrict_le_sum_clusterGradSq {U V : TriadicCube d} {S : Finset (Vertex d)}
    (hVS : crossingClusterVertices ω V ⊆ S) (w : CubeFun ω U) (c : ℝ) :
    cubeForm ω V (cubeRestrictExt V w) (cubeRestrictExt V w) ≤
      ∑ x ∈ crossingClusterVertices ω V, clusterGradSq ω S (fun y => cubeExtend ω U w y - c) x := by
  rw [← sum_clusterGradSq_eq_cubeForm]
  refine Finset.sum_le_sum fun x hx => ?_
  unfold clusterGradSq
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have e : ∀ y ∈ ((openGraph ω).neighborFinset x).filter (· ∈ crossingClusterVertices ω V),
      (cubeExtend ω V (cubeRestrictExt V w) x - cubeExtend ω V (cubeRestrictExt V w) y) ^ 2 =
      ((cubeExtend ω U w x - c) - (cubeExtend ω U w y - c)) ^ 2 := by
    intro y hy
    rw [cubeExtend_cubeRestrictExt V w hx, cubeExtend_cubeRestrictExt V w (Finset.mem_filter.1 hy).2]
    ring
  rw [Finset.sum_congr rfl e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => Finset.mem_filter.2
    ⟨(Finset.mem_filter.1 hy).1, hVS (Finset.mem_filter.1 hy).2⟩) fun _ _ _ => sq_nonneg _

/-- **The Caccioppoli inequality from `□_{n+1}` to `□_n`** (Armstrong and Dario, Lemma 3.5, as in
display (5.39), every dimension). -/
theorem cubeForm_restrict_le_caccioppoli (hd : 0 < d) (hP : PartitionEvent ω) {n : ℕ}
    (hn : 1 ≤ n) (hV : PartitionResolved ω ⟨n, 0⟩) {w : CubeFun ω ⟨n + 1, 0⟩}
    (hw : w ∈ cubeHarmonic ω ⟨n + 1, 0⟩) (c : ℝ) :
    cubeForm ω ⟨n, 0⟩ (cubeRestrictExt ⟨n, 0⟩ w) (cubeRestrictExt ⟨n, 0⟩ w) ≤
      8 * d / ((3 : ℝ) ^ n - 1) ^ 2 * ∑ x ∈ crossingClusterVertices ω ⟨n + 1, 0⟩,
        (cubeExtend ω ⟨n + 1, 0⟩ w x - c) ^ 2 := by
  have hVU : (⟨n, 0⟩ : TriadicCube d).vertices ⊆ (⟨n + 1, 0⟩ : TriadicCube d).vertices := by
    intro x hx
    rw [mem_vertices_originCube_iff] at hx ⊢
    intro i
    have h1 := hx i
    have h2 : (3 : ℤ) ^ n ≤ 3 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    linarith
  have hV'U' : crossingClusterVertices ω ⟨n, 0⟩ ⊆ interiorCluster ω ⟨n + 1, 0⟩ := fun x hx =>
    Finset.mem_filter.2 ⟨crossingClusterVertices_subset_of_resolved hd hP hV hVU (Nat.le_succ n) hx,
      isLatticeInterior_of_mem_central
        ((TriadicCube.mem_toIntegerCube_vertices _ x).1 (Finset.filter_subset _ _ hx))⟩
  have h3n : (1 : ℝ) < 3 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (0 : ℝ) < 3 ^ n - 1 := by linarith
  have hcac := caccioppoli_cluster ω _ _ hV'U' hr caccioppoli_dist_general
    (fun y => cubeExtend ω ⟨n + 1, 0⟩ w y - c) (caccioppoli_harm_general hw c)
  have hR : ∑ x ∈ (interiorCluster ω ⟨n + 1, 0⟩).filter
        (fun x => ¬ (x ∈ crossingClusterVertices ω ⟨n, 0⟩ ∧
          ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ crossingClusterVertices ω ⟨n, 0⟩)),
        (cubeExtend ω (⟨n + 1, 0⟩ : TriadicCube d) w x - c) ^ 2 ≤
      ∑ x ∈ crossingClusterVertices ω ⟨n + 1, 0⟩,
        (cubeExtend ω (⟨n + 1, 0⟩ : TriadicCube d) w x - c) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans
      (Finset.filter_subset _ _)) fun x _ _ => sq_nonneg _
  exact (cubeForm_restrict_le_sum_clusterGradSq hV'U' w c).trans
    (hcac.trans (mul_le_mul_of_nonneg_left hR (by positivity)))

end Rigidity.Percolation
