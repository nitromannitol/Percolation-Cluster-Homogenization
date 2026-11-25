import PercolationClusterHomogenization.Proofs.Dirichlet.GridTiles
import PercolationClusterHomogenization.Proofs.Dirichlet.LemmaSixThreeCoarse

/-!
# The faces of the tiles of a block

The step `x ↦ x + e_j` across the upper face `j` of a tile of the triadic grid lands in the next
tile in the direction `j` (`add_unit_mem_next_tile`), and the tiles of a block inside
`shrinkCube □_m (r + 3)` are triadic cubes inside `□_m` (`gridTile_vertices_subset_of_block`).
The squared slopes of a function on the tiles of a block sum to at most `N^{-d}` times its energy
(`sum_sq_cubeSlope_tiles_le`). These are the face and block conditions and the slope bound of the
proof of Lemma 6.3 of Armstrong and Dario, in every dimension.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The step across the upper face of a tile lands on the lower face of the next tile, where it
is not interior. -/
theorem add_unit_mem_next_tile {k : ℕ} {z₀ : Vertex d} {i x : Vertex d} {j : Fin d}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).upperFace j) :
    x + unit j ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • (i + unit j)) (3 ^ k)).vertices := by
  obtain ⟨hxv, hface⟩ := (IntegerCube.mem_upperFace _ j x).1 hx
  rw [IntegerCube.mem_vertices] at hxv ⊢
  intro t
  have h := hxv t
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply]
    at h hface ⊢
  by_cases htj : t = j
  · subst htj
    simp only [if_true] at h ⊢
    constructor <;> nlinarith
  · simp only [if_neg htj, add_zero] at h ⊢
    exact h

/-- The tiles of a block inside `shrinkCube □_m (r + 3)` are triadic cubes inside `□_m`. -/
theorem gridTile_vertices_subset_of_block {m k : ℕ} {z₀ : Vertex d}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {M r : ℕ}
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (r + 3)).vertices)
    {i : Vertex d} (hi : i ∈ (cornerCube 0 (M + 1)).vertices) :
    (gridTile k z₀ i).vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices := by
  intro y hy
  rw [← TriadicCube.mem_toIntegerCube_vertices, gridTile_toIntegerCube hz₀] at hy
  have h1 := hsub (tile_subset z₀ (M + 1) hi hy)
  rw [← TriadicCube.mem_toIntegerCube_vertices]
  exact shrinkCube_vertices_subset_self _ _ h1

/-- **The slopes on the tiles.** -/
theorem sum_sq_cubeSlope_tiles_le (Q : IntegerCube d) (uh : Vertex d → ℝ) {z : Vertex d}
    {M N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z (M * N)).vertices ⊆ (shrinkCube Q 1).vertices) :
    ∑ i ∈ (cornerCube 0 M).vertices, ∑ j, cubeSlope N uh (z + (N : ℤ) • i) j ^ 2 ≤
      (∑ y ∈ Q.vertices, ∑ j : Fin d,
        (if y + unit j ∈ Q.vertices then (uh (y + unit j) - uh y) ^ 2 else 0)) / (N : ℝ) ^ d := by
  have hV : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have h1 : ∀ i, ∑ j, cubeSlope N uh (z + (N : ℤ) • i) j ^ 2 ≤
      ∑ j : Fin d, (∑ y ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (uh (y + unit j) - uh y) ^ 2) / (N : ℝ) ^ d :=
    fun i => Finset.sum_le_sum fun j _ => sq_cubeSlope_le N uh _ j
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ hV.le
  have hblock : ∀ j : Fin d, ∑ i ∈ (cornerCube 0 M).vertices,
      ∑ y ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, (uh (y + unit j) - uh y) ^ 2 =
      ∑ y ∈ (cornerCube z (M * N)).vertices, (uh (y + unit j) - uh y) ^ 2 := fun j =>
    (sum_cornerCube_mul hN z M _).symm
  simp only [hblock]
  have hB : (cornerCube z (M * N)).vertices ⊆ Q.vertices :=
    hsub.trans (shrinkCube_vertices_subset_self Q 1)
  calc ∑ j : Fin d, ∑ y ∈ (cornerCube z (M * N)).vertices, (uh (y + unit j) - uh y) ^ 2
      = ∑ y ∈ (cornerCube z (M * N)).vertices, ∑ j : Fin d, (uh (y + unit j) - uh y) ^ 2 :=
        Finset.sum_comm
    _ = ∑ y ∈ (cornerCube z (M * N)).vertices, ∑ j : Fin d,
          (if y + unit j ∈ Q.vertices then (uh (y + unit j) - uh y) ^ 2 else 0) :=
        Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun j _ =>
          (if_pos (add_unit_mem_of_mem_shrinkCube Q le_rfl (hsub hy) j).2).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hB fun _ _ _ =>
        Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- Shrinking a cube more gives a smaller cube. -/
theorem shrinkCube_vertices_mono (Q : IntegerCube d) {s t : ℕ} (hst : s ≤ t) :
    (shrinkCube Q t).vertices ⊆ (shrinkCube Q s).vertices := by
  intro x hx
  rw [mem_shrinkCube_iff] at hx ⊢
  intro i
  have h := hx i
  constructor <;> omega

/-- The parent of a triadic cube of `□_m` of smaller scale lies in `□_m`. -/
theorem TriadicCube.parent_vertices_subset {T U : TriadicCube d} (hTU : T.vertices ⊆ U.vertices)
    (hs : T.scale + 1 ≤ U.scale) : T.parent.vertices ⊆ U.vertices :=
  TriadicCube.vertices_subset_of_mem_of_scale_le (T.vertices_subset_parent T.center_mem)
    (hTU T.center_mem) hs

end Rigidity.Dirichlet
