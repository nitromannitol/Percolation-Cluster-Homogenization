import PercolationClusterHomogenization.Proofs.Dirichlet.GridTiles
import PercolationClusterHomogenization.Proofs.Dirichlet.LemmaSixThreeCoarse

/-!
# The faces of the tiles of a block

The step `x ↦ x + e_j` across the upper face `j` of a tile of the triadic grid lands in the next
tile in the direction `j` (`add_unit_mem_next_tile`), and the tiles of a block inside
`shrinkCube □_m (r + 3)` are triadic cubes inside `□_m` (`gridTile_vertices_subset_of_block`).
These are the face and block conditions of the proof of Lemma 6.3 of Armstrong and Dario, in every
dimension.
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

end Rigidity.Dirichlet
