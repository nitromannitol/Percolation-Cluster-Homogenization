import PercolationClusterHomogenization.Proofs.Dirichlet.LemmaSixTwoInner
import PercolationClusterHomogenization.Proofs.Dirichlet.CutoffRegions
import PercolationClusterHomogenization.Proofs.Dirichlet.SubcubeMuTest

/-!
# The triadic grid and the tiles of a translate of a mesoscopic cube

For a scale `k` and a vertex `x` of `ℤᵈ`, `triadicGridCorner k x` is the first point of the triadic
grid of scale `k` (the corners of the triadic cubes of scale `k`) at or after `x` in each
coordinate, and `gridTile k z i` the triadic cube of scale `k` with corner `z + 3^k i`. For a
translate `x + □` of side `3^n ≥ 3^k` away from the boundary of `□_m`, the `(3^{n−k} − 1)^d` tiles
after the grid corner lie in the translate and in the interior of `□_m`
(`gridTile_vertices_subset`). Every vertex lies in exactly one tile of a grid (`tileIdx`), and the
affine approximation `cubeAffine` of a function on a tile has constant increments. These are the tiles of the `μ` test in the proof of Lemma 6.2 of
Armstrong and Dario, and of the patch of the maximizers of `ν` in the proof of Lemma 6.3.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The first point of the triadic grid of scale `k` (the corners of the triadic cubes of scale
`k`) at or after `x` in each coordinate. -/
def triadicGridCorner (k : ℕ) (x : Vertex d) : Vertex d :=
  fun t => x t + ((-((3 : ℤ) ^ k / 2) - x t) % 3 ^ k)

theorem triadicGridCorner_spec (k : ℕ) (x : Vertex d) (t : Fin d) :
    x t ≤ triadicGridCorner k x t ∧ triadicGridCorner k x t < x t + 3 ^ k ∧
      (3 : ℤ) ^ k ∣ triadicGridCorner k x t + (3 : ℤ) ^ k / 2 := by
  have hK : (0 : ℤ) < 3 ^ k := by positivity
  have h0 := Int.emod_nonneg (-((3 : ℤ) ^ k / 2) - x t) hK.ne'
  have h1 := Int.emod_lt_of_pos (-((3 : ℤ) ^ k / 2) - x t) hK
  refine ⟨by simp only [triadicGridCorner]; linarith, by simp only [triadicGridCorner]; linarith,
    ?_⟩
  simp only [triadicGridCorner]
  rw [Int.emod_def]
  exact ⟨-((-((3 : ℤ) ^ k / 2) - x t) / 3 ^ k), by ring⟩

/-- The triadic tile of scale `k` with corner `z + 3^k i`, for `z` on the triadic grid. -/
def gridTile (k : ℕ) (z i : Vertex d) : TriadicCube d :=
  ⟨k, fun t => (z t + (3 : ℤ) ^ k / 2) / 3 ^ k + i t⟩

theorem gridTile_toIntegerCube {k : ℕ} {z : Vertex d}
    (hz : ∀ t, (3 : ℤ) ^ k ∣ z t + (3 : ℤ) ^ k / 2) (i : Vertex d) :
    (gridTile k z i).toIntegerCube = cornerCube (z + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k) := by
  unfold gridTile TriadicCube.toIntegerCube cornerCube
  simp only [TriadicCube.side, IntegerCube.mk.injEq, and_true]
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [mul_add, Int.mul_ediv_cancel' (hz t)]
  ring

/-- A translate away from the boundary lies in the interior of the cube. -/
theorem mem_cubeInterior_of_mem_cornerCube_of_mem_trim (Q : IntegerCube d) {N r : ℕ}
    {x y : Vertex d} (hx : x ∈ (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1))
    (hy : y ∈ (cornerCube x N).vertices) : y ∈ cubeInterior Q := by
  obtain ⟨hxT, hxL⟩ := Finset.mem_sdiff.mp hx
  have hnot : ∀ i, ¬(x i < (trimCube Q N).corner i + ((r + 1 : ℕ) : ℤ) ∨
      (trimCube Q N).corner i + ((trimCube Q N).size : ℤ) ≤ x i + ((r + 1 : ℕ) : ℤ)) :=
    fun i h => hxL (Finset.mem_filter.mpr ⟨hxT, i, h⟩)
  rw [IntegerCube.mem_vertices] at hxT hy
  simp only [trimCube, cornerCube] at hxT hy hnot
  refine Finset.mem_filter.2 ⟨?_, fun i => ?_⟩
  · rw [IntegerCube.mem_vertices]
    intro i
    have h1 := hxT i
    have h2 := hy i
    have h3 := hnot i
    push Not at h3
    constructor <;> omega
  · have h1 := hxT i
    have h2 := hy i
    have h3 := hnot i
    push Not at h3
    constructor <;> omega

/-- The block of tiles after the grid corner lies in the translate. -/
theorem block_subset_cornerCube {K M N : ℕ} (hMK : (M + 1) * K ≤ N) {x z : Vertex d}
    (hz : ∀ t, x t ≤ z t ∧ z t < x t + K) :
    (cornerCube z (M * K)).vertices ⊆ (cornerCube x N).vertices := by
  intro y hy
  rw [IntegerCube.mem_vertices] at hy ⊢
  intro t
  have h1 := hy t
  have h2 := hz t
  simp only [cornerCube] at h1 ⊢
  have h3 : ((M * K : ℕ) : ℤ) + K ≤ (N : ℤ) := by
    have : (((M + 1) * K : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hMK
    push_cast at this ⊢
    linarith
  constructor <;> omega

/-- The vertices of the tiles of a translate away from the boundary. -/
theorem gridTile_vertices_subset {m n k r : ℕ} (hkn : k ≤ n) {x i : Vertex d}
    (hx : x ∈ (trimCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (3 ^ n)).vertices \
      cubeLayer (trimCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (3 ^ n)) (r + 1))
    (hi : i ∈ (cornerCube 0 (3 ^ (n - k) - 1)).vertices) :
    (gridTile k (triadicGridCorner k x) i).vertices ⊆ (cornerCube x (3 ^ n)).vertices ∧
      ∀ y ∈ (gridTile k (triadicGridCorner k x) i).vertices,
        y ∈ cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube := by
  have hMK : (3 ^ (n - k) - 1 + 1) * 3 ^ k ≤ 3 ^ n := by
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), ← pow_add, Nat.sub_add_cancel hkn]
  have hz : ∀ t, x t ≤ triadicGridCorner k x t ∧
      triadicGridCorner k x t < x t + ((3 ^ k : ℕ) : ℤ) := fun t => by
    have := triadicGridCorner_spec k x t
    push_cast
    exact ⟨this.1, this.2.1⟩
  have hsub : (gridTile k (triadicGridCorner k x) i).vertices ⊆ (cornerCube x (3 ^ n)).vertices := by
    intro y hy
    rw [← TriadicCube.mem_toIntegerCube_vertices,
      gridTile_toIntegerCube (fun t => (triadicGridCorner_spec k x t).2.2)] at hy
    exact block_subset_cornerCube hMK hz (tile_subset _ _ hi hy)
  exact ⟨hsub, fun y hy => mem_cubeInterior_of_mem_cornerCube_of_mem_trim _ hx (hsub hy)⟩

/-- The index of the tile containing `x`. -/
def tileIdx (K : ℕ) (z₀ x : Vertex d) : Vertex d := fun t => (x t - z₀ t) / K

theorem mem_tile_tileIdx {K : ℕ} (hK : 0 < K) (z₀ x : Vertex d) :
    x ∈ (cornerCube (z₀ + (K : ℤ) • tileIdx K z₀ x) K).vertices := by
  rw [IntegerCube.mem_vertices]
  intro t
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have h1 := Int.mul_ediv_add_emod (x t - z₀ t) K
  have h2 := Int.emod_nonneg (x t - z₀ t) hK'.ne'
  have h3 := Int.emod_lt_of_pos (x t - z₀ t) hK'
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tileIdx]
  constructor <;> linarith

theorem tileIdx_eq_of_mem {K : ℕ} (hK : 0 < K) (z₀ : Vertex d) {i x : Vertex d}
    (hx : x ∈ (cornerCube (z₀ + (K : ℤ) • i) K).vertices) : tileIdx K z₀ x = i := by
  rw [IntegerCube.mem_vertices] at hx
  funext t
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have h := hx t
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [tileIdx]
  exact ((Int.ediv_emod_unique (a := x t - z₀ t) (r := x t - z₀ t - K * i t) (q := i t)
    hK').2 ⟨by ring, by linarith [h.1], by linarith [h.2]⟩).1

/-- The affine approximation is affine with the slope of the cube. -/
theorem cubeAffine_eq_add (N : ℕ) (g : Vertex d → ℝ) (y x : Vertex d) :
    cubeAffine N g y x = cubeAffine N g y y + ∑ j, cubeSlope N g y j * ((x j - y j : ℤ) : ℝ) := by
  simp only [cubeAffine, sub_self, Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]

theorem cubeAffine_add_unit_sub_two (N : ℕ) (g : Vertex d → ℝ) (y x : Vertex d) (j : Fin d) :
    cubeAffine N g y (x + unit j) - cubeAffine N g y x = cubeSlope N g y j := by
  rw [cubeAffine_eq_add N g y (x + unit j), cubeAffine_eq_add N g y x]
  have h : ∀ i : Fin d, ((((x + unit j) i - y i : ℤ) : ℝ)) =
      (((x i - y i : ℤ) : ℝ)) + if i = j then 1 else 0 := by
    intro i
    simp only [Pi.add_apply, unit, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Rigidity.Dirichlet
