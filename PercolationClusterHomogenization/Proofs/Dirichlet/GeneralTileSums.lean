import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralErrorTerms

/-!
# Sums over the tiles of a block in every dimension

For a block of `M^d` tiles of side `K = 3^k` inside `shrinkCube □_m (r + 3)`, with all partition
cubes of `□_m` of scale at most `k₀ ≤ k`:

* if `|ν(T, ξ) − σ|ξ|²/2| ≤ ε |ξ|²` on the tiles, the errors of the tiles satisfy
  `Σ_i δ_i ≤ (ε + d (3^{k₀+1} + 1)/K) K^{-d} Σ_{edges in □_m} |∇u_h|²` (`cube_sum_tileError_le`);
* the `L²` distances of the patch to the affine approximations satisfy
  `Σ_i Σ_{tile} (ṽ − ℓ_i)² ≤ 4 P_T Σ_{edges in □_m} |∇u_h|²`, with `P_T` the Poincaré constant of
  the tiles (`sum_sq_cubeTilePatch_tiles_le`).

These are the forms in every dimension of `sum_tileError_le` and `sum_sq_tilePatch_tiles_le`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- **The errors of the tiles.** -/
theorem cube_sum_tileError_le (hd : 0 < d) (hP : PartitionEvent ω) {m k k₀ : ℕ}
    (hk₀k : k₀ ≤ k) (hU : PartitionResolved ω ⟨m, 0⟩)
    (hk₀ : ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k₀)
    {σ ε : ℝ} (hε0 : 0 ≤ ε)
    (hconv : ∀ T : TriadicCube d, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices →
      ∀ ξ : Fin d → ℝ, |cubeNu ω T ξ - σ * (∑ j, ξ j ^ 2) / 2| ≤ ε * ∑ j, ξ j ^ 2)
    {z₀ : Vertex d} (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (uh : Vertex d → ℝ)
    {M r : ℕ}
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (r + 3)).vertices) :
    ∑ i ∈ (cornerCube 0 M).vertices, cubeTileError ω m k z₀ σ uh i ≤
      (ε + d * (3 ^ (k₀ + 1) + 1) / ((3 ^ k : ℕ) : ℝ)) *
        ((∑ y ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, ∑ j : Fin d,
          (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
            (uh (y + unit j) - uh y) ^ 2 else 0)) / ((3 ^ k : ℕ) : ℝ) ^ d) := by
  set Q := (⟨m, 0⟩ : TriadicCube d).toIntegerCube
  have hK : (0 : ℝ) < ((3 ^ k : ℕ) : ℝ) := by positivity
  have hpt : ∀ i ∈ (cornerCube 0 M).vertices, cubeTileError ω m k z₀ σ uh i ≤
      (ε + d * (3 ^ (k₀ + 1) + 1) / ((3 ^ k : ℕ) : ℝ)) *
        ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 := by
    intro i hi
    have hTU := gridTile_vertices_subset_of_block hz₀ hsub (mem_cornerCube_succ hi)
    have hTres : PartitionResolved ω (gridTile k z₀ i) := fun y hy => (hk₀ y (hTU hy)).trans hk₀k
    have hX := card_sdiff_crossingClusterVertices_le (T := gridTile k z₀ i) hd hP hU hTres hk₀
    have hν := hconv _ rfl hTU (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)
    unfold cubeTileError
    set P2 := ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2
    have hP2 : 0 ≤ P2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    set X := (((crossingClusterVertices ω ⟨m, 0⟩).filter
      (fun x => x ∈ (gridTile k z₀ i).vertices) \
      crossingClusterVertices ω (gridTile k z₀ i)).card : ℝ)
    have hscale : (gridTile k z₀ i).scale = k := rfl
    rw [hscale] at hX
    have hKd : ((3 ^ k : ℕ) : ℝ) ^ d = ((3 ^ k : ℕ) : ℝ) ^ (d - 1) * ((3 ^ k : ℕ) : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    have h2 : P2 * X / (2 * ((3 ^ k : ℕ) : ℝ) ^ d) ≤
        d * (3 ^ (k₀ + 1) + 1) / ((3 ^ k : ℕ) : ℝ) * P2 := by
      rw [div_le_iff₀ (by positivity)]
      have : P2 * X ≤ P2 * (2 * d * ((3 ^ (k₀ + 1) + 1 : ℕ) : ℝ) * ((3 ^ k : ℕ) : ℝ) ^ (d - 1)) :=
        mul_le_mul_of_nonneg_left hX hP2
      have e : d * (3 ^ (k₀ + 1) + 1) / ((3 ^ k : ℕ) : ℝ) * P2 * (2 * ((3 ^ k : ℕ) : ℝ) ^ d) =
          P2 * (2 * d * ((3 ^ (k₀ + 1) + 1 : ℕ) : ℝ) * ((3 ^ k : ℕ) : ℝ) ^ (d - 1)) := by
        rw [hKd]
        push_cast
        field_simp
      linarith
    linarith
  have hslope := sum_sq_cubeSlope_tiles_le Q uh (z := z₀) (M := M) (N := 3 ^ k) (by positivity)
    (fun x hx => shrinkCube_vertices_mono Q (show 1 ≤ r + 3 by omega)
      (hsub (cornerCube_mul_subset_succ z₀ M (3 ^ k) hx)))
  calc _ ≤ ∑ i ∈ (cornerCube 0 M).vertices, (ε + d * (3 ^ (k₀ + 1) + 1) / ((3 ^ k : ℕ) : ℝ)) *
        ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 := Finset.sum_le_sum hpt
    _ = _ := by rw [← Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact_mod_cast hslope
        · positivity

/-- **The `L²` distances of the patch to the affine approximations on the tiles.** -/
theorem sum_sq_cubeTilePatch_tiles_le (hd : 0 < d) {K₀ : ℝ} (hK₀0 : 0 ≤ K₀)
    (hK₀ : ∀ (ω : Configuration d), PartitionEvent ω → ∀ (U : TriadicCube d)
      (k : ℕ), k ≤ U.scale →
      (∀ x ∈ U.parent.vertices, (partitionCube ω x).scale ≤ k) →
      ∀ f : Vertex d → ℝ,
      (∀ x, ¬(x ∈ crossingClusterVertices ω U ∧ U.IsLatticeInterior x) → f x = 0) →
      ∑ x ∈ crossingClusterVertices ω U, f x ^ 2 ≤
        (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k)) * K₀ * ((3 : ℝ) ^ k) ^ (2 * d) *
          ((3 : ℝ) ^ (U.scale + 1)) ^ 2 *
          ∑ z ∈ crossingClusterVertices ω U, ∑ j : Fin d,
            (if z + unit j ∈ crossingClusterVertices ω U ∧ (openGraph ω).Adj z (z + unit j) then
              (f (z + unit j) - f z) ^ 2 else 0))
    (hP : PartitionEvent ω) {m k k₀ : ℕ} (hk₀k : k₀ ≤ k) (hkm : k + 1 ≤ m)
    (hk₀ : ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k₀)
    {z₀ : Vertex d} (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (uh : Vertex d → ℝ)
    {M r : ℕ}
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (r + 3)).vertices) :
    ∑ i ∈ (cornerCube 0 M).vertices,
        ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
          (cubeTilePatch ω k z₀ uh x -
            cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 ≤
      (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
          ((3 : ℝ) ^ (k + 1)) ^ 2 *
        (4 * ∑ y ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, ∑ j : Fin d,
          (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
            (uh (y + unit j) - uh y) ^ 2 else 0)) := by
  set Q := (⟨m, 0⟩ : TriadicCube d).toIntegerCube
  set PT := (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
    ((3 : ℝ) ^ (k + 1)) ^ 2
  have h3d : (1 : ℝ) < 3 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have hPT : 0 ≤ PT := by
    have : (0 : ℝ) ≤ 3 ^ d / (3 ^ d - 1) := div_nonneg (by positivity) (by linarith)
    positivity
  have hpt : ∀ i ∈ (cornerCube 0 M).vertices,
      ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
        (cubeTilePatch ω k z₀ uh x - cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 ≤
      PT * (4 * ((3 : ℝ) ^ k) ^ d *
        ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) := by
    intro i hi
    have hTU := gridTile_vertices_subset_of_block hz₀ hsub (mem_cornerCube_succ hi)
    have hpar := TriadicCube.parent_vertices_subset hTU (by change k + 1 ≤ m; exact hkm)
    exact sum_sq_cubeTilePatch_sub_le hd hK₀0 hK₀ hP hz₀ uh hk₀k fun x hx => hk₀ x (hpar hx)
  have hslope := sum_sq_cubeSlope_tiles_le Q uh (z := z₀) (M := M) (N := 3 ^ k) (by positivity)
    (fun x hx => shrinkCube_vertices_mono Q (show 1 ≤ r + 3 by omega)
      (hsub (cornerCube_mul_subset_succ z₀ M (3 ^ k) hx)))
  have hKd : ((3 ^ k : ℕ) : ℝ) ^ d = ((3 : ℝ) ^ k) ^ d := by push_cast; rfl
  rw [hKd] at hslope
  calc _ ≤ ∑ i ∈ (cornerCube 0 M).vertices,
        PT * (4 * ((3 : ℝ) ^ k) ^ d *
          ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) :=
        Finset.sum_le_sum hpt
    _ = PT * (4 * ((3 : ℝ) ^ k) ^ d * ∑ i ∈ (cornerCube 0 M).vertices,
          ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ PT * (4 * ((3 : ℝ) ^ k) ^ d * ((∑ y ∈ Q.vertices, ∑ j : Fin d,
          (if y + unit j ∈ Q.vertices then (uh (y + unit j) - uh y) ^ 2 else 0)) /
            ((3 : ℝ) ^ k) ^ d)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hPT
        exact_mod_cast hslope
    _ = _ := by
        congr 1
        field_simp

end Rigidity.Dirichlet
