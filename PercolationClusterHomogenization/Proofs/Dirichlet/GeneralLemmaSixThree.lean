import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralTilePatch
import PercolationClusterHomogenization.Proofs.Dirichlet.TileFaces

/-!
# Lemma 6.3 of Armstrong and Dario in every dimension

Let `□_m` be a triadic cube of `ℤᵈ` resolved by the partition into good cubes, with all partition
cubes of its vertices of scale at most `k`. Tile a block of `□_m` by the triadic cubes of scale `k`
and let `ṽ` be the patch of the maximizers of `ν` on the tiles along the affine approximations of
the homogenized solution `u_h` (`cubeTilePatch`). Then the hypotheses of the lattice Lemma 6.3
(`innerEdgeEnergy_patch_dirichletSolution_div_le`) hold for the cluster conductance of `□_m`:
the energy of `ṽ` on a tile is at most `σ |p|² + 2 δ`, with
`δ = |ν(T, p) − σ|p|²/2| + |p|² |(C_*(□_m) ∩ T) \ C_*(T)| / (2 |T|)`
(`innerEdgeEnergy_cubeTilePatch_div_le`), and `ṽ` is affine on the faces of the tiles
(`cubeTilePatch_eq_of_not_isLatticeInterior`). This gives the energy estimate (ii) of Lemma 6.3 of
the source on the edges inside `□_m` (`cube_lemmaSixThree`), in every dimension; the planar form is
`planar_lemmaSixThree`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- A vertex of the upper face of a tile has a lattice neighbour outside it. -/
theorem not_isLatticeInterior_of_mem_upperFace {k : ℕ} {z₀ : Vertex d}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {i x : Vertex d} {j : Fin d}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).upperFace j) :
    ¬ (gridTile k z₀ i).IsLatticeInterior x := by
  intro hint
  have h1 := (TriadicCube.add_sub_unit_mem_of_isLatticeInterior hint j).1
  rw [← TriadicCube.mem_toIntegerCube_vertices, gridTile_toIntegerCube hz₀] at h1
  obtain ⟨-, hface⟩ := (IntegerCube.mem_upperFace _ j x).1 hx
  rw [IntegerCube.mem_vertices] at h1
  have h2 := (h1 j).2
  simp only [Pi.add_apply, unit, Pi.single_eq_same, cornerCube] at h2 hface
  omega

/-- The step across the upper face of a tile lands on a vertex of the next tile with a lattice
neighbour outside it. -/
theorem not_isLatticeInterior_next_tile {k : ℕ} {z₀ : Vertex d}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {i x : Vertex d} {j : Fin d}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).upperFace j) :
    ¬ (gridTile k z₀ (i + unit j)).IsLatticeInterior (x + unit j) := by
  intro hint
  have h1 := (TriadicCube.add_sub_unit_mem_of_isLatticeInterior hint j).2
  rw [add_sub_cancel_right, ← TriadicCube.mem_toIntegerCube_vertices,
    gridTile_toIntegerCube hz₀] at h1
  obtain ⟨hxv, -⟩ := (IntegerCube.mem_upperFace _ j x).1 hx
  rw [IntegerCube.mem_vertices] at h1 hxv
  have h2 := (h1 j).1
  have h3 := (hxv j).2
  simp only [cornerCube, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_eq_same]
    at h2 h3
  nlinarith

/-- The error `δ` of the tile `i` in Lemma 6.3: the convergence error of `ν` on the tile and the
affine energy of the vertices of `C_*(□_m)` in the tile outside the cluster of the tile. -/
noncomputable def cubeTileError (ω : Configuration d) (m k : ℕ) (z₀ : Vertex d) (σ : ℝ)
    (uh : Vertex d → ℝ) (i : Vertex d) : ℝ :=
  |cubeNu ω (gridTile k z₀ i) (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j) -
      σ * (∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) / 2| +
    (∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) *
      (((crossingClusterVertices ω ⟨m, 0⟩).filter (fun x => x ∈ (gridTile k z₀ i).vertices) \
        crossingClusterVertices ω (gridTile k z₀ i)).card : ℝ) / (2 * ((3 ^ k : ℕ) : ℝ) ^ d)

theorem cubeTileError_nonneg (ω : Configuration d) (m k : ℕ) (z₀ : Vertex d) (σ : ℝ)
    (uh : Vertex d → ℝ) (i : Vertex d) : 0 ≤ cubeTileError ω m k z₀ σ uh i := by
  unfold cubeTileError
  have : 0 ≤ ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

/-- The volume of a tile. -/
theorem gridTile_latticeVolume (k : ℕ) (z₀ i : Vertex d) :
    (gridTile k z₀ i).latticeVolume = ((3 ^ k : ℕ) : ℝ) ^ d := by
  change ((3 : ℝ) ^ k) ^ d = ((3 ^ k : ℕ) : ℝ) ^ d
  norm_cast

/-- **The energy of the patch on a tile in the form of the lattice Lemma 6.3.** -/
theorem innerEdgeEnergy_cubeTilePatch_div_le (hd : 0 < d) (hP : PartitionEvent ω) {m k : ℕ}
    {z₀ : Vertex d} (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) {σ : ℝ}
    (uh : Vertex d → ℝ) {i : Vertex d} (hres : PartitionResolved ω (gridTile k z₀ i)) :
    innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k))
        (cubeTilePatch ω k z₀ uh) / ((3 ^ k : ℕ) : ℝ) ^ d ≤
      ∑ j, σ * cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 +
        2 * cubeTileError ω m k z₀ σ uh i := by
  have h := innerEdgeEnergy_cubeTilePatch_le (m := m) hd hP hz₀ uh hres
  rw [gridTile_latticeVolume] at h
  have hK : (0 : ℝ) < ((3 ^ k : ℕ) : ℝ) ^ d := by positivity
  set P2 := ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2
  set ν := cubeNu ω (gridTile k z₀ i)
    (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)
  set X := (((crossingClusterVertices ω ⟨m, 0⟩).filter
    (fun x => x ∈ (gridTile k z₀ i).vertices) \
    crossingClusterVertices ω (gridTile k z₀ i)).card : ℝ)
  have hsum : ∑ j, σ * cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2 = σ * P2 := by
    rw [← Finset.mul_sum]
  rw [hsum]
  unfold cubeTileError
  rw [div_le_iff₀ hK]
  have habs := le_abs_self (ν - σ * P2 / 2)
  have e : 2 * (P2 * X / (2 * ((3 ^ k : ℕ) : ℝ) ^ d)) * ((3 ^ k : ℕ) : ℝ) ^ d = P2 * X := by
    field_simp
  nlinarith

/-- **Armstrong and Dario, Lemma 6.3 (ii)**, in every dimension, before bounding the errors of
the tiles and the `L²` distances to the affine approximations. -/
theorem cube_lemmaSixThree (hd : 0 < d) (hP : PartitionEvent ω) {m k : ℕ}
    (hk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, (partitionCube ω x).scale ≤ k)
    {σ : ℝ} (hσ : 0 < σ) (w : Vertex d → ℝ) {r : ℕ} (hr : 0 < r) {z₀ : Vertex d}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (M : ℕ)
    (hsub : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆
      (shrinkCube (⟨m, 0⟩ : TriadicCube d).toIntegerCube (r + 3)).vertices)
    {D : ℕ} (hT1 : ∀ t, z₀ t ≤ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.corner t + D)
    (hT2 : ∀ t, (⟨m, 0⟩ : TriadicCube d).toIntegerCube.corner t +
      (⟨m, 0⟩ : TriadicCube d).toIntegerCube.size ≤ z₀ t + (M * 3 ^ k : ℕ) + D)
    {ρ : ℕ} (hρ : 0 < ρ) {γ p : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (hp : 2 < p)
    (hγp : γ * (p / (p - 2)) < 1) :
    innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
        (patch (cubeCutoff (cornerCube z₀ (M * 3 ^ k)) ρ)
          (cubeTilePatch ω k z₀ (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w))
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w)) /
        (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d ≤
      innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube d).toIntegerCube
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) /
          (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d +
        (6 * ((3 ^ k : ℕ) : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices,
            cubeTileError ω m k z₀ σ (dirichletSolution (constCond fun _ => σ)
              (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) i +
          3 * (max σ 1 * ((d : ℝ) * (3 * ((1 + (d : ℝ)) * 2 ^ d * ((3 ^ k : ℕ) : ℝ) ^ 3 *
            (10 * (d : ℝ) * max σ 1 / (σ * (r : ℝ) ^ 2)) + 1 / ((3 ^ k : ℕ) : ℝ)) *
              ∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, ∑ j : Fin d,
                (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
                  (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w (x + unit j) -
                  dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w x) ^ 2 else 0)))) +
          6 * max σ 1 * ((d : ℝ) * (1 / (ρ : ℝ)) ^ 2) *
            (∑ i ∈ (cornerCube 0 M).vertices,
                ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
                (cubeTilePatch ω k z₀ (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w) x -
                  cubeAffine (3 ^ k) (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w)
                    (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 +
              ∑ i ∈ (cornerCube 0 M).vertices,
                ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
                (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w x -
                  cubeAffine (3 ^ k) (dirichletSolution (constCond fun _ => σ)
                    (cubeInterior (⟨m, 0⟩ : TriadicCube d).toIntegerCube) w)
                    (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2)) /
          (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d +
        (2 + 3 * max σ 1 / σ) *
          (2 * ((∑ x ∈ cubeLayer (⟨m, 0⟩ : TriadicCube d).toIntegerCube (D + ρ + 3 ^ k + 1),
              ∑ j : Fin d, (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
                σ * (w (x + unit j) - w x) ^ 2 else 0)) /
                (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d) +
            88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
              ((2 * (d : ℝ)) ^ (p / (p - 2)) / (1 - γ * (p / (p - 2)))) ^ (1 - 2 / p) *
              ((((D + ρ + 3 ^ k : ℕ) : ℝ) + 1) /
                (⟨m, 0⟩ : TriadicCube d).toIntegerCube.size) ^ γ *
              ((∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, √(∑ j : Fin d,
                  (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
                    (w (x + unit j) - w x) ^ 2 else 0)) ^ p) /
                (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ d) ^ (2 / p)) := by
  set Q := (⟨m, 0⟩ : TriadicCube d).toIntegerCube
  set uh := dirichletSolution (constCond fun _ => σ) (cubeInterior Q) w
  have hL : 0 < Q.size := by change 0 < 3 ^ m; positivity
  have hK : 0 < 3 ^ k := by positivity
  have hres : ∀ i ∈ (cornerCube 0 (M + 1)).vertices, PartitionResolved ω (gridTile k z₀ i) :=
    fun i hi y hy => hk y (gridTile_vertices_subset_of_block hz₀ hsub hi hy)
  have hsub' : (cornerCube z₀ ((M + 1) * 3 ^ k)).vertices ⊆ (shrinkCube Q (r + 3)).vertices :=
    hsub
  refine innerEdgeEnergy_patch_dirichletSolution_div_le (d := d) hd (fun _ => σ)
    (lam := σ) (Λ := max σ 1) hσ (fun _ => ⟨le_rfl, le_max_left _ _⟩) (cubeCond ω ⟨m, 0⟩)
    (fun e => cubeCond_nonneg _ e) (fun e => (cubeCond_le_one _ e).trans (le_max_right _ _))
    Q hL w hr z₀ M hK hsub' hT1 hT2 hρ (cubeTilePatch ω k z₀ uh) (cubeTileError ω m k z₀ σ uh)
    (fun i => cubeTileError_nonneg ω m k z₀ σ uh i) (fun i hi => ?_) (fun i hi j x hx _ => ?_)
    hγ0 hγ hp hγp
  · exact innerEdgeEnergy_cubeTilePatch_div_le hd hP hz₀ uh (hres i (mem_cornerCube_succ hi))
  · have hi1 := mem_cornerCube_succ hi
    have hxT : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices :=
      ((IntegerCube.mem_upperFace _ j x).1 hx).1
    have hnext : i + unit j ∈ (cornerCube 0 (M + 1)).vertices := by
      rw [IntegerCube.mem_vertices] at hi ⊢
      intro t
      have h := hi t
      simp only [cornerCube, Pi.zero_apply, zero_add, Pi.add_apply, unit, Pi.single_apply] at h ⊢
      split_ifs <;> constructor <;> push_cast <;> omega
    refine ⟨cubeTilePatch_eq_of_not_isLatticeInterior hd hP uh hxT (hres i hi1)
      (not_isLatticeInterior_of_mem_upperFace hz₀ hx), ?_⟩
    have h2 := cubeTilePatch_eq_of_not_isLatticeInterior hd hP uh (add_unit_mem_next_tile hx)
      (hres _ hnext) (not_isLatticeInterior_next_tile hz₀ hx)
    rw [h2, smul_add, add_assoc]

end Rigidity.Dirichlet
