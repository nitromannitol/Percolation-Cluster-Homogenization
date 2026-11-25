import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralLemmaSixTwo
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuDirichlet

/-!
# The maximizers of `ν` on the tiles of `ℤᵈ`, patched along the affine approximations

Fix a point `z₀` of the triadic grid of scale `k` and `K = 3^k`. Every vertex `x` lies in exactly
one tile `T(x) = z₀ + K i + □_K` (`tileIdx`). For a function `u_h` (the homogenized solution), the
tile `i` carries the slope `p_i` and the affine approximation `ℓ_i` of `u_h` on it
(`cubeSlope`, `cubeAffine`). The patched function `ṽ` is, at `x ∈ C_*(T(x))`, the maximizer of
`ν(T(x), p_i)` shifted so that it equals `ℓ_i` at the vertices of `C_*(T(x))` with a lattice
neighbour outside `T(x)` (Armstrong and Dario, Lemma 4.3 and (4.9),
`exists_cubeNu_maximizer_affine`), and `ℓ_i(x)` elsewhere, as in the proof of Lemma 6.3 of the
source. Then

* `ṽ = ℓ_i` at the vertices of the tile `i` with a lattice neighbour outside it, in particular on
  the faces of the tiles (`cubeTilePatch_eq_of_not_isLatticeInterior`), which is the face condition
  of the lattice Lemma 6.3;
* the energy of `ṽ` on the open edges of `C_*(□_m)` inside a resolved tile is at most
  `2 |T| ν(T, p_i) + |p_i|² |(C_*(□_m) ∩ T) \ C_*(T)|` (`innerEdgeEnergy_cubeTilePatch_le`);
* `ṽ − ℓ_i` is small in `L²` on a tile, by the Poincaré inequality on the cluster of the tile
  (`sum_sq_cubeTilePatch_sub_le`).

This is the general-dimensional form of `PlanarTilePatch.lean`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- The maximizer of `ν(T, p)`, with the constant of its affine boundary values, on the partition
event for a resolved cube (and `0` otherwise). -/
noncomputable def cubeNuMax (ω : Configuration d) (T : TriadicCube d) (p : Fin d → ℝ) :
    CubeFun ω T × ℝ :=
  if h : 0 < d ∧ PartitionEvent ω ∧ PartitionResolved ω T then
    (Classical.choose (exists_cubeNu_maximizer_affine h.1 h.2.1 h.2.2 p),
      Classical.choose
        (Classical.choose_spec (exists_cubeNu_maximizer_affine h.1 h.2.1 h.2.2 p)).2.2.2)
  else (0, 0)

theorem cubeNuMax_spec (hd : 0 < d) (hP : PartitionEvent ω) {T : TriadicCube d}
    (hT : PartitionResolved ω T) (p : Fin d → ℝ) :
    (cubeNuMax ω T p).1 ∈ cubeHarmonic ω T ∧
      cubeNu ω T p = cubeForm ω T (cubeNuMax ω T p).1 (cubeNuMax ω T p).1 / 2 / T.latticeVolume ∧
      ∀ x : ↥(crossingClusterVertices ω T), ¬ T.IsLatticeInterior x.1 →
        (cubeNuMax ω T p).1 x = ∑ i, p i * (x.1 i : ℝ) + (cubeNuMax ω T p).2 := by
  have h : 0 < d ∧ PartitionEvent ω ∧ PartitionResolved ω T := ⟨hd, hP, hT⟩
  unfold cubeNuMax
  rw [dif_pos h]
  obtain ⟨hv, -, hν, hc⟩ :=
    Classical.choose_spec (exists_cubeNu_maximizer_affine h.1 h.2.1 h.2.2 p)
  exact ⟨hv, hν, Classical.choose_spec hc⟩

/-- The patch of the maximizers of `ν` on the tiles along the affine approximations of `uh`. -/
noncomputable def cubeTilePatch (ω : Configuration d) (k : ℕ) (z₀ : Vertex d)
    (uh : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  if hx : x ∈ crossingClusterVertices ω (gridTile k z₀ (tileIdx (3 ^ k) z₀ x)) then
    (cubeNuMax ω (gridTile k z₀ (tileIdx (3 ^ k) z₀ x))
        (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j)).1
        ⟨x, hx⟩ -
      (cubeNuMax ω (gridTile k z₀ (tileIdx (3 ^ k) z₀ x))
        (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j)).2 -
      ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j *
        ((z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j : ℝ) +
      cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x)
        (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x)
  else cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) x

/-- **The patch is the affine approximation at the vertices of a tile with a lattice neighbour
outside it.** -/
theorem cubeTilePatch_eq_of_not_isLatticeInterior (hd : 0 < d) (hP : PartitionEvent ω) {k : ℕ}
    {z₀ : Vertex d} (uh : Vertex d → ℝ) {i x : Vertex d}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices)
    (hres : PartitionResolved ω (gridTile k z₀ i))
    (hint : ¬ (gridTile k z₀ i).IsLatticeInterior x) :
    cubeTilePatch ω k z₀ uh x = cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x := by
  have hidx : tileIdx (3 ^ k) z₀ x = i := tileIdx_eq_of_mem (by positivity) z₀ hx
  subst hidx
  unfold cubeTilePatch
  split_ifs with hxC
  · obtain ⟨-, -, hbd⟩ := cubeNuMax_spec hd hP hres
      (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • tileIdx (3 ^ k) z₀ x) j)
    rw [hbd ⟨x, hxC⟩ hint, cubeAffine_eq_add (3 ^ k) uh _ x]
    simp only [Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
    ring
  · rfl

/-- On the cluster of its tile, the patch is the maximizer up to a constant. -/
theorem cubeTilePatch_eq_of_mem (ω : Configuration d) {k : ℕ} {z₀ : Vertex d}
    (uh : Vertex d → ℝ) {i x : Vertex d}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices)
    (hxC : x ∈ crossingClusterVertices ω (gridTile k z₀ i)) :
    cubeTilePatch ω k z₀ uh x =
      cubeExtend ω (gridTile k z₀ i)
          (cubeNuMax ω (gridTile k z₀ i) (fun j => cubeSlope (3 ^ k) uh
            (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)).1 x -
        (cubeNuMax ω (gridTile k z₀ i)
          (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j)).2 -
        ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j *
          ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) +
        cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (z₀ + ((3 ^ k : ℕ) : ℤ) • i) := by
  have hidx : tileIdx (3 ^ k) z₀ x = i := tileIdx_eq_of_mem (by positivity) z₀ hx
  subst hidx
  unfold cubeTilePatch
  rw [dif_pos hxC, cubeExtend_apply_of_mem _ hxC]

/-- Off the cluster of its tile, the patch is the affine approximation. -/
theorem cubeTilePatch_eq_of_not_mem (ω : Configuration d) {k : ℕ} {z₀ : Vertex d}
    (uh : Vertex d → ℝ) {i x : Vertex d}
    (hx : x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices)
    (hxC : x ∉ crossingClusterVertices ω (gridTile k z₀ i)) :
    cubeTilePatch ω k z₀ uh x = cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x := by
  have hidx : tileIdx (3 ^ k) z₀ x = i := tileIdx_eq_of_mem (by positivity) z₀ hx
  subst hidx
  unfold cubeTilePatch
  rw [dif_neg hxC]

/-- **The energy of the patch on a resolved tile.** -/
theorem innerEdgeEnergy_cubeTilePatch_le (hd : 0 < d) (hP : PartitionEvent ω) {m k : ℕ}
    {z₀ : Vertex d} (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2)
    (uh : Vertex d → ℝ) {i : Vertex d} (hres : PartitionResolved ω (gridTile k z₀ i)) :
    innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k))
        (cubeTilePatch ω k z₀ uh) ≤
      2 * (gridTile k z₀ i).latticeVolume * cubeNu ω (gridTile k z₀ i)
          (fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j) +
        (∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) *
          (((crossingClusterVertices ω ⟨m, 0⟩).filter
              (fun x => x ∈ (gridTile k z₀ i).vertices) \
            crossingClusterVertices ω (gridTile k z₀ i)).card : ℝ) := by
  set T := gridTile k z₀ i
  set Tc := cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)
  have hTc : T.toIntegerCube = Tc := gridTile_toIntegerCube hz₀ i
  have hmemT : ∀ y, y ∈ Tc.vertices ↔ y ∈ T.vertices := fun y => by
    rw [← hTc, TriadicCube.mem_toIntegerCube_vertices]
  set p : Fin d → ℝ := fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j
  set vm := (cubeNuMax ω T p).1
  set ext := cubeExtend ω T vm
  set CT := crossingClusterVertices ω T
  set CU := crossingClusterVertices ω ⟨m, 0⟩
  set X := (CU.filter fun x => x ∈ T.vertices) \ CT
  set v := cubeTilePatch ω k z₀ uh
  obtain ⟨-, hν, -⟩ := cubeNuMax_spec hd hP hres p
  have hE : innerEdgeEnergy (cubeCond ω ⟨m, 0⟩) Tc v =
      ∑ x ∈ Tc.vertices, ∑ j : Fin d, (if x + unit j ∈ Tc.vertices then
        cubeCond ω ⟨m, 0⟩ (x, j) * (v (x + unit j) - v x) ^ 2 else 0) := by
    unfold innerEdgeEnergy
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_filter]
  rw [hE]
  have hterm : ∀ x ∈ Tc.vertices, ∑ j : Fin d, (if x + unit j ∈ Tc.vertices then
      cubeCond ω ⟨m, 0⟩ (x, j) * (v (x + unit j) - v x) ^ 2 else 0) ≤
      (if x ∈ CT then ∑ j : Fin d, (if x + unit j ∈ CT ∧ (openGraph ω).Adj x (x + unit j) then
        (ext (x + unit j) - ext x) ^ 2 else 0) else 0) +
      (if x ∈ X then ∑ j, p j ^ 2 else 0) := by
    intro x hx
    by_cases hxC : x ∈ CT
    · rw [if_pos hxC, if_neg (fun h => (Finset.mem_sdiff.1 h).2 hxC), add_zero]
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h1 h2
      · have hc := cubeCond_le_one (ω := ω) ⟨m, 0⟩ (x, j)
        rw [show v (x + unit j) = _ from cubeTilePatch_eq_of_mem ω uh h1 h2.1,
          show v x = _ from cubeTilePatch_eq_of_mem ω uh hx hxC]
        have e : ∀ a b c d : ℝ, (a - c - d + b) - (ext x - c - d + b) = a - ext x := by
          intros; ring
        rw [e]
        calc cubeCond ω ⟨m, 0⟩ (x, j) * (ext (x + unit j) - ext x) ^ 2
            ≤ 1 * (ext (x + unit j) - ext x) ^ 2 :=
              mul_le_mul_of_nonneg_right hc (sq_nonneg _)
          _ = _ := one_mul _
      · have hc : cubeCond ω ⟨m, 0⟩ (x, j) = 0 := by
          unfold cubeCond
          rw [if_neg]
          rintro ⟨-, -, hadj⟩
          exact h2 ⟨mem_crossingClusterVertices_of_adj hxC ((hmemT _).1 h1) hadj, hadj⟩
        rw [hc, zero_mul]
      · positivity
      · positivity
    · rw [if_neg hxC, zero_add]
      by_cases hxX : x ∈ X
      · rw [if_pos hxX]
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with h1
        · by_cases hc0 : cubeCond ω ⟨m, 0⟩ (x, j) = 0
          · rw [hc0, zero_mul]
            positivity
          · have hcl : cubeCond ω ⟨m, 0⟩ (x, j) = 1 := by
              rcases cubeCond_eq_zero_or (ω := ω) ⟨m, 0⟩ (x, j) with h | h
              · exact absurd h hc0
              · exact le_antisymm (cubeCond_le_one _ _) h
            have hadj : (openGraph ω).Adj x (x + unit j) := by
              unfold cubeCond at hcl
              split_ifs at hcl with hh
              · exact hh.2.2
              · norm_num at hcl
            have hyC : x + unit j ∉ CT := fun hy =>
              hxC (mem_crossingClusterVertices_of_adj hy ((hmemT _).1 hx) hadj.symm)
            rw [show v (x + unit j) = _ from cubeTilePatch_eq_of_not_mem ω uh h1 hyC,
              show v x = _ from cubeTilePatch_eq_of_not_mem ω uh hx hxC,
              cubeAffine_add_unit_sub_two, hcl, one_mul]
        · positivity
      · rw [if_neg hxX]
        refine Finset.sum_nonpos fun j _ => ?_
        split_ifs with h1
        · have hc0 : cubeCond ω ⟨m, 0⟩ (x, j) = 0 := by
            unfold cubeCond
            rw [if_neg]
            rintro ⟨hxU, -, -⟩
            exact hxX (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hxU, (hmemT x).1 hx⟩, hxC⟩)
          rw [hc0, zero_mul]
        · exact le_rfl
  have hCTc : CT ⊆ Tc.vertices := fun x hx => by
    rw [← hTc]
    exact Finset.filter_subset _ _ hx
  have hXc : X ⊆ Tc.vertices := fun x hx => by
    rw [hmemT]
    exact (Finset.mem_filter.1 (Finset.mem_sdiff.1 hx).1).2
  have hvm' : (fun x : ↥CT => ext x) = vm := by
    funext x
    exact cubeExtend_apply_of_mem vm x.2
  have hcf := cubeForm_eq_sum_edges (ω := ω) T ext
  rw [hvm'] at hcf
  have hvol := T.latticeVolume_pos
  calc _ ≤ ∑ x ∈ Tc.vertices, ((if x ∈ CT then ∑ j : Fin d,
          (if x + unit j ∈ CT ∧ (openGraph ω).Adj x (x + unit j) then
            (ext (x + unit j) - ext x) ^ 2 else 0) else 0) +
        (if x ∈ X then ∑ j, p j ^ 2 else 0)) := Finset.sum_le_sum hterm
    _ = ∑ x ∈ CT, ∑ j : Fin d,
          (if x + unit j ∈ CT ∧ (openGraph ω).Adj x (x + unit j) then
            (ext (x + unit j) - ext x) ^ 2 else 0) + (∑ j, p j ^ 2) * X.card := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.inter_eq_right.mpr hCTc, Finset.inter_eq_right.mpr hXc, Finset.sum_const,
          nsmul_eq_mul, mul_comm]
    _ = 2 * T.latticeVolume * cubeNu ω T p + (∑ j, p j ^ 2) * X.card := by
        rw [← hcf, hν]
        field_simp
        rfl

/-- The energy of an affine function on the open edges of a cluster. -/
theorem cubeForm_affine_le (T : TriadicCube d) (p : Fin d → ℝ) :
    cubeForm ω T (cubeClusterAffine ω T p) (cubeClusterAffine ω T p) ≤
      (crossingClusterVertices ω T).card * ∑ j, p j ^ 2 := by
  have hcf := cubeForm_eq_sum_edges (ω := ω) T (fun x => ∑ i, p i * (x i : ℝ))
  have e : (fun x : ↥(crossingClusterVertices ω T) =>
      (fun x : Vertex d => ∑ i, p i * (x i : ℝ)) x) = cubeClusterAffine ω T p := rfl
  rw [e] at hcf
  rw [hcf, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · have h : ∑ i, p i * ((x + unit j) i : ℝ) - ∑ i, p i * (x i : ℝ) = p j := by
      rw [← Finset.sum_sub_distrib]
      simp only [Pi.add_apply, unit, Pi.single_apply, Int.cast_add, mul_add, add_sub_cancel_left]
      simp
    rw [h]
  · positivity

/-- **The patch is close to the affine approximations in `L²` on a tile**, by the Poincaré
inequality on the cluster of the tile (`exists_cube_sum_sq_le_of_eq_zero`). -/
theorem sum_sq_cubeTilePatch_sub_le (hd : 0 < d) {K₀ : ℝ} (hK₀0 : 0 ≤ K₀)
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
    (hP : PartitionEvent ω) {k k₀ : ℕ} {z₀ : Vertex d}
    (hz₀ : ∀ t, (3 : ℤ) ^ k ∣ z₀ t + (3 : ℤ) ^ k / 2) (uh : Vertex d → ℝ) {i : Vertex d}
    (hk₀ : k₀ ≤ k)
    (hscale : ∀ x ∈ (gridTile k z₀ i).parent.vertices, (partitionCube ω x).scale ≤ k₀) :
    ∑ x ∈ (cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)).vertices,
        (cubeTilePatch ω k z₀ uh x - cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) x) ^ 2 ≤
      (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
          ((3 : ℝ) ^ (k + 1)) ^ 2 *
        (4 * ((3 : ℝ) ^ k) ^ d * ∑ j, cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j ^ 2) := by
  set T := gridTile k z₀ i
  set Tc := cornerCube (z₀ + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k)
  have hTc : T.toIntegerCube = Tc := gridTile_toIntegerCube hz₀ i
  have hres : PartitionResolved ω T := fun y hy =>
    (hscale y (T.vertices_subset_parent hy)).trans hk₀
  set p : Fin d → ℝ := fun j => cubeSlope (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) j
  set ℓ := cubeAffine (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i)
  set CT := crossingClusterVertices ω T
  set vm := (cubeNuMax ω T p).1
  set ext := cubeExtend ω T vm
  obtain ⟨-, hν, -⟩ := cubeNuMax_spec hd hP hres p
  set f : Vertex d → ℝ := fun x => if x ∈ CT then cubeTilePatch ω k z₀ uh x - ℓ x else 0
    with hf
  have hCTc : CT ⊆ Tc.vertices := fun x hx => by
    rw [← hTc]
    exact Finset.filter_subset _ _ hx
  have hsum : ∑ x ∈ Tc.vertices, (cubeTilePatch ω k z₀ uh x - ℓ x) ^ 2 =
      ∑ x ∈ CT, f x ^ 2 := by
    rw [← Finset.sum_subset hCTc]
    · exact Finset.sum_congr rfl fun x hx => by rw [hf]; simp only [if_pos hx]
    · intro x hx hxC
      rw [cubeTilePatch_eq_of_not_mem ω uh hx hxC, sub_self]
      ring
  have hf0 : ∀ x, ¬(x ∈ CT ∧ T.IsLatticeInterior x) → f x = 0 := by
    intro x hx
    simp only [hf]
    split_ifs with hxC
    · have hint : ¬ T.IsLatticeInterior x := fun h => hx ⟨hxC, h⟩
      rw [cubeTilePatch_eq_of_not_isLatticeInterior hd hP uh (hCTc hxC) hres hint, sub_self]
    · rfl
  have hP6 := hK₀ ω hP T k₀ (by change k₀ ≤ k; exact hk₀) hscale f hf0
  have hval : ∀ x ∈ CT, f x = ext x - (cubeNuMax ω T p).2 -
      ∑ j, p j * ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) + ℓ (z₀ + ((3 ^ k : ℕ) : ℤ) • i) -
        ℓ x := by
    intro x hx
    simp only [hf, if_pos hx]
    rw [cubeTilePatch_eq_of_mem ω uh (hCTc hx) hx]
  have hEf : ∑ z ∈ CT, ∑ j : Fin d,
      (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2
        else 0) ≤ 2 * cubeForm ω T vm vm + 2 * (CT.card * ∑ j, p j ^ 2) := by
    have hvm' : (fun x : ↥CT => ext x) = vm := by
      funext x
      exact cubeExtend_apply_of_mem vm x.2
    have hcf := cubeForm_eq_sum_edges (ω := ω) T ext
    rw [hvm'] at hcf
    rw [hcf]
    have hterm : ∀ z ∈ CT, ∀ j : Fin d,
        (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2
          else 0) ≤
        2 * (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then
          (ext (z + unit j) - ext z) ^ 2 else 0) + 2 * p j ^ 2 := by
      intro z hz j
      split_ifs with h
      · rw [hval _ h.1, hval z hz]
        have e : ext (z + unit j) - (cubeNuMax ω T p).2 -
            ∑ j, p j * ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) + ℓ (z₀ + ((3 ^ k : ℕ) : ℤ) • i) -
              ℓ (z + unit j) -
            (ext z - (cubeNuMax ω T p).2 - ∑ j, p j * ((z₀ + ((3 ^ k : ℕ) : ℤ) • i) j : ℝ) +
              ℓ (z₀ + ((3 ^ k : ℕ) : ℤ) • i) - ℓ z) =
            (ext (z + unit j) - ext z) - p j := by
          have := cubeAffine_add_unit_sub_two (3 ^ k) uh (z₀ + ((3 ^ k : ℕ) : ℤ) • i) z j
          linarith
        rw [e]
        nlinarith [sq_nonneg (ext (z + unit j) - ext z + p j)]
      · positivity
    calc _ ≤ ∑ z ∈ CT, ∑ j : Fin d,
          (2 * (if z + unit j ∈ CT ∧ (openGraph ω).Adj z (z + unit j) then
            (ext (z + unit j) - ext z) ^ 2 else 0) + 2 * p j ^ 2) :=
          Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun j _ => hterm z hz j
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
  have hvmE : cubeForm ω T vm vm ≤ CT.card * ∑ j, p j ^ 2 := by
    have hle := cubeNu_le_of_affine_boundary (ω := ω) (U := T) p
      (w := cubeClusterAffine ω T p) (by rw [sub_self]; exact Submodule.zero_mem _)
    have hvol := T.latticeVolume_pos
    rw [hν, div_le_div_iff_of_pos_right hvol, div_le_div_iff_of_pos_right (by norm_num)] at hle
    exact hle.trans (cubeForm_affine_le T p)
  have hCT : (CT.card : ℝ) ≤ ((3 : ℝ) ^ k) ^ d := by
    have h1 : CT.card ≤ T.toIntegerCube.vertices.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [IntegerCube.card_vertices_eq] at h1
    have h2 : ((T.toIntegerCube.size ^ d : ℕ) : ℝ) = ((3 : ℝ) ^ k) ^ d := by
      change (((3 ^ k) ^ d : ℕ) : ℝ) = ((3 : ℝ) ^ k) ^ d
      push_cast
      rfl
    have : (CT.card : ℝ) ≤ ((T.toIntegerCube.size ^ d : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hp0 : 0 ≤ ∑ j, p j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hconst : 0 ≤ (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
      ((3 : ℝ) ^ (T.scale + 1)) ^ 2 := by
    have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) ≤ 3 ^ d / (3 ^ d - 1) := div_nonneg (by positivity) (by linarith)
    positivity
  rw [hsum]
  refine hP6.trans ?_
  change (1 + 3 ^ d / (3 ^ d - 1) * 3 ^ (d * k₀)) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
    ((3 : ℝ) ^ (k + 1)) ^ 2 * _ ≤ _
  refine mul_le_mul_of_nonneg_left ?_ hconst
  nlinarith

end Rigidity.Dirichlet
