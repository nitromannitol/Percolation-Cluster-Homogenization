import PercolationClusterHomogenization.Proofs.Regularity.GeneralCoarseComparisonAS
import PercolationClusterHomogenization.Proofs.Cluster.SobolevMeanZero

/-!
# The bound of the coarsened function on a triadic cube (Step 2 of Lemma 7.1)

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Step 2, with `w = a` a constant, on
the triadic cubes `□_j` of `ℤᵈ`: for `u` harmonic on the cluster,
`‖[u]_𝒫 - a‖_{L̲²(□_j)} ≤ K |□_{j+3}|^{-1/2} ‖u - a‖_{L²(C_*(□_{j+3}))}`.
As in the planar case (`squareL2_coarse_sub_le`), in place of the Sobolev step in `L^{p'}` of the
paper the proof splits `[u]_𝒫 - a` into `[u]_𝒫 - m`, with `m` the mean of `[u]_𝒫` on `□_j`, and
`m - a`:

* `sum_sq_coarse_sub_mean_le_cube`: the Poincaré inequality on `□_j`
  (`IntegerCube.sum_abs_sub_mean_rpow_le`), Lemma 3.3 for the partition into good cubes
  (`partition_sum_gradNormIn_coarseAnchor_rpow_le`, with the weights `size(□_𝒫(z))^{2d-1}`), the
  Hölder inequality with the Meyers estimate and the moments of the partition sizes, and the
  Caccioppoli inequality bound `[u]_𝒫 - m`;
* `cubeL2_coarse_sub_le`: averaging `m - a = (m - [u]_𝒫) + ([u]_𝒫 - u) + (u - a)` over the
  cluster `C_*(□_j)`, which carries a fixed proportion of `□_j`, bounds `m - a` by the first part,
  the comparison (7.8) and `u - a`.

`cubeCoarseBoundAS_holds` checks the hypotheses almost surely above a minimal scale.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster Rigidity.Proofs.Cluster.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

theorem toIntegerCube_vertices_zero_eq (j : ℕ) :
    (⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices = triadicCubeFinset d j 0 := by
  ext x
  rw [TriadicCube.mem_toIntegerCube_vertices, mem_cubeFinset_iff_vertices]

/-- The constant of Lemma 3.3 for the partition into good cubes. -/
noncomputable def partitionGradConst (d : ℕ) : ℝ :=
  2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) * (2 * √(d : ℝ))

theorem partitionGradConst_nonneg (d : ℕ) : 0 ≤ partitionGradConst d := by
  unfold partitionGradConst; positivity

/-- **The Poincaré inequality on `□_j`**. -/
theorem sum_sq_sub_mean_cube_le (j : ℕ) (f : Vertex d → ℝ) :
    ∑ x ∈ triadicCubeFinset d j 0,
        (f x - (∑ y ∈ triadicCubeFinset d j 0, f y) / ((3 : ℝ) ^ j) ^ d) ^ 2 ≤
      2 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * ∑ x ∈ triadicCubeFinset d j 0,
        gradNormIn (nearestNeighborGraph d) (triadicCubeFinset d j 0) f x ^ 2 := by
  have hB : 0 < (⟨j, 0⟩ : TriadicCube d).toIntegerCube.size := by
    change 0 < 3 ^ j
    positivity
  have h := IntegerCube.sum_abs_sub_mean_rpow_le _ hB f (p := 2) (by norm_num)
  have hsize : (((⟨j, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) = 3 ^ j := by
    change ((3 ^ j : ℕ) : ℝ) = _
    push_cast
    rfl
  have hc : (d : ℝ) ^ ((2 : ℝ) - 1) * ((d : ℝ) * √2 ^ (2 : ℝ)) *
      (((⟨j, 0⟩ : TriadicCube d).toIntegerCube.size : ℕ) : ℝ) ^ (2 : ℝ) =
      2 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ j) ^ 2 := by
    rw [hsize, Real.rpow_two, Real.rpow_two, Real.sq_sqrt (by norm_num),
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  rw [hc, toIntegerCube_vertices_zero_eq, card_triadicCubeFinset_real] at h
  simp only [Real.rpow_two, sq_abs] at h
  exact h

set_option maxHeartbeats 400000 in
/-- **The Hölder step with the Meyers estimate** for a weight `a` on the crossing cluster of
`□_j`: `∑ |∇u|² a ≤ C_M^{1/q} K_a^{1/q'} A / 3^d`, with `A` the energy on `□_{j+1}` of `u` on the
crossing cluster of `□_{j+2}`. -/
theorem sum_gradNormIn_mul_le_of_meyers_cube (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h02 : crossingClusterVertices ω ⟨j, 0⟩ ⊆ crossingClusterVertices ω ⟨j + 2, 0⟩)
    {q CM Ka : ℝ} (hq : 1 < q) (hCM : 0 ≤ CM) (hKa : 0 ≤ Ka)
    (hM : avg (cube j (0 : Vertex d)) (fun x => clusterEnergy ω
        (crossingClusterVertices ω ⟨j + 2, 0⟩) (Rigidity.Section3.extend C u) x ^ q) ≤
      CM * avg (enl 1 j (0 : Vertex d)) (clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩)
        (Rigidity.Section3.extend C u)) ^ q)
    (a : Vertex d → ℝ) (ha : ∀ z, 0 ≤ a z)
    (hmom : ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, a z ^ Real.conjExponent q ≤
      Ka * ((3 : ℝ) ^ j) ^ d) :
    ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, gradNormIn (openGraph ω)
        (crossingClusterVertices ω ⟨j, 0⟩) (Rigidity.Section3.extend C u) z ^ 2 * a z ≤
      CM ^ (1 / q) * Ka ^ (1 / Real.conjExponent q) *
        ((∑ z ∈ enl 1 j (0 : Vertex d), clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩)
          (Rigidity.Section3.extend C u) z) / 3 ^ d) := by
  set f := Rigidity.Section3.extend C u with hfdef
  obtain ⟨E, hEdef⟩ : ∃ E : Vertex d → ℝ,
      E = clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩) f := ⟨_, rfl⟩
  rw [← hEdef] at hM ⊢
  have hE0 : ∀ z, 0 ≤ E z := fun z => by rw [hEdef]; exact clusterEnergy_nonneg _ _ _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 j (0 : Vertex d), E z := ⟨_, rfl⟩
  rw [← hAdef]
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Finset.sum_nonneg fun z _ => hE0 z
  set N : ℝ := ((3 : ℝ) ^ j) ^ d with hNdef
  have hN : (0 : ℝ) < N := by positivity
  have hF : (0 : ℝ) < 3 ^ d := by positivity
  have hcube : ((cube j (0 : Vertex d)).card : ℝ) = N := card_cube j 0
  have henl : ((enl 1 j (0 : Vertex d)).card : ℝ) = 3 ^ d * N := by
    rw [card_enl, hNdef, ← mul_pow, pow_succ']
  have hgE : ∀ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
      gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2 ≤ E z := by
    intro z hz
    have hz2 := h02 hz
    rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
      split_ifs <;> positivity)), hEdef, clusterEnergy, if_pos hz2, clusterGradSq,
      ← Finset.sum_filter]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hy2, h02 hy1⟩)
      fun _ _ _ => sq_nonneg _
  have hbq : ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, (gradNormIn (openGraph ω)
      (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2) ^ q ≤ CM * N * (A / (3 ^ d * N)) ^ q := by
    have hq0 : 0 ≤ q := by linarith
    calc ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, (gradNormIn (openGraph ω)
          (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2) ^ q
        ≤ ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩, E z ^ q :=
          Finset.sum_le_sum fun z hz => Real.rpow_le_rpow (sq_nonneg _) (hgE z hz) hq0
      _ ≤ ∑ z ∈ cube j (0 : Vertex d), E z ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => mem_cube_zero_of_mem_cubeFinset
              (mem_cubeFinset_of_mem_crossingClusterVertices hz))
            fun z _ _ => Real.rpow_nonneg (hE0 z) _
      _ = N * avg (cube j (0 : Vertex d)) (fun x => E x ^ q) := by
          rw [avg, hcube]; field_simp
      _ ≤ N * (CM * avg (enl 1 j (0 : Vertex d)) E ^ q) :=
          mul_le_mul_of_nonneg_left hM hN.le
      _ = CM * N * (A / (3 ^ d * N)) ^ q := by
          rw [avg, henl, ← hAdef]; ring
  exact holder_meyers_bound_of_factor (crossingClusterVertices ω ⟨j, 0⟩) (a := a)
    (b := fun z => gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩) f z ^ 2)
    (fun z _ => ha z) (fun z _ => sq_nonneg _) hq hKa hCM hN hA0 hF hbq hmom

set_option maxHeartbeats 400000 in
/-- **The bound of `[u]_𝒫` minus its mean on one cube**: from the Poincaré inequality on `□_j`,
Lemma 3.3 for the partition into good cubes, the Hölder inequality with the Meyers estimate `hM`
and the moments `hmom` of the partition sizes, and the Caccioppoli inequality on `𝒞 ∩ □_{j+2}`. -/
theorem sum_sq_coarse_sub_mean_le_cube (hd : 0 < d) (hP : PartitionEvent ω)
    (C : OpenComponent ω) (u : C → ℝ) {j : ℕ} (hres0 : PartitionResolved ω ⟨j, 0⟩)
    (h02 : crossingClusterVertices ω ⟨j, 0⟩ ⊆ crossingClusterVertices ω ⟨j + 2, 0⟩)
    (h2C : ∀ x ∈ crossingClusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (hU3 : ∀ x ∈ triadicCubeFinset d (j + 2) 0, x ∈ C.supp →
      x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩)
    (hharm : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    {q CM Ks : ℝ} (hq : 1 < q) (hCM : 0 ≤ CM) (hKs : 0 ≤ Ks)
    (hM : avg (cube j (0 : Vertex d)) (fun x => clusterEnergy ω
        (crossingClusterVertices ω ⟨j + 2, 0⟩) (Rigidity.Section3.extend C u) x ^ q) ≤
      CM * avg (enl 1 j (0 : Vertex d)) (clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩)
        (Rigidity.Section3.extend C u)) ^ q)
    (hmom : ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
        (((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * d - 1)) ^ Real.conjExponent q ≤
      Ks * ((3 : ℝ) ^ j) ^ d) (c : ℝ) :
    ∑ x ∈ triadicCubeFinset d j 0, (partitionCoarse C u x -
        (∑ y ∈ triadicCubeFinset d j 0, partitionCoarse C u y) / ((3 : ℝ) ^ j) ^ d) ^ 2 ≤
      16 * (d : ℝ) ^ 3 * partitionGradConst d ^ 2 *
        (CM ^ (1 / q) * Ks ^ (1 / Real.conjExponent q)) *
        ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, (Rigidity.Section3.extend C u x - c) ^ 2 := by
  have hPo := sum_sq_sub_mean_cube_le j (partitionCoarse C u)
  have hL3 := partition_sum_gradNormIn_coarseAnchor_rpow_le hd hP hres0
    (Rigidity.Section3.extend C u) (s := 2) (by norm_num)
  rw [toIntegerCube_vertices_zero_eq] at hL3
  have e1 : ∀ x ∈ triadicCubeFinset d j 0, gradNormIn (nearestNeighborGraph d)
      (triadicCubeFinset d j 0) (fun x => Rigidity.Section3.extend C u (partitionAnchor ω x))
        x ^ (2 : ℝ) =
      gradNormIn (nearestNeighborGraph d) (triadicCubeFinset d j 0) (partitionCoarse C u) x ^ 2 :=
    fun x _ => by rw [Real.rpow_two]; rfl
  have e2 : ∀ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * d - 1) *
        gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩)
          (Rigidity.Section3.extend C u) z ^ (2 : ℝ) =
      gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨j, 0⟩)
          (Rigidity.Section3.extend C u) z ^ 2 *
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * d - 1) :=
    fun z _ => by rw [Real.rpow_two, mul_comm]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Real.rpow_two] at hL3
  have hW := sum_gradNormIn_mul_le_of_meyers_cube C u h02 hq hCM hKs hM
    (fun z => ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * d - 1))
    (fun z => by positivity) hmom
  have hcac := energy_enl_le_caccioppoli_cube C u h2C hU3 hharm c
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ z ∈ enl 1 j (0 : Vertex d),
      clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩) (Rigidity.Section3.extend C u) z :=
    ⟨_, rfl⟩
  rw [← hAdef] at hW hcac
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = CM ^ (1 / q) * Ks ^ (1 / Real.conjExponent q) := ⟨_, rfl⟩
  rw [← hPdef] at hW ⊢
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  set C3 := partitionGradConst d with hC3
  have hC30 : 0 ≤ C3 := partitionGradConst_nonneg d
  have hK0 : 0 ≤ C3 ^ 2 := sq_nonneg _
  obtain ⟨Ssum, hSdef⟩ : ∃ S : ℝ, S = ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩,
      (Rigidity.Section3.extend C u x - c) ^ 2 := ⟨_, rfl⟩
  rw [← hSdef] at hcac ⊢
  have hS0 : 0 ≤ Ssum := by rw [hSdef]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN : (0 : ℝ) < 3 ^ j := by positivity
  have hF : (0 : ℝ) < 3 ^ d := by positivity
  have hF1 : (1 : ℝ) ≤ 9 * 3 ^ d := by
    have : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    linarith
  have hfinal : 16 * (d : ℝ) ^ 3 * C3 ^ 2 * P * Ssum / (9 * 3 ^ d) ≤
      16 * (d : ℝ) ^ 3 * C3 ^ 2 * P * Ssum :=
    div_le_self (by positivity) hF1
  calc _ ≤ _ := hPo
    _ ≤ 2 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * (C3 ^ 2 * (P * (A / 3 ^ d))) :=
        mul_le_mul_of_nonneg_left (hL3.trans (mul_le_mul_of_nonneg_left hW hK0)) (by positivity)
    _ = 2 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * C3 ^ 2 * P / 3 ^ d * A := by ring
    _ ≤ 2 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * C3 ^ 2 * P / 3 ^ d *
          (8 * d / ((3 : ℝ) ^ (j + 1)) ^ 2 * Ssum) :=
        mul_le_mul_of_nonneg_left hcac (by positivity)
    _ = 16 * (d : ℝ) ^ 3 * C3 ^ 2 * P * Ssum / (9 * 3 ^ d) := by
        rw [pow_succ]; field_simp; ring
    _ ≤ _ := hfinal

/-- `(x + y + z)² ≤ 3 (x² + y² + z²)`. -/
theorem sq_add_add_le_three (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

set_option maxHeartbeats 400000 in
/-- **Step 2 on one cube from its two parts.** If `[u]_𝒫 - m` is bounded on `□_j`, `u - [u]_𝒫`
on `C_*(□_j)`, and `C_*(□_j)` carries at least `κ |□_j|` vertices, then
`‖[u]_𝒫 - a‖_{L̲²(□_j)} ≤ 27^{d/2} (2 K₁ + 6 (K₁ + K₂ + 1) / κ)^{1/2} ‖u - a‖_{L̲²(C_*(□_{j+3}))}`,
the norm on `C_*(□_{j+3})` being normalized by `|□_{j+3}|`. -/
theorem cubeL2_coarse_sub_le (C : OpenComponent ω) (u : C → ℝ) {j : ℕ} (a m : ℝ)
    {K₁ K₂ κ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hκ : 0 < κ)
    (hPo : ∑ x ∈ triadicCubeFinset d j 0, (partitionCoarse C u x - m) ^ 2 ≤
      K₁ * ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩,
        (Rigidity.Section3.extend C u x - a) ^ 2)
    (hL : ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩,
        (Rigidity.Section3.extend C u x - partitionCoarse C u x) ^ 2 ≤
      K₂ * ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩,
        (Rigidity.Section3.extend C u x - a) ^ 2)
    (hST : crossingClusterVertices ω ⟨j, 0⟩ ⊆ crossingClusterVertices ω ⟨j + 3, 0⟩)
    (hcard : κ * ((3 : ℝ) ^ j) ^ d ≤ (crossingClusterVertices ω ⟨j, 0⟩).card) :
    cubeL2 d j (fun y => partitionCoarse C u y - a) ≤
      Real.sqrt (27 ^ d) * Real.sqrt (2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) *
        clusterCubeL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - a) := by
  set f := Rigidity.Section3.extend C u with hfdef
  set g := partitionCoarse C u with hgdef
  set T := ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, (f x - a) ^ 2 with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set N : ℝ := ((3 : ℝ) ^ j) ^ d with hNdef
  have hN : (0 : ℝ) < N := by positivity
  have hSB : crossingClusterVertices ω ⟨j, 0⟩ ⊆ triadicCubeFinset d j 0 :=
    fun x hx => mem_cubeFinset_of_mem_crossingClusterVertices hx
  -- the mean against `a`
  have hpt : ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩,
      (m - a) ^ 2 ≤ 3 * ((g x - m) ^ 2 + (f x - g x) ^ 2 + (f x - a) ^ 2) := by
    intro x _
    have h := sq_add_add_le_three (m - g x) (g x - f x) (f x - a)
    have e : m - g x + (g x - f x) + (f x - a) = m - a := by ring
    rw [e] at h
    calc (m - a) ^ 2 ≤ _ := h
      _ = 3 * ((g x - m) ^ 2 + (f x - g x) ^ 2 + (f x - a) ^ 2) := by ring
  have hS : ((crossingClusterVertices ω ⟨j, 0⟩).card : ℝ) * (m - a) ^ 2 ≤
      3 * (K₁ + K₂ + 1) * T := by
    have h1 : ∑ _x ∈ crossingClusterVertices ω ⟨j, 0⟩, (m - a) ^ 2 ≤
        ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩,
          3 * ((g x - m) ^ 2 + (f x - g x) ^ 2 + (f x - a) ^ 2) :=
      Finset.sum_le_sum hpt
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at h1
    have h2 : ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, (g x - m) ^ 2 ≤
        ∑ x ∈ triadicCubeFinset d j 0, (g x - m) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hSB fun _ _ _ => sq_nonneg _
    have h3 : ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, (f x - a) ^ 2 ≤ T :=
      Finset.sum_le_sum_of_subset_of_nonneg hST fun _ _ _ => sq_nonneg _
    linarith
  have hm : N * (m - a) ^ 2 ≤ 3 * (K₁ + K₂ + 1) / κ * T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    calc N * (m - a) ^ 2 * κ = κ * N * (m - a) ^ 2 := by ring
      _ ≤ ((crossingClusterVertices ω ⟨j, 0⟩).card : ℝ) * (m - a) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ ≤ _ := hS
  -- the cube
  have hB : ∑ x ∈ triadicCubeFinset d j 0, (g x - a) ^ 2 ≤
      (2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) * T := by
    have h1 : ∀ x ∈ triadicCubeFinset d j 0,
        (g x - a) ^ 2 ≤ 2 * (g x - m) ^ 2 + 2 * (m - a) ^ 2 :=
      fun x _ => by nlinarith [sq_nonneg (g x - m - (m - a))]
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      card_triadicCubeFinset_real] at h2
    have e : 6 * (K₁ + K₂ + 1) / κ * T = 2 * (3 * (K₁ + K₂ + 1) / κ * T) := by ring
    nlinarith
  unfold cubeL2 clusterCubeL2
  have hK0 : 0 ≤ 2 * K₁ + 6 * (K₁ + K₂ + 1) / κ := by positivity
  have e27 : ((3 : ℝ) ^ (j + 3)) ^ d = 27 ^ d * N := by
    rw [hNdef, ← mul_pow, pow_add, mul_comm ((3 : ℝ) ^ j) (3 ^ 3)]; norm_num
  have hNne : N ≠ 0 := hN.ne'
  have hrhs : Real.sqrt (27 ^ d) * Real.sqrt (2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) *
      Real.sqrt (T / ((3 : ℝ) ^ (j + 3)) ^ d) =
      Real.sqrt ((2 * K₁ + 6 * (K₁ + K₂ + 1) / κ) * T / N) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), e27]
    congr 1
    field_simp
  rw [hrhs]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hB hN.le)

/-- The sums of squares from the comparison (7.8) in the normalized form. -/
theorem sum_sq_le_of_clusterCubeL2_le {j : ℕ} {g f : Vertex d → ℝ} {K : ℝ}
    (h : clusterCubeL2 ω j g ≤ K / 3 ^ j * clusterCubeL2 ω (j + 3) f) :
    ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, g x ^ 2 ≤
      K ^ 2 * ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, f x ^ 2 := by
  unfold clusterCubeL2 at h
  set A := ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, g x ^ 2 with hA
  set B := ∑ x ∈ crossingClusterVertices ω ⟨j + 3, 0⟩, f x ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  set N : ℝ := ((3 : ℝ) ^ j) ^ d with hNdef
  have hN : (0 : ℝ) < N := by positivity
  have e27 : ((3 : ℝ) ^ (j + 3)) ^ d = 27 ^ d * N := by
    rw [hNdef, ← mul_pow, pow_add, mul_comm ((3 : ℝ) ^ j) (3 ^ 3)]; norm_num
  rw [e27] at h
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), div_pow] at hsq
  have h27 : (1 : ℝ) ≤ 27 ^ d := one_le_pow₀ (by norm_num)
  have h9 : (1 : ℝ) ≤ (3 ^ j) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have h1 : A ≤ K ^ 2 * B / ((3 ^ j) ^ 2 * 27 ^ d) := by
    rw [div_le_iff₀ hN] at hsq
    calc A ≤ K ^ 2 / (3 ^ j) ^ 2 * (B / (27 ^ d * N)) * N := hsq
      _ = K ^ 2 * B / ((3 ^ j) ^ 2 * 27 ^ d) := by field_simp
  calc A ≤ K ^ 2 * B / ((3 ^ j) ^ 2 * 27 ^ d) := h1
    _ ≤ K ^ 2 * B := div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le h9 h27)

/-- **The crossing cluster of `□_{i+1}` carries a fixed proportion of the cube**, from the density
of the infinite cluster in `□_i` and the inclusion of `𝒞 ∩ □_i` in `C_*(□_{i+1})`. -/
theorem card_crossingClusterVertices_succ_ge (hd : 0 < d) (C : OpenComponent ω) {ℓ κ : ℝ}
    (hcube : ClusterCubeDensity C 0 (Real.sqrt d) ℓ κ) {i : ℕ} (hi : ℓ ≤ 3 ^ i)
    (hsucc : ∀ x ∈ triadicCubeFinset d i 0, x ∈ C.supp →
      x ∈ crossingClusterVertices ω ⟨i + 1, 0⟩) :
    κ / 3 ^ d * ((3 : ℝ) ^ (i + 1)) ^ d ≤ (crossingClusterVertices ω ⟨i + 1, 0⟩).card := by
  have hin : ∀ y ∈ triadicCube d i 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) <
        Real.sqrt d * 3 ^ i := by
    intro y hy
    rw [← coe_triadicCubeFinset] at hy
    exact dist_lt_of_mem_cubeFinset_of_le hd le_rfl y hy
  have h := hcube i 0 hi hin
  have hle : (clusterCubePoints C 0 (Real.sqrt d * 3 ^ i) i 0).card ≤
      (crossingClusterVertices ω ⟨i + 1, 0⟩).card := by
    refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
    · intro x hx
      have hx' : x ∈ clusterCubePoints C 0 (Real.sqrt d * 3 ^ i) i 0 := hx
      simp only [clusterCubePoints, mem_filter] at hx'
      refine hsucc x.val ?_ x.2
      rw [mem_cubeFinset_iff]
      intro k
      simpa using hx'.2 k
    · intro x _ y _ hxy
      exact Subtype.val_injective hxy
  have hF : (0 : ℝ) < 3 ^ d := by positivity
  calc κ / 3 ^ d * ((3 : ℝ) ^ (i + 1)) ^ d = κ * 3 ^ (d * i) := by
        rw [pow_succ, mul_pow, ← pow_mul, mul_comm i d]; field_simp
    _ ≤ _ := h
    _ ≤ _ := by exact_mod_cast hle

end Rigidity.Proofs.Regularity
