import PercolationClusterHomogenization.Proofs.Regularity.GeneralMesoscopicTwoSteps
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicTwoTop

/-!
# The coarsening at the top scale in the proof of Lemma 7.3 at `k = 2` in every dimension

At the top scale `T = R / (8A)` of the iteration of Lemma 7.2 for the coarsening `U = [u]_𝒫` of a
function `u` harmonic on `𝒞_∞ ∩ B_R` (Armstrong and Dario, arXiv:1609.09431v2, proof of
Lemma 7.3, the passage from (7.19) to (7.20) and Step 2, (7.22)–(7.23)), in every dimension:

* `anchor_boundsD`: the anchors of the points of `B_ρ`, `ρ ≤ R / 2`, stay in `B_R` when the
  partition cubes have side at most `S'`, `√d S' ≤ R / 4`;
* `sum_abs_coarse_sub_quad_top_leD`: the `ℓ¹` distance of `U` to a quadratic polynomial `W` on
  `B_ρ`, from the moments of the sizes of the partition cubes on `B_R`;
* `harmonicApproximation_error_leD`: the harmonic approximation hypothesis of Lemma 7.2 at the
  radius `R / 2 = 4 A T` bounds the distance of `U` to the lattice harmonic functions on `B_{4T}`,
  the coarse oscillation at `R / 2` being bounded crudely through the largest cube side `S'`;
* `coarse_top_boundsD`: the excesses of `U` on `B_T` over the lattice harmonic quadratic
  functions and over the constants, by the excesses of `u` on the cluster ball `B_R`.

These are the planar statements of `PlanarMesoscopicTwoTop` and `PlanarMesoscopicTwoTopBounds`
in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The anchors of the points of `B_ρ` stay in `B_R` when the cubes have side at most `S'`. -/
theorem anchor_boundsD (hP : PartitionEvent ω) {ρ R S' : ℝ} (hS0 : 0 ≤ S')
    (hS' : Real.sqrt d * S' ≤ R / 4)
    (hρR : ρ ≤ R / 2) {y : Vertex d}
    (hy : dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < ρ)
    (hside : (3 : ℝ) ^ (partitionCube ω y).scale ≤ S') :
    dist (latticeEuclideanEmbedding (partitionAnchor ω y))
        (latticeEuclideanEmbedding (0 : Vertex d)) < R ∧
      (∀ i, |((partitionAnchor ω y i : ℤ) : ℝ)| ≤ R) ∧ ∀ i, |((y i : ℤ) : ℝ)| ≤ R := by
  have hcoord : ∀ i, |((partitionAnchor ω y i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| ≤ S' := fun i =>
    (abs_partitionAnchor_sub_le hP y i).trans hside
  have hd' : dist (latticeEuclideanEmbedding (partitionAnchor ω y)) (latticeEuclideanEmbedding y)
      ≤ Real.sqrt d * S' :=
    dist_latticeEuclideanEmbedding_le hS0 fun i => hcoord i
  have hdist : dist (latticeEuclideanEmbedding (partitionAnchor ω y))
      (latticeEuclideanEmbedding (0 : Vertex d)) < R := by
    have := dist_triangle (latticeEuclideanEmbedding (partitionAnchor ω y))
      (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d))
    have := dist_nonneg (x := latticeEuclideanEmbedding y)
      (y := latticeEuclideanEmbedding (0 : Vertex d))
    linarith
  have hR0 : 0 < R := lt_of_le_of_lt dist_nonneg hdist
  refine ⟨hdist, fun i => ?_, fun i => ?_⟩
  · have := (abs_sub_le_dist_latticeEuclideanEmbedding (partitionAnchor ω y) 0 i).trans
      hdist.le
    simpa using this
  · have := (abs_sub_le_dist_latticeEuclideanEmbedding y 0 i).trans hy.le
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at this
    linarith

/-- **The sum of the coarse error at the top scale.** -/
theorem sum_abs_coarse_sub_quad_top_leD [NeZero d] (hP : PartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ)
    {ρ R S' K₁ K₂ : ℝ} (hR : 0 < R) (hS0 : 0 ≤ S') (hS' : Real.sqrt d * S' ≤ R / 4)
    (hρR : ρ ≤ R / 2)
    (hsize : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R →
        (3 : ℝ) ^ (partitionCube ω y).scale ≤ S')
    (hm₁ : ∑ y ∈ latticeBallPointsD 0 R, (3 : ℝ) ^ (partitionCube ω y).scale ≤ K₁ * R ^ d)
    (hm₂ : ∑ y ∈ latticeBallPointsD 0 R, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d ≤ K₂ * R ^ d)
    (hK₂ : 0 ≤ K₂) (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∑ y ∈ latticeBallPointsD 0 ρ,
        |partitionCoarse (uniqueInfiniteComponent h) u y - latticeQuadFunD a p M y| ≤
      Real.sqrt K₂ * R ^ d * clusterBallVolumeL2 (uniqueInfiniteComponent h) R
          (u - fun x => latticeQuadFunD a p M x.val) +
        d * quadSlopeD p M R * (K₁ * R ^ d) := by
  classical
  have hΛ0 : 0 ≤ quadSlopeD p M R := quadSlopeD_nonneg p M hR.le
  have hball : ∀ y ∈ latticeBallPointsD 0 ρ,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < ρ :=
    fun y hy => mem_latticeBallPointsD.1 hy
  have hρR' : ρ ≤ R := by linarith
  have hsub : latticeBallPointsD 0 ρ ⊆ latticeBallPointsD 0 R := fun y hy =>
    mem_latticeBallPointsD.2 ((hball y hy).trans_le hρR')
  have hb := fun y hy => anchor_boundsD hP hS0 hS' hρR (hball y hy)
    (hsize y ((hball y hy).trans_le hρR'))
  have h1 := sum_abs_coarse_sub_leD hP h u (latticeQuadFunD a p M) hΛ0
    (fun y hy => (hb y hy).1)
    (fun y hy => by
      have := abs_latticeQuadFunD_sub_le a p M (hb y hy).2.2 (hb y hy).2.1
      simp only [Int.cast_sub] at this
      exact this)
  have hm₂' : ∑ y ∈ latticeBallPointsD 0 ρ, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d ≤
      K₂ * R ^ d :=
    (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans hm₂
  have hm₁' : ∑ y ∈ latticeBallPointsD 0 ρ, (3 : ℝ) ^ (partitionCube ω y).scale ≤ K₁ * R ^ d :=
    (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans hm₁
  have hcl : Real.sqrt (∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
      (u x - latticeQuadFunD a p M x.val) ^ 2) =
      Real.sqrt (R ^ d) * clusterBallVolumeL2 (uniqueInfiniteComponent h) R
        (u - fun x => latticeQuadFunD a p M x.val) := by
    rw [clusterBallVolumeL2, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
    rfl
  rw [hcl] at h1
  obtain ⟨E, hEdef⟩ : ∃ x, x = clusterBallVolumeL2 (uniqueInfiniteComponent h) R
      (u - fun x => latticeQuadFunD a p M x.val) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ x, x =
      ∑ y ∈ latticeBallPointsD 0 ρ, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ x, x =
      ∑ y ∈ latticeBallPointsD 0 ρ, (3 : ℝ) ^ (partitionCube ω y).scale := ⟨_, rfl⟩
  rw [← hEdef, ← hQdef, ← hPdef] at h1
  rw [← hEdef]
  rw [← hQdef] at hm₂'
  rw [← hPdef] at hm₁'
  have hE0 : 0 ≤ E := by rw [hEdef]; exact clusterBallVolumeL2_nonnegD _ _ _
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact sum_nonneg fun _ _ => by positivity
  have hs : Real.sqrt Q * Real.sqrt (R ^ d) ≤ Real.sqrt K₂ * R ^ d := by
    rw [← Real.sqrt_mul hQ0]
    have e : Real.sqrt K₂ * R ^ d = Real.sqrt (K₂ * R ^ d * R ^ d) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK₂, mul_assoc, Real.mul_self_sqrt
        (by positivity)]
    rw [e]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hm₂' (by positivity))
  have h3 : Real.sqrt Q * (Real.sqrt (R ^ d) * E) ≤ Real.sqrt K₂ * R ^ d * E := by
    have := mul_le_mul_of_nonneg_right hs hE0
    have e : Real.sqrt Q * (Real.sqrt (R ^ d) * E) = Real.sqrt Q * Real.sqrt (R ^ d) * E := by
      ring
    rw [e]
    exact this
  have h4 : d * quadSlopeD p M R * P ≤ d * quadSlopeD p M R * (K₁ * R ^ d) :=
    mul_le_mul_of_nonneg_left hm₁' (by positivity)
  linarith

end Rigidity.Proofs.Regularity
