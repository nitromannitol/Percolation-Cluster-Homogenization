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

/-- **The harmonic approximation error at `4T`.** -/
theorem harmonicApproximation_error_leD [NeZero d] (hP : PartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ)
    {A α K X R S' : ℝ} (hA : 2 ≤ A) (hK : 0 ≤ K) (hR4 : 4 * Real.sqrt d ≤ R) (hS'0 : 0 ≤ S')
    (hS' : Real.sqrt d * S' ≤ R / 4) (hXT : X ≤ 4 * (R / (8 * A)))
    (hsize : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R →
        (3 : ℝ) ^ (partitionCube ω y).scale ≤ S')
    (hHA : HarmonicApproximation (componentBallSeminorm (latticeComponent d) 0)
      (latticeHarmonicClass 0) (clusterConstants (latticeComponent d)) A α X (R / 2)
      (K / (R / 2) * ⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
        (u - fun _ => a))
      (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val)) :
    ballDist (componentBallSeminorm (latticeComponent d) 0)
        (latticeHarmonicClass 0 (4 * (R / (8 * A)))) (4 * (R / (8 * A)))
        (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) ≤
      (4 * (R / (8 * A))) ^ (1 - α) *
        (2 * Real.sqrt ((4 * Real.sqrt d * S') ^ d) *
            ((⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a)) / R) +
          Real.sqrt (2 ^ d) * K * ((⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun _ => a)) / R) / (R / (8 * A))) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hA0 : 0 < A := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR4
  obtain ⟨T, hT⟩ : ∃ x : ℝ, x = R / (8 * A) := ⟨_, rfl⟩
  rw [← hT]
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨D0R, hD0R⟩ : ∃ x : ℝ,
      x = ⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) :=
    ⟨_, rfl⟩
  rw [← hD0R]
  have hD0R0 : 0 ≤ D0R := by rw [hD0R]; exact iInf_nonneg_of_nonneg fun _ => Real.sqrt_nonneg _
  obtain ⟨U, hU⟩ : ∃ f : latticeComponent d → ℝ,
      f = fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val := ⟨_, rfl⟩
  rw [← hU] at hHA ⊢
  have h4T : 4 * T ≤ R / 2 / A := by
    rw [hT, le_div_iff₀ hA0]; field_simp; linarith
  have hHA' := hHA (4 * T) (by rw [hT]; exact hXT) h4T
  have hAT : A * (4 * T) = R / 2 := by rw [hT]; field_simp; ring
  rw [hAT] at hHA'
  have hsup := iSup_Icc_self_le (f := fun s => ballExcess (componentBallSeminorm
    (latticeComponent d) 0) (clusterConstants (latticeComponent d)) s U / s) (R / 2)
  -- the crude bound of the coarse oscillation at `R/2`
  set c₁ := Real.sqrt ((4 * Real.sqrt d * S') ^ d) with hc₁
  have hc₁0 : 0 ≤ c₁ := Real.sqrt_nonneg _
  have hcrude : ballExcess (componentBallSeminorm (latticeComponent d) 0)
      (clusterConstants (latticeComponent d)) (R / 2) U ≤ 0 + c₁ * D0R := by
    rw [hD0R]
    apply le_add_mul_iInf hc₁0
    intro c
    have hc : (fun _ : latticeComponent d => c) ∈ clusterConstants (latticeComponent d) :=
      ⟨c, fun _ => rfl⟩
    have h1 := ballExcess_le (componentBallSeminorm (latticeComponent d) 0)
      (clusterConstants (latticeComponent d)) (s := R / 2) (u := U) hc
    rw [componentBallSeminorm_apply] at h1
    have h2 := componentBallL2_coarse_sub_const_leD hP h u (ρ := R / 2) (R := R) (S := S')
      (by linarith) hR0 hS'0
      (fun y hy => (anchor_boundsD hP hS'0 hS' le_rfl (mem_latticeBallPointsD.1 hy)
        (hsize y ((mem_latticeBallPointsD.1 hy).trans (by linarith)))).1)
      (fun y hy => hsize y ((mem_latticeBallPointsD.1 hy).trans (by linarith))) c
    have e : S' ^ d * (2 * Real.sqrt d) ^ d * R ^ d / (R / 2) ^ d =
        (4 * Real.sqrt d * S') ^ d := by
      rw [← mul_pow, ← mul_pow, ← div_pow]
      congr 1
      field_simp
      ring
    rw [e, ← hc₁] at h2
    rw [hU] at h1
    calc ballExcess (componentBallSeminorm (latticeComponent d) 0)
          (clusterConstants (latticeComponent d)) (R / 2) U
        ≤ componentBallL2 (latticeComponent d) 0 (R / 2) (U - fun _ => c) := by
          rw [hU]; exact h1
      _ ≤ c₁ * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := by
          rw [hU]; exact h2
      _ = 0 + c₁ * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := by
          ring
  -- the oscillation at `R/2`
  have hosc : (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
      (u - fun _ => a)) ≤ 0 + Real.sqrt (2 ^ d) * D0R := by
    rw [hD0R]
    apply le_add_mul_iInf (Real.sqrt_nonneg _)
    intro c
    have h1 := iInf_le_of_le (f := fun a : ℝ => clusterBallVolumeL2 (uniqueInfiniteComponent h)
      (R / 2) (u - fun _ => a)) (fun _ => Real.sqrt_nonneg _) c
    have h2 := clusterBallVolumeL2_le_sqrt_mul (uniqueInfiniteComponent h)
      (by linarith : 0 < R / 2) (by linarith : R / 2 ≤ R) (u - fun _ => c)
    have e : R / (R / 2) = 2 := by field_simp
    rw [e] at h2
    linarith
  have hrpow : 0 ≤ (4 * T) ^ (1 - α) := Real.rpow_nonneg (by positivity) _
  refine hHA'.trans (mul_le_mul_of_nonneg_left ?_ hrpow)
  have hE : K / (R / 2) * (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
      (u - fun _ => a)) / (4 * T) ≤ Real.sqrt (2 ^ d) * K * (D0R / R) / T := by
    have hK' : 0 ≤ K / (R / 2) := by positivity
    have := mul_le_mul_of_nonneg_left hosc hK'
    rw [div_le_iff₀ (by positivity)]
    calc K / (R / 2) * (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
          (u - fun _ => a)) ≤ K / (R / 2) * (0 + Real.sqrt (2 ^ d) * D0R) := this
      _ = Real.sqrt (2 ^ d) * K * (D0R / R) / T * (2 * T) := by field_simp; ring
      _ ≤ Real.sqrt (2 ^ d) * K * (D0R / R) / T * (4 * T) := by
          have : 0 ≤ Real.sqrt (2 ^ d) * K * (D0R / R) / T := by positivity
          nlinarith
  have hS : ballExcess (componentBallSeminorm (latticeComponent d) 0)
      (clusterConstants (latticeComponent d)) (R / 2) U / (R / 2) ≤ 2 * c₁ * (D0R / R) := by
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ 0 + c₁ * D0R := hcrude
      _ = 2 * c₁ * (D0R / R) * (R / 2) := by field_simp; ring
  have := hsup.trans hS
  linarith

end Rigidity.Proofs.Regularity
