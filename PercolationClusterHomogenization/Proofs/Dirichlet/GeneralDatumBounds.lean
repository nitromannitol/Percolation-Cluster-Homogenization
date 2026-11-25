import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralPropSixOne
import PercolationClusterHomogenization.Proofs.Dirichlet.HomogenizedSolution

/-!
# Bounds on the datum of the homogenized problem in every dimension

Under moment bounds `|□_m|⁻¹ Σ_{x ∈ □_m} size(□_𝒫(x))^t ≤ C_M` (the first bound of (2.13) of
Armstrong and Dario above the minimal scale), Lemma 6.4 (iii) for the partition into good cubes
(`cube_sum_abs_grad_boundaryInterpolation_rpow_div_le`) and the bound of the moments of the reach
scales give, for `1 ≤ s < p'`,
`|□_m|⁻¹ Σ_{edges in □_m} |∇w̃|^s ≤ C(s, p', C_M) M^s`, `M = cubeGradNorm`, the normalized
`L^{p'}` norm of the open gradient of `u` on `C_*(□_m)` (`sum_abs_grad_cubeDatum_rpow_div_le`).
The planar form is `sum_abs_grad_planarDatum_rpow_div_le`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- The normalized `L^{p'}` norm
`M = (|□_m|⁻¹ Σ_{x ∈ C_*(□_m)} |∇u 1_{a≠0}|^{p'}(x))^{1/p'}` of the open gradient of `u` on the
crossing cluster of `□_m`. -/
noncomputable def cubeGradNorm (ω : Configuration d) (m : ℕ) (p' : ℝ) (u : Vertex d → ℝ) : ℝ :=
  ((∑ x ∈ crossingClusterVertices ω ⟨m, 0⟩,
      gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨m, 0⟩) u x ^ p') /
    ((3 : ℝ) ^ m) ^ d) ^ (1 / p')

theorem cubeGradNorm_nonneg (ω : Configuration d) (m : ℕ) (p' : ℝ) (u : Vertex d → ℝ) :
    0 ≤ cubeGradNorm ω m p' u := by
  unfold cubeGradNorm
  exact Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun z _ =>
    Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) (by positivity)) _

/-- The constant of Lemma 6.4 (iii) for the partition into good cubes under the moment bound
`C_M`. -/
noncomputable def cubeDatumConst (d : ℕ) (s p' CM : ℝ) : ℝ :=
  (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) * cubeConstThree d ^ s *
      CM ^ (1 - s / p') +
    2 * (d : ℝ) * cubeConstTwo d ^ s * (7 ^ d * CM) ^ (1 - s / p'))

/-- **The gradient of the datum under the moment bounds.** -/
theorem sum_abs_grad_cubeDatum_rpow_div_le (hd : 0 < d) (hP : PartitionEvent ω) {m : ℕ}
    (hU : PartitionResolved ω ⟨m, 0⟩) {s p' CM : ℝ} (hs : 1 ≤ s) (hsp : s < p')
    (hmom3 : (∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
        ((3 : ℝ) ^ (partitionCube ω x).scale) ^ ((s * d - 1) * (p' / (p' - s)))) /
        ((3 : ℝ) ^ m) ^ d ≤ CM)
    (hmom2 : (∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
        ((3 : ℝ) ^ (partitionCube ω x).scale) ^ ((s * d) * (p' / (p' - s)) + d)) /
        ((3 : ℝ) ^ m) ^ d ≤ CM)
    (u : Vertex d → ℝ) :
    (∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices, ∑ j : Fin d,
        (if x + unit j ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices then
          |cubeDatum hd hP m hU u (x + unit j) - cubeDatum hd hP m hU u x| ^ s else 0)) /
        ((3 : ℝ) ^ m) ^ d ≤
      cubeDatumConst d s p' CM * cubeGradNorm ω m p' u ^ s := by
  have hV : (0 : ℝ) < ((3 : ℝ) ^ m) ^ d := by positivity
  have h := cube_sum_abs_grad_boundaryInterpolation_rpow_div_le hd hP hU
    (cubeClusterBoundary_subset ω m) u hs hsp hV
  refine h.trans ?_
  unfold cubeInterpolationBound cubeDatumConst
  have he : 0 ≤ 1 - s / p' := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hsp.le
  have hCU : crossingClusterVertices ω ⟨m, 0⟩ ⊆
      (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices := Finset.filter_subset _ _
  have hM3 : (∑ z ∈ crossingClusterVertices ω ⟨m, 0⟩,
      (((3 : ℝ) ^ (partitionCube ω z).scale) ^ (s * d - 1)) ^ (p' / (p' - s))) /
        ((3 : ℝ) ^ m) ^ d ≤ CM := by
    have e : ∀ z, (((3 : ℝ) ^ (partitionCube ω z).scale) ^ (s * d - 1)) ^ (p' / (p' - s)) =
        ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((s * d - 1) * (p' / (p' - s))) := fun z => by
      rw [← Real.rpow_mul (by positivity)]
    simp only [e]
    refine le_trans (div_le_div_of_nonneg_right ?_ hV.le) hmom3
    exact Finset.sum_le_sum_of_subset_of_nonneg hCU fun _ _ _ => by positivity
  have hM2 : (∑ z ∈ crossingClusterVertices ω ⟨m, 0⟩,
      (((3 : ℝ) ^ (partitionCoarseData hd hP ⟨m, 0⟩ hU).reachScale z) ^
        (s * d)) ^ (p' / (p' - s))) / ((3 : ℝ) ^ m) ^ d ≤ 7 ^ d * CM := by
    have e : ∀ z, (((3 : ℝ) ^ (partitionCoarseData hd hP ⟨m, 0⟩ hU).reachScale z) ^
        (s * d)) ^ (p' / (p' - s)) =
        ((3 : ℝ) ^ (partitionCoarseData hd hP ⟨m, 0⟩ hU).reachScale z) ^
          ((s * d) * (p' / (p' - s))) := fun z => by
      rw [← Real.rpow_mul (by positivity)]
    simp only [e]
    have h1 := sum_three_pow_reachScale_partition_rpow_le hd hP hU ((s * d) * (p' / (p' - s)))
    rw [div_le_iff₀ hV]
    rw [div_le_iff₀ hV] at hmom2
    have h7 : (0 : ℝ) ≤ 7 ^ d := by positivity
    nlinarith
  have hG : ((∑ z ∈ crossingClusterVertices ω ⟨m, 0⟩,
      gradNormIn (openGraph ω) (crossingClusterVertices ω ⟨m, 0⟩) u z ^ p') /
        ((3 : ℝ) ^ m) ^ d) ^ (s / p') = cubeGradNorm ω m p' u ^ s := by
    unfold cubeGradNorm
    rw [← Real.rpow_mul (div_nonneg (Finset.sum_nonneg fun z _ =>
      Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) hV.le)]
    congr 1
    field_simp
  rw [hG]
  have hGs : 0 ≤ cubeGradNorm ω m p' u ^ s := Real.rpow_nonneg (cubeGradNorm_nonneg _ _ _ _) _
  refine mul_le_mul_of_nonneg_right ?_ hGs
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
  · refine mul_le_mul_of_nonneg_left ?_ (by
      have := cubeConstThree_nonneg d
      positivity)
    exact Real.rpow_le_rpow (by positivity) hM3 he
  · refine mul_le_mul_of_nonneg_left ?_ (by
      have := cubeConstTwo_nonneg d
      positivity)
    exact Real.rpow_le_rpow (by positivity) hM2 he

end Rigidity.Dirichlet
