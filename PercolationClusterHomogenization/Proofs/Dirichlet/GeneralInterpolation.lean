import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralPoincareZero
import PercolationClusterHomogenization.Proofs.Dirichlet.Interpolation

/-!
# Lemma 6.4 (iii) for the partition into good cubes of `ℤᵈ`

For the coarse-graining data of a resolved cube `U` of `ℤᵈ` (`partitionCoarseData`), Lemma 3.2 of
Armstrong and Dario holds with the reach scale `ρ` in place of the size of the partition cube
(`partition_sum_abs_sub_coarseAnchor_rpow_le`) and Lemma 3.3 with the size of the partition cube
(`partition_sum_gradNormIn_coarseAnchor_rpow_le`). With the weighted Hölder inequality, the
normalized `L^s` norm of the gradient of the boundary interpolation `w̃` is at most
`3^{s-1} (d 2^{s/2} C₃^s 𝔐'_{sd-1} + 2 d C₂^s 𝔐_{sd}) (V⁻¹ Σ_{C_*(U)} |∇u 1_{a≠0}|^p)^{s/p}`,
with `𝔐'_a = (V⁻¹ Σ_z size(□_𝒫(z))^{a p/(p-s)})^{1-s/p}` and `𝔐_a` the same with `3^{ρ(z)}`
(`cube_sum_abs_grad_boundaryInterpolation_rpow_div_le`), Armstrong and Dario, Lemma 6.4 (iii), for
the partition into good cubes in every dimension. The moments of the reach scales are bounded by
those of the partition sizes: `Σ_z (3^{ρ(z)})^t ≤ 7^d Σ_{x ∈ U} (3^{s(x)})^{t + d}`, since the reach
scale at `z` is the largest scale of a partition cube whose region contains `z`, and the region of
the partition cube of `x` lies in its `3s`-neighbourhood, with `7^d 3^{d s(x)}` vertices
(`sum_three_pow_reachScale_partition_rpow_le`). The planar forms are
`planar_sum_abs_grad_boundaryInterpolation_rpow_div_le` and `sum_three_pow_reachScale_rpow_le`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Dirichlet

variable {d : ℕ} {ω : Configuration d}

/-- The constant of Lemma 3.2 for the partition into good cubes. -/
noncomputable def cubeConstTwo (d : ℕ) : ℝ :=
  3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d * (2 * √(d : ℝ))

/-- The constant of Lemma 3.3 for the partition into good cubes. -/
noncomputable def cubeConstThree (d : ℕ) : ℝ :=
  2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) * (2 * √(d : ℝ))

theorem cubeConstTwo_nonneg (d : ℕ) : 0 ≤ cubeConstTwo d := by unfold cubeConstTwo; positivity

theorem cubeConstThree_nonneg (d : ℕ) : 0 ≤ cubeConstThree d := by
  unfold cubeConstThree; positivity

/-- The right side of Lemma 6.4 (iii) for the partition into good cubes: the moments of the
partition sizes and of the reach scales times the normalized `L^p` norm of the open gradient of `u`
to the power `s/p`. -/
noncomputable def cubeInterpolationBound (hd : 0 < d) (hP : PartitionEvent ω) (U : TriadicCube d)
    (hU : PartitionResolved ω U) (s p V : ℝ) (u : Vertex d → ℝ) : ℝ :=
  (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) * cubeConstThree d ^ s *
      ((∑ z ∈ crossingClusterVertices ω U,
        (((3 : ℝ) ^ (partitionCube ω z).scale) ^ (s * d - 1)) ^ (p / (p - s))) / V) ^
          (1 - s / p) +
    2 * (d : ℝ) * cubeConstTwo d ^ s *
      ((∑ z ∈ crossingClusterVertices ω U,
        (((3 : ℝ) ^ (partitionCoarseData hd hP U hU).reachScale z) ^ (s * d)) ^
          (p / (p - s))) / V) ^ (1 - s / p)) *
    ((∑ z ∈ crossingClusterVertices ω U,
      gradNormIn (openGraph ω) (crossingClusterVertices ω U) u z ^ p) / V) ^ (s / p)

/-- **Armstrong and Dario, Lemma 6.4 (iii), for the partition into good cubes**, in every
dimension. -/
theorem cube_sum_abs_grad_boundaryInterpolation_rpow_div_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {B : Finset (Vertex d)}
    (hB : B ⊆ crossingClusterVertices ω U) (u : Vertex d → ℝ) {s p : ℝ} (hs : 1 ≤ s)
    (hsp : s < p) {V : ℝ} (hV : 0 < V) :
    (∑ x ∈ U.toIntegerCube.vertices, ∑ j : Fin d, (if x + unit j ∈ U.toIntegerCube.vertices then
        |boundaryInterpolation (partitionCoarseData hd hP U hU) B u (x + unit j) -
          boundaryInterpolation (partitionCoarseData hd hP U hU) B u x| ^ s else 0)) / V ≤
      cubeInterpolationBound hd hP U hU s p V u := by
  set P := partitionCoarseData hd hP U hU with hPdef
  have hs0 : 0 < s := by linarith
  set G : Vertex d → ℝ := fun z => gradNormIn (openGraph ω) (crossingClusterVertices ω U) u z
  have hG : ∀ z, 0 ≤ G z := fun z => gradNormIn_nonneg _ _ _ _
  have hGabs : ∀ z (t : ℝ), |G z| ^ t = G z ^ t := fun z t => by rw [abs_of_nonneg (hG z)]
  have hstep := sum_abs_grad_boundaryInterpolation_rpow_le P hB u hs
  have hL3 := partition_sum_gradNormIn_coarseAnchor_rpow_le hd hP hU u hs
  have hL2 := partition_sum_abs_sub_coarseAnchor_rpow_le hd hP hU u hs
  have hW3 := sum_mul_rpow_div_le (crossingClusterVertices ω U)
    (fun z => ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (s * d - 1))
    G (fun z _ => by positivity) hs0 hsp hV
  have hW2 := sum_mul_rpow_div_le (crossingClusterVertices ω U)
    (fun z => ((3 : ℝ) ^ P.reachScale z) ^ (s * d))
    G (fun z _ => by positivity) hs0 hsp hV
  simp only [hGabs] at hW3 hW2
  set C₃ : ℝ := cubeConstThree d ^ s
  set C₂ : ℝ := cubeConstTwo d ^ s
  set S₃ : ℝ := ∑ z ∈ crossingClusterVertices ω U,
    ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (s * d - 1) * G z ^ s
  set S₂ : ℝ := ∑ z ∈ crossingClusterVertices ω U,
    ((3 : ℝ) ^ P.reachScale z) ^ (s * d) * G z ^ s
  have hC₃ : 0 ≤ C₃ := Real.rpow_nonneg (cubeConstThree_nonneg d) _
  have hC₂ : 0 ≤ C₂ := Real.rpow_nonneg (cubeConstTwo_nonneg d) _
  have h3s : 0 ≤ (3 : ℝ) ^ (s - 1) := by positivity
  have hA : 0 ≤ (d : ℝ) * (2 : ℝ) ^ (s / 2) := by positivity
  have hL3' : ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen u) x ^ s ≤
      C₃ * S₃ := hL3
  have hL2' : ∑ z ∈ P.cluster, |u z - P.coarsen u z| ^ s ≤ C₂ * S₂ := hL2
  unfold cubeInterpolationBound
  calc (∑ x ∈ U.toIntegerCube.vertices, ∑ j : Fin d,
        (if x + unit j ∈ U.toIntegerCube.vertices then
          |boundaryInterpolation P B u (x + unit j) - boundaryInterpolation P B u x| ^ s
          else 0)) / V
      ≤ (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) * (C₃ * S₃) +
          2 * d * (C₂ * S₂)) / V := by
        refine div_le_div_of_nonneg_right (hstep.trans ?_) hV.le
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) h3s
        · exact mul_le_mul_of_nonneg_left hL3' hA
        · exact mul_le_mul_of_nonneg_left hL2' (by positivity)
    _ = (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) * C₃ * (S₃ / V) +
          2 * d * C₂ * (S₂ / V)) := by
        field_simp
    _ ≤ _ := by
        rw [mul_assoc ((3 : ℝ) ^ (s - 1))]
        refine mul_le_mul_of_nonneg_left ?_ h3s
        rw [add_mul]
        refine add_le_add ?_ ?_
        · rw [mul_assoc ((d : ℝ) * (2 : ℝ) ^ (s / 2) * C₃)]
          exact mul_le_mul_of_nonneg_left hW3 (by positivity)
        · rw [mul_assoc (2 * (d : ℝ) * C₂)]
          exact mul_le_mul_of_nonneg_left hW2 (by positivity)

/-- **Moments of the reach scale** by the moments of the partition sizes:
`Σ_{z ∈ C_*(U)} (3^{ρ(z)})^t ≤ 7^d Σ_{x ∈ U} (3^{s(x)})^{t+d}`. -/
theorem sum_three_pow_reachScale_partition_rpow_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (t : ℝ) :
    ∑ z ∈ crossingClusterVertices ω U,
        ((3 : ℝ) ^ (partitionCoarseData hd hP U hU).reachScale z) ^ t ≤
      7 ^ d * ∑ x ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ (t + d) := by
  set P := partitionCoarseData hd hP U hU
  set C := crossingClusterVertices ω U
  set g : Vertex d → ℝ := fun x => ((3 : ℝ) ^ (partitionCube ω x).scale) ^ t with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hpt : ∀ z ∈ C, ((3 : ℝ) ^ P.reachScale z) ^ t ≤
      ∑ x ∈ C, (if z ∈ P.region x then g x else 0) := by
    intro z hz
    have hne : (C.filter fun x => z ∈ P.region x).Nonempty :=
      ⟨z, Finset.mem_filter.2 ⟨hz, P.mem_region_self hz⟩⟩
    obtain ⟨x, hx, hxmax⟩ := Finset.exists_mem_eq_sup _ hne (fun x => (P.part x).scale)
    have e : P.reachScale z = (partitionCube ω x).scale := hxmax
    rw [e, ← Finset.sum_filter]
    exact Finset.single_le_sum (f := g) (fun y _ => hg0 y) hx
  have hcard : ∀ x ∈ C, ((C.filter fun z => z ∈ P.region x).card : ℝ) ≤
      7 ^ d * (3 : ℝ) ^ ((partitionCube ω x).scale * d) := by
    intro x _
    have hsub : C.filter (fun z => z ∈ P.region x) ⊆ ((partitionCube ω x).thicken 3).vertices :=
      fun z hz => partitionRegion_subset_thicken hP U x (Finset.mem_filter.1 hz).2
    have h := Finset.card_le_card hsub
    rw [TriadicCube.card_thicken] at h
    have h' : ((C.filter fun z => z ∈ P.region x).card : ℝ) ≤
        ((2 * 3 + 1) ^ d * 3 ^ ((partitionCube ω x).scale * d) : ℕ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hCU : C ⊆ U.toIntegerCube.vertices := Finset.filter_subset _ _
  calc ∑ z ∈ C, ((3 : ℝ) ^ P.reachScale z) ^ t
      ≤ ∑ z ∈ C, ∑ x ∈ C, (if z ∈ P.region x then g x else 0) := Finset.sum_le_sum hpt
    _ = ∑ x ∈ C, g x * ((C.filter fun z => z ∈ P.region x).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ C, g x * (7 ^ d * (3 : ℝ) ^ ((partitionCube ω x).scale * d)) :=
        Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hcard x hx) (hg0 x)
    _ = 7 ^ d * ∑ x ∈ C, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ (t + d) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hg, Real.rpow_add (by positivity), Real.rpow_natCast, ← pow_mul]
        ring
    _ ≤ 7 ^ d * ∑ x ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ (t + d) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hCU
          fun _ _ _ => by positivity) (by positivity)

end Rigidity.Dirichlet
