import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicExcessTwo
import PercolationClusterHomogenization.Proofs.Regularity.OrderOneOrigin
import PercolationClusterHomogenization.Proofs.Regularity.OrderZeroLiouville
import PercolationClusterHomogenization.Proofs.Partition.PartitionCube
import PercolationClusterHomogenization.Proofs.Lattice.ConfigurationExtension

/-!
# Armstrong–Dario, Lemma 7.1, in every dimension: statement and triadic cubes of the lattice

Armstrong and Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(arXiv:1609.09431v2), Lemma 7.1, approximate the coarsening `[u]_𝒫` of a function `u` harmonic on
the infinite cluster by `ā`-harmonic functions on the triadic cubes `□_m`, and the proof of
Lemma 7.3 turns this into the harmonic approximation hypothesis of Lemma 7.2 on balls. With the
homogenized problem discretized (the function `u_hom` of Theorem 1 being harmonic for the lattice
Laplacian), the approximating class on the balls of `ℤᵈ` is `latticeHarmonicClass 0`.

This file states the outcome in the form used by the iteration, for the partition `𝒫` into good
cubes of `Rigidity.Percolation.partitionCube` in every dimension `d`
(`CubeHarmonicApproximation d`): above a minimal scale `𝒳 ≤ O_s(θ)`, for `R ≥ A 𝒳` and `u`
harmonic on `𝒞_∞ ∩ B_R`, the coarsening `[u]_𝒫` (`partitionCoarse`, the value of `u` at the anchor
`z̄(𝒫(x))` of the partition cube) satisfies the hypothesis of Lemma 7.2 on the balls of the lattice
with `E = K R^{-1} inf_a ‖u - a‖`, where `‖·‖` is the normalized norm
`r^{-d/2} ‖·‖_{L²(𝒞_∞ ∩ B_r)}` (`clusterBallVolumeL2`), `u` is close to `[u]_𝒫` on the cluster
balls (the `L²` form of (7.8)), and the normalized norms of `[u]_𝒫 - a` on the balls of the
lattice are bounded by those of `u - a` on larger cluster balls. The planar form is
`PlanarHarmonicApproximationTwo`, for the partition into meshed cubes.

It also introduces the normalized `ℓ²` norms on the cubes `□_m = ℤᵈ ∩ (-3^m/2, 3^m/2)ᵈ`
(`cubeL2`), the oscillation `inf_a ‖f - a‖_{L̲²(□_m)}` (`cubeOsc`) and the distance to the
lattice harmonic functions on `□_m` (`cubeHarmonicDist`), and compares the normalized norms on
cubes and on the balls of the lattice: a ball inside a cube (`componentBallL2_le_cubeL2`) and a
cube inside a ball (`cubeL2_le_componentBallL2`), with the factors `(3^m / 3^j)^{d/2}` and
`((2 s + 3) / 3^j)^{d/2}`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

variable {d : ℕ}

/-- The coarsening `[u]_𝒫` of a function on an open component: the value of `u`, extended by `0`
off the component, at the anchor `z̄(𝒫(y))` of the partition cube. -/
noncomputable def partitionCoarse {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ) :
    Vertex d → ℝ :=
  fun y => Rigidity.Section3.extend C u (partitionAnchor ω y)

/-- The conclusion of Armstrong–Dario, Lemma 7.1, for one cluster `C` above the scale `X`, in the
form used in the proof of Lemma 7.3: for `R ≥ A X` and `u` harmonic on `C ∩ B_R`, the coarsening
`[u]_𝒫` satisfies on the balls of `ℤᵈ` the harmonic approximation hypothesis of Lemma 7.2 with
the lattice harmonic functions and `E = K R^{-1} inf_a ‖u - a‖_{R}`, `‖·‖_r` being
`r^{-d/2} ‖·‖_{L²(C ∩ B_r)}`; for `r ∈ [X, R / A]`,
`‖u - [u]_𝒫‖_r ≤ K r^{-1} inf_a ‖u - a‖_{A r}` (the `L²` form of (7.8)); and, for every `a ∈ ℝ`,
`‖[u]_𝒫 - a‖_{L̲²(B_r)} ≤ K ‖u - a‖_{A r}` on the balls of `ℤᵈ` (the bound of Step 2 of the proof
of Lemma 7.1 with `w` constant). -/
def CubeHarmonicApproximationAt [NeZero d] {ω : Configuration d} (C : OpenComponent ω)
    (A α K X : ℝ) : Prop :=
  ∀ R : ℝ, A * X ≤ R → ∀ u : C → ℝ, IsHarmonicInBall C R u →
    HarmonicApproximation (componentBallSeminorm (latticeComponent d) 0)
        (latticeHarmonicClass 0) (clusterConstants (latticeComponent d)) A α X R
        (K / R * ⨅ a : ℝ, clusterBallVolumeL2 C R (u - fun _ => a))
        (fun x => partitionCoarse C u x.val) ∧
      (∀ r : ℝ, X ≤ r → r ≤ R / A →
        clusterBallVolumeL2 C r (u - fun x => partitionCoarse C u x.val) ≤
          K / r * ⨅ a : ℝ, clusterBallVolumeL2 C (A * r) (u - fun _ => a)) ∧
      ∀ r : ℝ, X ≤ r → r ≤ R / A → ∀ a : ℝ,
        componentBallL2 (latticeComponent d) 0 r (fun x => partitionCoarse C u x.val - a) ≤
          K * clusterBallVolumeL2 C (A * r) (u - fun _ => a)

/-- **Armstrong–Dario, Lemma 7.1, in dimension `d`**, in the form used in the proof of Lemma 7.3
(`CubeHarmonicApproximationAt`), almost surely on the infinite cluster above a minimal scale
`𝒳 ≤ O_s(θ)`. -/
def CubeHarmonicApproximation (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ A α K : ℝ), 0 < s ∧ 0 < θ ∧ 2 ≤ A ∧ 0 < α ∧ 0 ≤ K ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 1 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        CubeHarmonicApproximationAt (uniqueInfiniteComponent h) A α K (X ω)

/-! ### Triadic cubes of the lattice -/

/-- The normalized `ℓ²` norm `‖g‖_{L̲²(□_m)} = (3^{-dm} ∑_{□_m} g²)^{1/2}` on the triadic cube
`□_m = ℤᵈ ∩ (-3^m/2, 3^m/2)ᵈ`. -/
noncomputable def cubeL2 (d m : ℕ) (g : Vertex d → ℝ) : ℝ :=
  Real.sqrt ((∑ y ∈ triadicCubeFinset d m 0, g y ^ 2) / ((3 : ℝ) ^ m) ^ d)

/-- The oscillation `inf_{a ∈ ℝ} ‖f - a‖_{L̲²(□_m)}`. -/
noncomputable def cubeOsc (d m : ℕ) (f : Vertex d → ℝ) : ℝ :=
  ⨅ a : ℝ, cubeL2 d m (fun y => f y - a)

/-- The functions on `ℤᵈ` harmonic for the lattice Laplacian at every point of `□_m`. -/
def cubeLatticeHarmonic (d m : ℕ) : Set (Vertex d → ℝ) :=
  {F | ∀ y ∈ triadicCubeFinset d m 0, latticeLaplacian F y = 0}

/-- The distance `inf_{w ∈ Ā(□_m)} ‖f - w‖_{L̲²(□_m)}` to the lattice harmonic functions. -/
noncomputable def cubeHarmonicDist (d m : ℕ) (f : Vertex d → ℝ) : ℝ :=
  ⨅ F : cubeLatticeHarmonic d m, cubeL2 d m (f - F)

theorem cubeL2_nonneg (m : ℕ) (g : Vertex d → ℝ) : 0 ≤ cubeL2 d m g :=
  Real.sqrt_nonneg _

theorem zero_mem_cubeLatticeHarmonic (m : ℕ) : (0 : Vertex d → ℝ) ∈ cubeLatticeHarmonic d m :=
  fun _ _ => by simp [latticeLaplacian]

theorem cubeOsc_le (m : ℕ) (f : Vertex d → ℝ) (a : ℝ) :
    cubeOsc d m f ≤ cubeL2 d m (fun y => f y - a) :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ cubeL2_nonneg _ _⟩ a

theorem cubeOsc_nonneg (m : ℕ) (f : Vertex d → ℝ) : 0 ≤ cubeOsc d m f :=
  le_ciInf fun _ => cubeL2_nonneg _ _

theorem cubeHarmonicDist_nonneg (m : ℕ) (f : Vertex d → ℝ) : 0 ≤ cubeHarmonicDist d m f := by
  haveI : Nonempty (cubeLatticeHarmonic d m) := ⟨⟨0, zero_mem_cubeLatticeHarmonic m⟩⟩
  exact le_ciInf fun _ => cubeL2_nonneg _ _

theorem sum_sq_cube_eq (m : ℕ) (g : Vertex d → ℝ) :
    ∑ y ∈ triadicCubeFinset d m 0, g y ^ 2 = ((3 : ℝ) ^ m) ^ d * cubeL2 d m g ^ 2 := by
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ m) ^ d := by positivity
  rw [cubeL2, Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) h3.le)]
  field_simp

/-- The number of points of `□_m` as a real number. -/
theorem card_triadicCubeFinset_real (m : ℕ) :
    ((triadicCubeFinset d m 0).card : ℝ) = ((3 : ℝ) ^ m) ^ d := by
  rw [card_triadicCubeFinset, ← pow_mul, mul_comm]
  push_cast
  ring

theorem mem_cubeFinset_iff (m : ℕ) (y : Vertex d) :
    y ∈ triadicCubeFinset d m 0 ↔ ∀ i, |(y i : ℝ)| < 3 ^ m / 2 := by
  rw [← Finset.mem_coe, coe_triadicCubeFinset]
  simp [triadicCube]

/-- The points of `ℤᵈ` at distance less than `3^m / 2` from the origin lie in `□_m`. -/
theorem mem_cubeFinset_of_dist_lt {m : ℕ} {y : Vertex d}
    (hy : dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) <
      3 ^ m / 2) : y ∈ triadicCubeFinset d m 0 := by
  rw [mem_cubeFinset_iff]
  intro i
  have h := abs_sub_le_dist_latticeEuclideanEmbedding y 0 i
  simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h
  exact h.trans_lt hy

/-- The points of `□_m` lie at distance at most `√d 3^m / 2` from the origin. -/
theorem dist_le_of_mem_cubeFinset {m : ℕ} {y : Vertex d} (hy : y ∈ triadicCubeFinset d m 0) :
    dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) ≤
      Real.sqrt d * (3 ^ m / 2) := by
  rw [mem_cubeFinset_iff] at hy
  exact dist_latticeEuclideanEmbedding_le (by positivity) fun i => by
    show |(y i : ℝ) - ((0 : Vertex d) i : ℝ)| ≤ 3 ^ m / 2
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
    exact (hy i).le

/-- `√d ≤ 3^d`. -/
theorem sqrt_le_three_pow (d : ℕ) : Real.sqrt d ≤ 3 ^ d := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : (d : ℝ) < 3 ^ d := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
  have h2 : (3 : ℝ) ^ d ≤ (3 ^ d) ^ 2 := by
    rw [sq]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  linarith

/-- `√(x^d) ≤ x^d` for `x ≥ 1`. -/
theorem sqrt_pow_le_pow {x : ℝ} (hx : 1 ≤ x) (d : ℕ) : Real.sqrt (x ^ d) ≤ x ^ d := by
  have h1 : 1 ≤ x ^ d := one_le_pow₀ hx
  rw [Real.sqrt_le_left (by positivity), sq]
  exact le_mul_of_one_le_left (by positivity) h1

/-- Square sums over a lattice ball are sums over its points in `ℤᵈ`. -/
theorem sum_latticeBall_eq' [NeZero d] (r : ℝ) (g : Vertex d → ℝ) :
    ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 r, g x.val ^ 2 =
      ∑ y ∈ (componentEuclideanBall (latticeComponent d) 0 r).image Subtype.val, g y ^ 2 :=
  (sum_image (f := fun y => g y ^ 2) fun _ _ _ _ h => Subtype.val_injective h).symm

theorem mem_image_latticeBall' [NeZero d] {r : ℝ} {y : Vertex d} :
    y ∈ (componentEuclideanBall (latticeComponent d) 0 r).image Subtype.val ↔
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r := by
  rw [mem_image_componentEuclideanBall]
  exact ⟨fun h => h.2, fun h => ⟨mem_latticeComponent_supp y, h⟩⟩

/-- A lattice ball containing `□_j` has at least `3^{dj}` points. -/
theorem le_card_latticeBall_of_subset [NeZero d] {r : ℝ} {j : ℕ}
    (hj : ∀ y ∈ triadicCubeFinset d j 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r) :
    ((3 : ℝ) ^ j) ^ d ≤ (componentEuclideanBall (latticeComponent d) 0 r).card := by
  classical
  have hsub : triadicCubeFinset d j 0 ⊆
      (componentEuclideanBall (latticeComponent d) 0 r).image Subtype.val := fun y hy =>
    mem_image_latticeBall'.2 (hj y hy)
  have h1 := card_le_card hsub
  have h2 := card_image_le (s := componentEuclideanBall (latticeComponent d) 0 r)
    (f := Subtype.val)
  rw [← card_triadicCubeFinset_real]
  exact_mod_cast h1.trans h2

/-- **A ball inside a cube.** If `B_r ⊆ □_m` and `□_j ⊆ B_r`, the normalized norm on `B_r` is at
most `(3^m / 3^j)^{d/2}` times the one on `□_m`. -/
theorem componentBallL2_le_cubeL2 [NeZero d] {r : ℝ} {m j : ℕ}
    (hsub : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r →
        y ∈ triadicCubeFinset d m 0)
    (hj : ∀ y ∈ triadicCubeFinset d j 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r)
    (g : Vertex d → ℝ) :
    componentBallL2 (latticeComponent d) 0 r (fun x => g x.val) ≤
      Real.sqrt (((3 : ℝ) ^ m / 3 ^ j) ^ d) * cubeL2 d m g := by
  have hc := le_card_latticeBall_of_subset hj
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ j) ^ d := by positivity
  have hcpos : (0 : ℝ) < (componentEuclideanBall (latticeComponent d) 0 r).card :=
    h3.trans_le hc
  have hsum : ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 r, g x.val ^ 2 ≤
      ∑ y ∈ triadicCubeFinset d m 0, g y ^ 2 := by
    rw [sum_latticeBall_eq']
    exact sum_le_sum_of_subset_of_nonneg (fun y hy => hsub y (mem_image_latticeBall'.1 hy))
      fun _ _ _ => sq_nonneg _
  rw [sum_sq_cube_eq] at hsum
  have hK : 0 ≤ Real.sqrt (((3 : ℝ) ^ m / 3 ^ j) ^ d) * cubeL2 d m g :=
    mul_nonneg (Real.sqrt_nonneg _) (cubeL2_nonneg _ _)
  rw [componentBallL2, Real.sqrt_le_left hK, div_le_iff₀ hcpos, mul_pow,
    Real.sq_sqrt (by positivity)]
  calc ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 r, g x.val ^ 2
      ≤ ((3 : ℝ) ^ m) ^ d * cubeL2 d m g ^ 2 := hsum
    _ = ((3 : ℝ) ^ m / 3 ^ j) ^ d * cubeL2 d m g ^ 2 * ((3 : ℝ) ^ j) ^ d := by
        rw [div_pow]; field_simp
    _ ≤ ((3 : ℝ) ^ m / 3 ^ j) ^ d * cubeL2 d m g ^ 2 *
          (componentEuclideanBall (latticeComponent d) 0 r).card :=
        mul_le_mul_of_nonneg_left hc (by positivity)

/-- **A cube inside a ball.** If `□_j ⊆ B_s`, the normalized norm on `□_j` is at most
`((2 s + 3) / 3^j)^{d/2}` times the one on the lattice ball `B_s`. -/
theorem cubeL2_le_componentBallL2 [NeZero d] {s : ℝ} {j : ℕ} (hs : 0 ≤ s)
    (hj : ∀ y ∈ triadicCubeFinset d j 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < s)
    (g : Vertex d → ℝ) :
    cubeL2 d j g ≤ Real.sqrt (((2 * s + 3) / 3 ^ j) ^ d) *
      componentBallL2 (latticeComponent d) 0 s (fun x => g x.val) := by
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ j) ^ d := by positivity
  have hsum : ∑ y ∈ triadicCubeFinset d j 0, g y ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (latticeComponent d) 0 s, g x.val ^ 2 := by
    rw [sum_latticeBall_eq']
    exact sum_le_sum_of_subset_of_nonneg (fun y hy => mem_image_latticeBall'.2 (hj y hy))
      fun _ _ _ => sq_nonneg _
  rw [sum_sq_cube_eq, sum_sq_eq_card_mul_componentBallL2_sq] at hsum
  have hcard := card_componentEuclideanBall_le (latticeComponent d) 0 hs
  set N := componentBallL2 (latticeComponent d) 0 s (fun x => g x.val)
  have hK : 0 ≤ Real.sqrt (((2 * s + 3) / 3 ^ j) ^ d) * N :=
    mul_nonneg (Real.sqrt_nonneg _) (componentBallL2_nonneg _ _ _ _)
  rw [cubeL2, Real.sqrt_le_left hK, div_le_iff₀ h3, mul_pow, Real.sq_sqrt (by positivity)]
  calc ∑ y ∈ triadicCubeFinset d j 0, g y ^ 2 ≤ ((3 : ℝ) ^ j) ^ d * cubeL2 d j g ^ 2 := by
        rw [sum_sq_cube_eq]
    _ ≤ ((componentEuclideanBall (latticeComponent d) 0 s).card : ℝ) * N ^ 2 := hsum
    _ ≤ (2 * s + 3) ^ d * N ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = ((2 * s + 3) / 3 ^ j) ^ d * N ^ 2 * ((3 : ℝ) ^ j) ^ d := by
        rw [div_pow]; field_simp

end Rigidity.Proofs.Regularity
