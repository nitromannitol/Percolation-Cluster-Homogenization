import PercolationClusterHomogenization.Proofs.Regularity.GeneralClusterInclusions
import PercolationClusterHomogenization.Proofs.Regularity.ClusterCubeDensityOfConcentration
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityConcentration
import PercolationClusterHomogenization.Proofs.Percolation.SupercriticalUniqueness

/-!
# Armstrong–Dario, Lemma 7.1, in every dimension, from the estimates on cubes, almost surely

`cubeHarmonicApproximation_of_cubeEstimates` proves `CubeHarmonicApproximation d` from two
statements on the partition into good cubes, taken as hypotheses:

* `CubeEstimatesAS d p`: above a minimal scale `𝒳 ≤ O_s(θ)`, every `u` harmonic on `𝒞_∞ ∩ B_R`
  satisfies the estimates (7.7), (7.8) and the bound of Step 2 of the proof of Lemma 7.1 on the
  cubes `□_j`, `3^j ≥ 𝒳`, `L 3^{j + 3} ≤ R` (`CubeEstimates`);
* `CubePartitionSizeScale d p`: above a minimal scale `𝓜 ≤ O_s(θ)`, the partition cubes of the
  vertices of `□_m` have scale at most `m - 2` (from the second bound of (2.13) of the source,
  Proposition 2.4).

The density of the infinite cluster in triadic cubes (Dario–Gu, Proposition A.1, proved) gives a
vertex of `𝒞_∞` in every large cube, so that the crossing clusters of the cubes lie in `𝒞_∞`
(`mem_supp_of_mem_crossingClusterVertices`), and the bound on the partition cubes gives
`𝒞_∞ ∩ □_m ⊆ C_*(□_{m + 1})` (`mem_crossingClusterVertices_succ`) and the resolution of the cubes.
The planar form is `planarHarmonicApproximationTwo_of_squareEstimates`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

variable {d : ℕ}

/-- The partition cubes of the vertices of `□_m` have scale at most `m - 2` above a minimal scale
`𝓜 ≤ O_s(θ)`. -/
def CubePartitionSizeScale (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s θ : ℝ, 0 < s ∧ 0 < θ ∧
    ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, PartitionEvent ω ∧ ∀ m : ℕ, M ω ≤ 3 ^ m →
        ∀ x ∈ triadicCubeFinset d m 0, (partitionCube ω x).scale + 2 ≤ m

/-- The estimates of the proof of Armstrong–Dario, Lemma 7.1, on the cubes `□_j` above a minimal
scale `𝒳 ≤ O_s(θ)`, for the functions harmonic on the balls of the infinite cluster. -/
def CubeEstimatesAS (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s θ L C₁ K₂ K₃ α : ℝ, 0 < s ∧ 0 < θ ∧ 1 ≤ L ∧ Real.sqrt d ≤ L ∧ 0 ≤ C₁ ∧ 0 ≤ K₂ ∧
    0 ≤ K₃ ∧ 0 < α ∧
    ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
            CubeEstimates (uniqueInfiniteComponent h) C₁ K₂ K₃ α j u

/-- A vertex of a cluster in a large cube, from the density in cubes. -/
theorem exists_mem_cubeFinset_of_clusterCubeDensity (hd : 0 < d) {ω : Configuration d}
    (C : OpenComponent ω) {ℓ κ : ℝ} (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 (Real.sqrt d) ℓ κ) {j : ℕ} (hj : ℓ ≤ 3 ^ j) :
    ∃ x : C, x.val ∈ triadicCubeFinset d j 0 := by
  have hin : ∀ y ∈ triadicCube d j 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) <
        Real.sqrt d * 3 ^ j := by
    intro y hy
    rw [← coe_triadicCubeFinset] at hy
    exact dist_lt_of_mem_cubeFinset_of_le hd le_rfl y hy
  have h := hcube j 0 hj hin
  have hpos : 0 < (clusterCubePoints C 0 (Real.sqrt d * 3 ^ j) j 0).card := by
    have : (0 : ℝ) < (clusterCubePoints C 0 (Real.sqrt d * 3 ^ j) j 0).card :=
      lt_of_lt_of_le (by positivity) h
    exact_mod_cast this
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  refine ⟨x, ?_⟩
  simp only [clusterCubePoints, mem_filter] at hx
  rw [mem_cubeFinset_iff]
  intro i
  simpa using hx.2 i

set_option maxHeartbeats 400000 in
/-- **Armstrong–Dario, Lemma 7.1, in dimension `d`** (`CubeHarmonicApproximation d`), from the
estimates on cubes and the bound on the scales of the partition cubes. -/
theorem cubeHarmonicApproximation_of_cubeEstimates [NeZero d] (hd : 2 ≤ d)
    (hS : ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      CubeEstimatesAS d p)
    (hM : ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      CubePartitionSizeScale d p) :
    CubeHarmonicApproximation d := by
  have hd0 : 0 < d := by omega
  intro p hpc hp1
  obtain ⟨s₁, θ₁, L, C₁, K₂, K₃, α, hs₁, hθ₁, hL, hLd, hC₁, hK₂, hK₃, hα, X, hXm, hX0, hXos,
    hSae⟩ := hS p hpc hp1
  obtain ⟨s₂, θ₂, hs₂, hθ₂, M, hMm, hM0, hMos, hMae⟩ := hM p hpc hp1
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₃, θ₃, hs₃, hθ₃, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (Real.sqrt d)
  obtain ⟨Md, hMdm, hMd0, hMdos, hMdae⟩ := hcube 0
  set A := 4374 * L with hAdef
  set K := cubeApproxConst d L K₂ K₃ with hKdef
  set c := cubeScale d (4374 * L) L C₁ K₂ α with hcdef
  have hc1 : 1 ≤ c := by
    rw [hcdef]; unfold cubeScale
    exact ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hc0 : 0 < c := by linarith
  -- the minimal scale
  set s := min s₁ (min s₂ s₃) with hsdef
  have hs : 0 < s := lt_min hs₁ (lt_min hs₂ hs₃)
  have hss₁ : s ≤ s₁ := by rw [hsdef]; exact min_le_left _ _
  have hss₂ : s ≤ s₂ := by rw [hsdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hss₃ : s ≤ s₃ := by rw [hsdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have h1 := IsOsBond.mono_exponent hs hss₁ hXm hXos
  have h2 := IsOsBond.mono_exponent hs hss₂ hMm hMos
  have h3 := IsOsBond.mono_exponent hs hss₃ hMdm hMdos
  have h23 := IsOsBond.max hs (by positivity) (by positivity) hMm hMdm h2 h3
  have h123 := IsOsBond.max hs (by positivity) (by positivity) hXm (hMm.max hMdm) h1 h23
  have hone := isOsBond_const (p := p) (d := d) one_pos hs
  have h1234 := IsOsBond.max hs (by positivity) (by positivity)
    (hXm.max (hMm.max hMdm)) measurable_const h123 hone
  have hcc := isOsBond_const (p := p) (d := d) hc0 hs
  have h12345 := IsOsBond.max hs (by positivity) (by positivity)
    ((hXm.max (hMm.max hMdm)).max measurable_const) measurable_const h1234 hcc
  set Y : Configuration d → ℝ := fun ω => max (max (max (X ω) (max (M ω) (Md ω))) 1) c
    with hYdef
  have hYm : Measurable Y := ((hXm.max (hMm.max hMdm)).max measurable_const).max measurable_const
  have hY1 : ∀ ω, 1 ≤ Y ω := fun ω => (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨θY, hθY, hYos⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond d p Y s θ := ⟨_, by positivity, h12345⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]; unfold cubeApproxConst
    exact (Real.sqrt_nonneg _).trans (le_max_left _ _)
  refine ⟨s, θY, A, α / 2, K, hs, hθY, by rw [hAdef]; linarith, by positivity, hK0, Y, hYm, hY1,
    hYos, ?_⟩
  filter_upwards [hSae, hMae, hMdae] with ω hω₁ ⟨hP, hω₂⟩ hω₃ h
  set C := uniqueInfiniteComponent h with hCdef
  have hinf : C.supp.Infinite := uniqueInfiniteComponent_infinite h
  set X₀ := max (X ω) (max (M ω) (Md ω)) with hX₀def
  have hXX₀ : X ω ≤ X₀ := le_max_left _ _
  have hMX₀ : M ω ≤ X₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hMdX₀ : Md ω ≤ X₀ := (le_max_right _ _).trans (le_max_right _ _)
  set X₁ := max X₀ 1 with hX₁def
  have hX₁1 : 1 ≤ X₁ := le_max_right _ _
  have hX₀X₁ : X₀ ≤ X₁ := le_max_left _ _
  have hκ : 0 < theta d p / 2 := by positivity
  have hsub : ∀ j : ℕ, X₁ ≤ 3 ^ j → ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩, x ∈ C.supp := by
    intro j hj x hx
    have hsize := hω₂ j (hMX₀.trans (hX₀X₁.trans hj))
    have hres : PartitionResolved ω ⟨j, 0⟩ := by
      intro z hz
      have hz' : z ∈ triadicCubeFinset d j 0 := mem_cubeFinset_iff_vertices.2 hz
      have := hsize z hz'
      show (partitionCube ω z).scale ≤ j
      omega
    obtain ⟨x₀, hx₀⟩ := exists_mem_cubeFinset_of_clusterCubeDensity hd0 C hκ (hω₃ h)
      (hMdX₀.trans (hX₀X₁.trans hj))
    exact mem_supp_of_mem_crossingClusterVertices hd0 hP hres C hinf
      (mem_cubeFinset_iff_vertices.1 hx₀) x₀.2 hx
  have hgeo : ∀ (m : ℕ) (r : ℝ), X₁ ≤ r → 2 * r ≤ 3 ^ m → ∀ x : C,
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding (0 : Vertex d)) < r →
        x.val ∈ crossingClusterVertices ω ⟨m + 1, 0⟩ := by
    intro m r hr hm x hx
    have hsize := hω₂ m (by linarith)
    have hxm : x.val ∈ triadicCubeFinset d m 0 := mem_cubeFinset_of_dist_lt (by linarith)
    exact mem_crossingClusterVertices_succ hd0 hP C hinf hsize hxm x.2
  have hest : ∀ R : ℝ, ∀ u : C → ℝ, IsHarmonicInBall C R u → ∀ j : ℕ, X₁ ≤ 3 ^ j →
      L * 3 ^ (j + 3) ≤ R → CubeEstimates C C₁ K₂ K₃ α j u :=
    fun R u hu j hj hjR => hω₁ h R u hu j (hXX₀.trans (hX₀X₁.trans hj)) hjR
  exact cubeHarmonicApproximationAt_of_cubeEstimates hL hLd hC₁ hK₂ hK₃ hα C hX₁1 hsub hgeo hest

end Rigidity.Proofs.Regularity
