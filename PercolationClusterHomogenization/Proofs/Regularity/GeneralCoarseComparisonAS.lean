import PercolationClusterHomogenization.Proofs.Regularity.GeneralCoarseComparison

/-!
# The comparison (7.8) on triadic cubes, almost surely above a minimal scale

`cubeCoarseComparisonAS_holds` proves the comparison (7.8) of the proof of Armstrong–Dario,
Lemma 7.1 (arXiv:1609.09431v2), in `L²` on the triadic cubes of `ℤᵈ`, `d ≥ 2`, almost surely above
a minimal scale `𝒳 ≤ O_s(θ)`, from the minimal scales of Proposition 2.4
(`cubeRegularityScales_holds`, `cubePartitionSizeScale_holds`), the density of the infinite cluster
and the Meyers estimate on the reverse Hölder cells (`meyers_rh_uniform`). The ingredients at one
scale are `coarseComparison_on_cube`; here they are checked above the minimal scale:

* the cells of the reverse Hölder partition inside `□_{j+1}` have scale at most `j + 1` (the bound
  `3^{s(x)} ≤ 3^{m/2}`) and satisfy the moment bound used by the Meyers estimate;
* the reach scales of the partition are bounded by its reach
  (`three_pow_reachScale_le_partitionReach`), whose moments are bounded above the minimal scale
  (`sum_reachScale_rpow_le_of_reach`);
* the cubes are resolved and their crossing clusters lie in the infinite cluster
  (`GeneralClusterInclusions`).

The planar form is `planarCoarseComparisonTwo_of_minimalScales`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster Rigidity.Proofs.Cluster.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ}

/-- The comparison (7.8) of the proof of Armstrong–Dario, Lemma 7.1, in `L²` on the cubes `□_j`
of `ℤᵈ`, almost surely on the infinite cluster above a minimal scale `𝒳 ≤ O_s(θ)`, for the
functions harmonic on `𝒞_∞ ∩ B_R`, `√d 3^{j+3} ≤ R`. -/
def CubeCoarseComparisonAS (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s θ K₂ : ℝ, 0 < s ∧ 0 < θ ∧ 0 ≤ K₂ ∧
    ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → Real.sqrt d * 3 ^ (j + 3) ≤ R →
            clusterCubeL2 ω j (fun x => Rigidity.Section3.extend (uniqueInfiniteComponent h) u x -
                partitionCoarse (uniqueInfiniteComponent h) u x) ≤
              K₂ / 3 ^ j * clusterCubeOsc (uniqueInfiniteComponent h) u (j + 3)

set_option maxHeartbeats 400000 in
/-- **The comparison (7.8) on triadic cubes almost surely**, for `p_c(d) < p < 1`, `d ≥ 2`. -/
theorem cubeCoarseComparisonAS_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : CubeCoarseComparisonAS d p := by
  have hd0 : 0 < d := by omega
  obtain ⟨s₃, θ₃, hs₃, hθ₃, M₃, hM₃m, hM₃0, hM₃os, hM₃ae⟩ := cubePartitionSizeScale_holds hd hpc
  obtain ⟨A₀, sc, hcellae, hmoms⟩ := cubeRegularityScales_holds hd hpc
  obtain ⟨ε, hε, t, ht, hMK⟩ := meyers_rh_uniform (d := d) (by omega) A₀
  have hq : 1 < 1 + ε / 2 := by linarith
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁ae⟩ :=
    hmoms t ht (1 / 2) (by norm_num)
  obtain ⟨CM, hCM, hMey⟩ := hMK K₁ hK₁
  have hpq := Real.HolderConjugate.conjExponent hq
  have hτ : 0 < (2 : ℝ) * d * Real.conjExponent (1 + ε / 2) := by
    have := hpq.symm.pos
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    positivity
  obtain ⟨Kr, r₂, θ₂, hKr, hr₂, hθ₂, M₂, hM₂m, hM₂0, hM₂os, hM₂ae⟩ :=
    hmoms ((2 : ℝ) * d * Real.conjExponent (1 + ε / 2)) hτ (1 / 2) (by norm_num)
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (Real.sqrt d)
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  -- the minimal scale
  set r := min (min r₁ r₂) (min s₃ s₄) with hrdef
  have hr : 0 < r := lt_min (lt_min hr₁ hr₂) (lt_min hs₃ hs₄)
  have hr1 : r ≤ r₁ := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ r₂ := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ s₃ := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr4 : r ≤ s₄ := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have h1 := IsOsBond.mono_exponent hr hr1 hM₁m hM₁os
  have h2 := IsOsBond.mono_exponent hr hr2 hM₂m hM₂os
  have h3 := IsOsBond.mono_exponent hr hr3 hM₃m hM₃os
  have h4 := IsOsBond.mono_exponent hr hr4 hM₄m hM₄os
  have h12 := IsOsBond.max hr (by positivity) (by positivity) hM₁m hM₂m h1 h2
  have h34 := IsOsBond.max hr (by positivity) (by positivity) hM₃m hM₄m h3 h4
  have h1234 := IsOsBond.max hr (by positivity) (by positivity) (hM₁m.max hM₂m)
    (hM₃m.max hM₄m) h12 h34
  obtain ⟨θX, hθX, hXos⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond d p
      (fun ω => max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) r θ := ⟨_, by positivity, h1234⟩
  have hK₂0 : 0 ≤ partitionCoarseConst d * Real.sqrt (8 * d * 9 ^ d) *
      Real.sqrt (CM ^ (1 / (1 + ε / 2)) * Kr ^ (1 / Real.conjExponent (1 + ε / 2))) := by
    have := partitionCoarseConst_nonneg d; positivity
  refine ⟨r, θX, _, hr, hθX, hK₂0, _, (hM₁m.max hM₂m).max (hM₃m.max hM₄m),
    fun ω => (hM₁0 ω).trans ((le_max_left _ _).trans (le_max_left _ _)), hXos, ?_⟩
  filter_upwards [hcellae, hM₁ae, hM₂ae, hM₃ae, hM₄ae] with
    ω hcells hω₁ hω₂ hω₃' hω₄ h
  obtain ⟨hP, hω₃⟩ := hω₃'
  obtain ⟨hcell, hnb, hrh⟩ := hcells
  set C := uniqueInfiniteComponent h with hCdef
  intro R u hu j hj hjR
  have hinf := uniqueInfiniteComponent_infinite h
  have hle : ∀ m, j ≤ m → (3 : ℝ) ^ j ≤ 3 ^ m := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hj1 : M₁ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_left _ _)).trans hj
  have hj2 : M₂ ω ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_left _ _)).trans hj
  have hj3 : M₃ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_right _ _)).trans hj
  have hj4 : M₄ ω ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_right _ _)).trans hj
  have hres : ∀ m, j ≤ m → PartitionResolved ω ⟨m, 0⟩ := by
    intro m hm z hz
    have hz' : z ∈ triadicCubeFinset d m 0 := mem_cubeFinset_iff_vertices.2 hz
    have := hω₃ m (hj3.trans (hle m hm)) z hz'
    show (partitionCube ω z).scale ≤ m
    omega
  have hκ : 0 < theta d p / 2 := by positivity
  have hsub : ∀ m, j ≤ m → ∀ x ∈ crossingClusterVertices ω ⟨m, 0⟩, x ∈ C.supp := by
    intro m hm x hx
    obtain ⟨x₀, hx₀⟩ := exists_mem_cubeFinset_of_clusterCubeDensity hd0 C hκ (hω₄ h)
      (hj4.trans (hle m hm))
    exact mem_supp_of_mem_crossingClusterVertices hd0 hP (hres m hm) C hinf
      (mem_cubeFinset_iff_vertices.1 hx₀) x₀.2 hx
  have hsucc : ∀ m, j ≤ m → ∀ x ∈ triadicCubeFinset d m 0, x ∈ C.supp →
      x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩ := fun m hm x hx hxC =>
    mem_crossingClusterVertices_succ hd0 hP C hinf (hω₃ m (hj3.trans (hle m hm))) hx hxC
  have h02 : crossingClusterVertices ω ⟨j, 0⟩ ⊆ crossingClusterVertices ω ⟨j + 2, 0⟩ := by
    intro x hx
    have hxC := hsub j le_rfl x hx
    have hx1 : x ∈ triadicCubeFinset d (j + 1) 0 :=
      mem_cubeFinset_mono (by omega) (mem_cubeFinset_of_mem_crossingClusterVertices hx)
    exact hsucc (j + 1) (by omega) x hx1 hxC
  have hharm := harm_on_cube_of_isHarmonicInBall hd0 hu hjR
  -- the Meyers estimate
  have hω₁' := hω₁ (j + 1) (hj1.trans (hle (j + 1) (by omega)))
  have hsize : ∀ z ∈ cube (j + 1) (0 : Vertex d), sc ω z ≤ j + 1 := fun z hz => by
    have := two_mul_le_of_three_pow_le_rpow_half' (hω₁'.2.1 z hz)
    omega
  have hmemenl : ∀ b ∈ enl 1 j (0 : Vertex d), b ∈ triadicCubeFinset d (j + 1) 0 := by
    intro b hb
    rw [enl_one_zero_eq_cube_succ] at hb
    exact mem_cubeFinset_of_mem_cube_zero hb
  have hMeyj := hMey ω (crossingClusterVertices ω ⟨j + 2, 0⟩) (Rigidity.Section3.extend C u) j 0
    (sc ω) (fun a ha b hab hb => by
      have hbV : b ∈ (⟨j + 2, 0⟩ : TriadicCube d).vertices :=
        mem_cubeFinset_iff_vertices.1 (mem_cubeFinset_mono (by omega) (hmemenl b hb))
      exact mem_crossingClusterVertices.2
        (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 ha) hbV hab))
    (fun a ha hae _ => by
      have haC := hsub (j + 2) (by omega) a ha
      rw [openLaplacian_extend_eq_componentLaplacian C u haC]
      exact hharm a haC (mem_cubeFinset_mono (by omega) (hmemenl a hae)))
    hcell hnb (fun z hz => by
      rw [enl_one_zero_eq_cube_succ] at hz ⊢
      intro w hw'
      have hle' := hsize z hz
      have h1 : w ∈ cube (j + 1) z := cube_mono hle' z hw'
      rw [cube_eq_of_mem hz] at h1
      exact h1)
    (fun k y hk _ => hrh k y hk) (hω₁ j hj1).1
  -- the moments of the reach scales
  have hω₂j := hω₂ j hj2
  have hfin : ∀ x ∈ cube j (0 : Vertex d), partitionReach ω x ≠ ⊤ := fun x hx =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hω₂j.2.2.2 x hx)
  have hreach := sum_reachScale_rpow_le_of_reach hd0 hP (hres j le_rfl) hτ hfin hω₂j.2.2.1 hKr
  have hreach' : ∑ z ∈ crossingClusterVertices ω ⟨j, 0⟩,
      (((3 : ℝ) ^ (partitionCoarseData hd0 hP ⟨j, 0⟩ (hres j le_rfl)).reachScale z) ^
        ((2 : ℝ) * d)) ^ Real.conjExponent (1 + ε / 2) ≤ Kr * ((3 : ℝ) ^ j) ^ d := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) hreach
    rw [← Real.rpow_mul (by positivity)]
  exact coarseComparison_on_cube hd0 hP C u (hres j le_rfl) h02 (hsub (j + 2) (by omega))
    (hsucc (j + 2) (by omega)) hharm hq hCM hKr hMeyj hreach'

end Rigidity.Proofs.Regularity
