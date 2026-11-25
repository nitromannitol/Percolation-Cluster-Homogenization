import PercolationClusterHomogenization.Proofs.Regularity.GeneralCoarseBound

/-!
# Step 2 of the proof of Lemma 7.1 on triadic cubes, almost surely above a minimal scale

`cubeCoarseBoundAS_holds` proves the bound of Step 2 of the proof of Armstrong–Dario, Lemma 7.1
(arXiv:1609.09431v2), with `w = a` a constant, in `L²` on the triadic cubes of `ℤᵈ`, `d ≥ 2`,
almost surely above a minimal scale `𝒳 ≤ O_s(θ)`: from the comparison (7.8)
(`cubeCoarseComparisonAS_holds`), the minimal scales of Proposition 2.4 (the moments of the sizes
of the partition cubes, `cubeMinimalScales_holds`, and the cells of the reverse Hölder partition,
`cubeRegularityScales_holds`), the Meyers estimate (`meyers_rh_uniform`, through `meyers_on_cube`)
and the density of the infinite cluster. The planar form is `planarCoarseBoundTwo_of_minimalScales`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster Rigidity.Proofs.Cluster.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

/-- **The Meyers estimate on `□_j`** for `u` on the crossing cluster of `□_{j+2}`, from the cells
of the reverse Hölder partition. -/
theorem meyers_on_cube {A₀ ε t K CM : ℝ}
    (hMey : ∀ (ω : Configuration d) (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (n : ℕ)
        (x₀ : Vertex d) (s : Vertex d → ℕ),
        (∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 n x₀ → b ∈ U₀) →
        (∀ a ∈ U₀, a ∈ enl 1 n x₀ → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
          openLaplacian ω u a = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2))
    (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    (h2C : ∀ x ∈ crossingClusterVertices ω ⟨j + 2, 0⟩, x ∈ C.supp)
    (hharm : ∀ (x : Vertex d) (hx : x ∈ C.supp), x ∈ triadicCubeFinset d (j + 3) 0 →
      componentLaplacian C u ⟨x, hx⟩ = 0)
    (s : Vertex d → ℕ) (hcell : ∀ x, ∀ z ∈ cube (s x) x, s z = s x)
    (hnb : ∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1)
    (hrh : ∀ (k : ℕ) (y : Vertex d), s y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω)
    (hsize : ∀ z ∈ cube (j + 1) (0 : Vertex d), s z ≤ j + 1)
    (hmom : ∑ x ∈ cube j (0 : Vertex d), ((3 : ℝ) ^ s x) ^ t ≤
      K * (cube j (0 : Vertex d)).card) :
    avg (cube j (0 : Vertex d)) (fun x => clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩)
        (Rigidity.Section3.extend C u) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 j (0 : Vertex d)) (clusterEnergy ω (crossingClusterVertices ω ⟨j + 2, 0⟩)
        (Rigidity.Section3.extend C u)) ^ (1 + ε / 2) := by
  have hmemenl : ∀ b ∈ enl 1 j (0 : Vertex d), b ∈ triadicCubeFinset d (j + 1) 0 := by
    intro b hb
    rw [enl_one_zero_eq_cube_succ] at hb
    exact mem_cubeFinset_of_mem_cube_zero hb
  refine hMey ω (crossingClusterVertices ω ⟨j + 2, 0⟩) (Rigidity.Section3.extend C u) j 0 s
    (fun a ha b hab hb => ?_) (fun a ha hae _ => ?_) hcell hnb (fun z hz => ?_)
    (fun k y hk _ => hrh k y hk) hmom
  · have hbV : b ∈ (⟨j + 2, 0⟩ : TriadicCube d).vertices :=
      mem_cubeFinset_iff_vertices.1 (mem_cubeFinset_mono (by omega) (hmemenl b hb))
    exact mem_crossingClusterVertices.2
      (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 ha) hbV hab)
  · have haC := h2C a ha
    rw [openLaplacian_extend_eq_componentLaplacian C u haC]
    exact hharm a haC (mem_cubeFinset_mono (by omega) (hmemenl a hae))
  · rw [enl_one_zero_eq_cube_succ] at hz ⊢
    intro w hw'
    have hle' := hsize z hz
    have h1 : w ∈ cube (j + 1) z := cube_mono hle' z hw'
    rw [cube_eq_of_mem hz] at h1
    exact h1

/-- Step 2 of the proof of Armstrong–Dario, Lemma 7.1, with `w = a`, in `L²` on the cubes `□_j`
of `ℤᵈ`, almost surely on the infinite cluster above a minimal scale `𝒳 ≤ O_s(θ)`, for the
functions harmonic on `𝒞_∞ ∩ B_R`, `√d 3^{j+3} ≤ R`. -/
def CubeCoarseBoundAS (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s θ K₃ : ℝ, 0 < s ∧ 0 < θ ∧ 0 ≤ K₃ ∧
    ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → Real.sqrt d * 3 ^ (j + 3) ≤ R → ∀ a : ℝ,
            cubeL2 d j (fun y => partitionCoarse (uniqueInfiniteComponent h) u y - a) ≤
              K₃ * clusterCubeL2 ω (j + 3)
                (fun x => Rigidity.Section3.extend (uniqueInfiniteComponent h) u x - a)

set_option maxHeartbeats 400000 in
/-- **Step 2 on triadic cubes almost surely**, for `p_c(d) < p < 1`, `d ≥ 2`. -/
theorem cubeCoarseBoundAS_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : CubeCoarseBoundAS d p := by
  have hd0 : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨s₀, θ₀, K₂, hs₀, hθ₀, hK₂, X₀, hX₀m, hX₀0, hX₀os, hX₀ae⟩ :=
    cubeCoarseComparisonAS_holds hd hpc hp1
  obtain ⟨s₃, θ₃, hs₃, hθ₃, M₃, hM₃m, hM₃0, hM₃os, hM₃ae⟩ := cubePartitionSizeScale_holds hd hpc
  obtain ⟨A₀, sc, hcellae, hmoms⟩ := cubeRegularityScales_holds hd hpc
  obtain ⟨ε, hε, t, ht, hMK⟩ := meyers_rh_uniform (d := d) (by omega) A₀
  have hq : 1 < 1 + ε / 2 := by linarith
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁ae⟩ :=
    hmoms t ht (1 / 2) (by norm_num)
  obtain ⟨CM, hCM, hMey⟩ := hMK K₁ hK₁
  have hpq := Real.HolderConjugate.conjExponent hq
  have hq'1 : 1 < Real.conjExponent (1 + ε / 2) := hpq.symm.lt
  have hd1 : (1 : ℝ) ≤ 2 * d - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    linarith
  have hτ1 : 1 ≤ ((2 : ℝ) * d - 1) * Real.conjExponent (1 + ε / 2) := by nlinarith
  obtain ⟨r₂, Cs, hr₂, hCs, M₂, hM₂m, hM₂0, hM₂os, hM₂ae⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc _ hτ1
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (Real.sqrt d)
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  -- the minimal scale
  obtain ⟨θ₁₂, hθ₁₂, h12⟩ := Rigidity.Dirichlet.IsOsBond.exists_max hr₁ hr₂ hθ₁ hCs hM₁m hM₂m hM₁os hM₂os
  obtain ⟨θ₃₄, hθ₃₄, h34⟩ := Rigidity.Dirichlet.IsOsBond.exists_max hs₃ hs₄ hθ₃ hθ₄ hM₃m hM₄m hM₃os hM₄os
  obtain ⟨θY, hθY, hY⟩ := Rigidity.Dirichlet.IsOsBond.exists_max (lt_min hr₁ hr₂) (lt_min hs₃ hs₄) hθ₁₂ hθ₃₄
    (hM₁m.max hM₂m) (hM₃m.max hM₄m) h12 h34
  have hrY : 0 < min (min r₁ r₂) (min s₃ s₄) := lt_min (lt_min hr₁ hr₂) (lt_min hs₃ hs₄)
  have hYm : Measurable fun ω => max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω)) :=
    (hM₁m.max hM₂m).max (hM₃m.max hM₄m)
  have hY1 := IsOsBond.max hrY hθY (by positivity) hYm measurable_const hY
    (isOsBond_const (p := p) (d := d) (by norm_num : (0 : ℝ) < 1) hrY)
  have hY3 := IsOsBond.const_mul (by norm_num : (0 : ℝ) < 3) hY1
  have hY3m : Measurable fun ω => 3 * max (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1 :=
    (hYm.max measurable_const).const_mul 3
  obtain ⟨θX, hθX, hXos⟩ :=
    Rigidity.Dirichlet.IsOsBond.exists_max hs₀ hrY hθ₀ (by positivity) hX₀m hY3m hX₀os hY3
  -- the constant
  have hκ : 0 < theta d p / 2 := by positivity
  have hκ' : 0 < theta d p / 2 / 3 ^ d := by positivity
  obtain ⟨K₁', hK₁'def⟩ : ∃ K : ℝ, K = 16 * (d : ℝ) ^ 3 * partitionGradConst d ^ 2 *
      (CM ^ (1 / (1 + ε / 2)) * Cs ^ (1 / Real.conjExponent (1 + ε / 2))) := ⟨_, rfl⟩
  have hK₁'0 : 0 ≤ K₁' := by rw [hK₁'def]; positivity
  refine ⟨_, θX, Real.sqrt (27 ^ d) *
    Real.sqrt (2 * K₁' + 6 * (K₁' + K₂ ^ 2 + 1) / (theta d p / 2 / 3 ^ d)),
    lt_min hs₀ hrY, hθX, by positivity, _, hX₀m.max hY3m,
    fun ω => (hX₀0 ω).trans (le_max_left _ _), hXos, ?_⟩
  filter_upwards [hcellae, hM₁ae, hM₂ae, hM₃ae, hM₄ae, hX₀ae] with
    ω hcells hω₁ hω₂ hω₃' hω₄ hω₀ h
  obtain ⟨hP, hω₃⟩ := hω₃'
  obtain ⟨hcell, hnb, hrh⟩ := hcells
  set C := uniqueInfiniteComponent h with hCdef
  intro R u hu j hj hjR a
  have hinf := uniqueInfiniteComponent_infinite h
  have hjX₀ : X₀ ω ≤ 3 ^ j := (le_max_left _ _).trans hj
  have hjY : 3 * max (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1 ≤ 3 ^ j :=
    (le_max_right _ _).trans hj
  have hj1 : 1 ≤ j := by
    have h31 : (3 : ℝ) ^ 1 ≤ 3 ^ j := by
      have := le_max_right (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1
      rw [pow_one]; linarith
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h31
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hiY : max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω)) ≤ 3 ^ i := by
    rw [pow_succ] at hjY
    have := le_max_left (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1
    linarith
  have hle : ∀ m, i ≤ m → (3 : ℝ) ^ i ≤ 3 ^ m := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hi1 : M₁ ω ≤ 3 ^ i := ((le_max_left _ _).trans (le_max_left _ _)).trans hiY
  have hi2 : M₂ ω ≤ 3 ^ i := ((le_max_right _ _).trans (le_max_left _ _)).trans hiY
  have hi3 : M₃ ω ≤ 3 ^ i := ((le_max_left _ _).trans (le_max_right _ _)).trans hiY
  have hi4 : M₄ ω ≤ 3 ^ i := ((le_max_right _ _).trans (le_max_right _ _)).trans hiY
  have hres : ∀ m, i ≤ m → PartitionResolved ω ⟨m, 0⟩ := by
    intro m hm z hz
    have hz' : z ∈ triadicCubeFinset d m 0 := mem_cubeFinset_iff_vertices.2 hz
    have := hω₃ m (hi3.trans (hle m hm)) z hz'
    show (partitionCube ω z).scale ≤ m
    omega
  have hsub : ∀ m, i ≤ m → ∀ x ∈ crossingClusterVertices ω ⟨m, 0⟩, x ∈ C.supp := by
    intro m hm x hx
    obtain ⟨x₀, hx₀⟩ := exists_mem_cubeFinset_of_clusterCubeDensity hd0 C hκ (hω₄ h)
      (hi4.trans (hle m hm))
    exact mem_supp_of_mem_crossingClusterVertices hd0 hP (hres m hm) C hinf
      (mem_cubeFinset_iff_vertices.1 hx₀) x₀.2 hx
  have hsucc : ∀ m, i ≤ m → ∀ x ∈ triadicCubeFinset d m 0, x ∈ C.supp →
      x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩ := fun m hm x hx hxC =>
    mem_crossingClusterVertices_succ hd0 hP C hinf (hω₃ m (hi3.trans (hle m hm))) hx hxC
  have hincl : ∀ m n, i ≤ m → m < n →
      crossingClusterVertices ω ⟨m, 0⟩ ⊆ crossingClusterVertices ω ⟨n, 0⟩ := by
    intro m n hm hmn x hx
    have hxC := hsub m hm x hx
    have hx1 : x ∈ triadicCubeFinset d (n - 1) 0 :=
      mem_cubeFinset_mono (by omega) (mem_cubeFinset_of_mem_crossingClusterVertices hx)
    have := hsucc (n - 1) (by omega) x hx1 hxC
    rwa [show n - 1 + 1 = n by omega] at this
  have hharm := harm_on_cube_of_isHarmonicInBall hd0 hu hjR
  -- the Meyers estimate
  have hω₁' := hω₁ (i + 1 + 1) (hi1.trans (hle _ (by omega)))
  have hsize : ∀ z ∈ cube (i + 1 + 1) (0 : Vertex d), sc ω z ≤ i + 1 + 1 := fun z hz => by
    have := two_mul_le_of_three_pow_le_rpow_half' (hω₁'.2.1 z hz)
    omega
  have hMeyj := meyers_on_cube hMey C u (hsub (i + 1 + 2) (by omega)) hharm (sc ω) hcell hnb hrh
    hsize (hω₁ (i + 1) (hi1.trans (hle _ (by omega)))).1
  -- the moments of the sizes of the partition cubes
  obtain ⟨hsumS, -⟩ := hω₂ (i + 1) (hi2.trans (hle _ (by omega)))
  have hNpos : (0 : ℝ) < ((3 : ℝ) ^ (i + 1)) ^ d := by positivity
  have hmomS : ∑ z ∈ crossingClusterVertices ω ⟨i + 1, 0⟩,
      (((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * d - 1)) ^
        Real.conjExponent (1 + ε / 2) ≤ Cs * ((3 : ℝ) ^ (i + 1)) ^ d := by
    rw [div_le_iff₀ hNpos, toIntegerCube_vertices_zero_eq] at hsumS
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) (le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun z hz => mem_cubeFinset_of_mem_crossingClusterVertices hz)
        fun _ _ _ => by positivity) hsumS)
    rw [← Real.rpow_mul (by positivity)]
  have hPo := sum_sq_coarse_sub_mean_le_cube hd0 hP C u (hres (i + 1) (by omega))
    (hincl _ _ (by omega) (by omega)) (hsub (i + 1 + 2) (by omega))
    (hsucc (i + 1 + 2) (by omega)) hharm hq hCM hCs.le hMeyj hmomS a
  rw [← hK₁'def] at hPo
  -- the comparison (7.8)
  have h74 := hω₀ h R u hu (i + 1) hjX₀ hjR
  have h74' := h74.trans (mul_le_mul_of_nonneg_left
    (clusterCubeOsc_le_clusterCubeL2 C u (i + 1 + 3) a) (by positivity))
  have hL := sum_sq_le_of_clusterCubeL2_le h74'
  -- the density of the cluster
  have hcard := card_crossingClusterVertices_succ_ge hd0 C (hω₄ h) hi4 (hsucc i le_rfl)
  exact cubeL2_coarse_sub_le C u a _ hK₁'0 (sq_nonneg K₂) hκ' hPo hL
    (hincl _ _ (by omega) (by omega)) hcard

end Rigidity.Proofs.Regularity
