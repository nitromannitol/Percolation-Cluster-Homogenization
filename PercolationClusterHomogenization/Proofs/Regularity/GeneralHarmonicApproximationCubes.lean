import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZero
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationSquares
import PercolationClusterHomogenization.Proofs.Cluster.PartitionCoarseData

/-!
# Armstrong–Dario, Lemma 7.1, in every dimension, from the estimates on triadic cubes

The proof of Lemma 7.1 of Armstrong and Dario (arXiv:1609.09431v2) consists of three estimates on
the triadic cube `□_j` for `3^j` above the minimal scale, followed by an iteration (Step 4):

* (7.7), the harmonic approximation of the coarsening on `□_j` (Steps 1 and 2):
  `inf_{w ∈ Ā(□_j)} ‖[u]_𝒫 - w‖_{L̲²(□_j)} ≤ C₁ 3^{-j α} Γ_{j + 3}`;
* (7.8), the comparison of `u` with its coarsening (Step 3), in `L²`:
  `|□_j|^{-1/2} ‖u - [u]_𝒫‖_{L²(C_*(□_j))} ≤ K₂ 3^{-j} Γ_{j + 3}`;
* the bound of Step 2 for constant `w = a`:
  `‖[u]_𝒫 - a‖_{L̲²(□_j)} ≤ K₃ |□_{j+3}|^{-1/2} ‖u - a‖_{L²(C_*(□_{j + 3}))}`;

where `Γ_j = inf_a |□_j|^{-1/2} ‖u - a‖_{L²(C_*(□_j))}` (`clusterCubeOsc`), `C_*(□_j)` being the
crossing cluster `crossingClusterVertices ω ⟨j, 0⟩` of the cube. `CubeEstimates` collects them,
and `cubeHarmonicApproximationAt_of_cubeEstimates` derives the form `CubeHarmonicApproximationAt`
of Lemma 7.1 used in the proof of Lemma 7.3, under the two inclusions of the clusters used in the
source: `C_*(□_j) ⊆ 𝒞_∞` and `𝒞_∞ ∩ B_r ⊆ C_*(□_{m + 1})` when `B_r ⊆ □_m`, above the minimal
scale. This is the argument of `planarHarmonicApproximationAt_of_squareEstimates`, with the factors
`(ρ / 3^j)^{d/2}` between the normalized norms on `C_*(□_j)` and on `C ∩ B_ρ`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

variable {d : ℕ}

/-- The normalized `ℓ²` norm `|□_j|^{-1/2} ‖g‖_{ℓ²(C_*(□_j))}` on the crossing cluster of the
triadic cube `□_j`. -/
noncomputable def clusterCubeL2 (ω : Configuration d) (j : ℕ) (g : Vertex d → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, g x ^ 2) / ((3 : ℝ) ^ j) ^ d)

/-- The oscillation `Γ_j = inf_a |□_j|^{-1/2} ‖u - a‖_{ℓ²(C_*(□_j))}` of a function on a
cluster. -/
noncomputable def clusterCubeOsc {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (j : ℕ) : ℝ :=
  ⨅ a : ℝ, clusterCubeL2 ω j (fun x => Rigidity.Section3.extend C u x - a)

/-- The estimates of the proof of Armstrong–Dario, Lemma 7.1, on the triadic cube `□_j`: (7.7),
the `L²` form of (7.8), and the bound of Step 2 for constant `w`. -/
def CubeEstimates {ω : Configuration d} (C : OpenComponent ω) (C₁ K₂ K₃ α : ℝ) (j : ℕ)
    (u : C → ℝ) : Prop :=
  cubeHarmonicDist d j (partitionCoarse C u) ≤
      C₁ / ((3 : ℝ) ^ j) ^ α * clusterCubeOsc C u (j + 3) ∧
    clusterCubeL2 ω j (fun x => Rigidity.Section3.extend C u x - partitionCoarse C u x) ≤
      K₂ / 3 ^ j * clusterCubeOsc C u (j + 3) ∧
    ∀ a : ℝ, cubeL2 d j (fun y => partitionCoarse C u y - a) ≤
      K₃ * clusterCubeL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - a)

theorem clusterCubeL2_nonneg (ω : Configuration d) (j : ℕ) (g : Vertex d → ℝ) :
    0 ≤ clusterCubeL2 ω j g :=
  Real.sqrt_nonneg _

theorem clusterCubeL2_add_le (ω : Configuration d) (j : ℕ) (g h : Vertex d → ℝ) :
    clusterCubeL2 ω j (fun x => g x + h x) ≤ clusterCubeL2 ω j g + clusterCubeL2 ω j h := by
  unfold clusterCubeL2
  exact sqrt_sum_sq_add_le _ (by positivity) g h

theorem clusterCubeOsc_nonneg {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (j : ℕ) : 0 ≤ clusterCubeOsc C u j :=
  le_ciInf fun _ => clusterCubeL2_nonneg _ _ _

theorem clusterCubeOsc_le_clusterCubeL2 {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) (j : ℕ) (a : ℝ) :
    clusterCubeOsc C u j ≤ clusterCubeL2 ω j (fun x => Rigidity.Section3.extend C u x - a) :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ clusterCubeL2_nonneg _ _ _⟩ a

theorem extend_val_of_mem {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ) (x : C) :
    Rigidity.Section3.extend C u x.val = u x := by
  simp [Rigidity.Section3.extend]

theorem mem_triadicCube_zero_iff' {j : ℕ} {x : Vertex d} :
    x ∈ (⟨j, 0⟩ : TriadicCube d).vertices ↔ ∀ i, 2 * |x i| < 3 ^ j := by
  simp only [TriadicCube.vertices, TriadicCube.side, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
    sub_zero, abs_mul]
  simp

theorem mem_cubeFinset_iff_int {m : ℕ} {x : Vertex d} :
    x ∈ triadicCubeFinset d m 0 ↔ ∀ i, 2 * |x i| < 3 ^ m := by
  rw [mem_cubeFinset_iff]
  refine forall_congr' fun i => ?_
  constructor
  · intro h
    have h' : 2 * |(x i : ℝ)| < 3 ^ m := by linarith
    exact_mod_cast h'
  · intro h
    have h' : ((2 * |x i| : ℤ) : ℝ) < ((3 ^ m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith

theorem mem_cubeFinset_iff_vertices {m : ℕ} {x : Vertex d} :
    x ∈ triadicCubeFinset d m 0 ↔ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices := by
  rw [mem_cubeFinset_iff_int, mem_triadicCube_zero_iff']

theorem mem_cubeFinset_of_mem_crossingClusterVertices {ω : Configuration d} {j : ℕ}
    {x : Vertex d} (hx : x ∈ crossingClusterVertices ω ⟨j, 0⟩) : x ∈ triadicCubeFinset d j 0 :=
  mem_cubeFinset_iff_vertices.2
    (TriadicCube.crossingCluster_subset ω _ (mem_crossingClusterVertices.1 hx))

/-- The crossing cluster of a cube against its cube. -/
theorem clusterCubeL2_le_cubeL2 (ω : Configuration d) (j : ℕ) (g : Vertex d → ℝ) :
    clusterCubeL2 ω j g ≤ cubeL2 d j g := by
  unfold clusterCubeL2 cubeL2
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg
    (fun x hx => mem_cubeFinset_of_mem_crossingClusterVertices hx) fun _ _ _ => sq_nonneg _

/-- The cluster of `□_j` inside the cluster ball `C ∩ B_ρ`, `√d 3^j ≤ ρ`: for every `a`,
`|□_j|^{-1/2} ‖u - a‖_{ℓ²(C_*(□_j))} ≤ (ρ / 3^j)^{d/2} ρ^{-d/2} ‖u - a‖_{ℓ²(C ∩ B_ρ)}`. -/
theorem clusterCubeL2_le_clusterBallVolumeL2 (hd : 0 < d) {ω : Configuration d}
    (C : OpenComponent ω) (u : C → ℝ) {j : ℕ} {ρ : ℝ}
    (hsub : ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hρ : Real.sqrt d * 3 ^ j ≤ ρ) (a : ℝ) :
    clusterCubeL2 ω j (fun x => Rigidity.Section3.extend C u x - a) ≤
      Real.sqrt ((ρ / 3 ^ j) ^ d) * clusterBallVolumeL2 C ρ (u - fun _ => a) := by
  classical
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hsd : 1 ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by norm_num) (by positivity), one_pow]; exact_mod_cast hd
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by nlinarith) hρ
  have hin := dist_lt_of_mem_cubeFinset_of_le hd hρ
  set G : Vertex d → ℝ := fun x => Rigidity.Section3.extend C u x - a with hG
  have hsum : ∑ x ∈ crossingClusterVertices ω ⟨j, 0⟩, G x ^ 2 ≤
      ∑ x ∈ componentEuclideanBall C 0 ρ, (u x - a) ^ 2 := by
    have e : ∑ x ∈ componentEuclideanBall C 0 ρ, (u x - a) ^ 2 =
        ∑ y ∈ (componentEuclideanBall C 0 ρ).image Subtype.val, G y ^ 2 := by
      rw [sum_image fun _ _ _ _ h => Subtype.val_injective h]
      refine sum_congr rfl fun x _ => ?_
      simp only [hG, extend_val_of_mem]
    rw [e]
    refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
    rw [mem_image]
    refine ⟨⟨y, hsub y hy⟩, ?_, rfl⟩
    rw [mem_componentEuclideanBall]
    exact hin y (mem_cubeFinset_of_mem_crossingClusterVertices hy)
  unfold clusterCubeL2 clusterBallVolumeL2
  simp only [Pi.sub_apply]
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [div_pow, div_mul_div_comm, mul_comm (ρ ^ d), mul_div_mul_right _ _ (pow_ne_zero d hρ0.ne')]
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- The oscillation on the cluster of `□_j` against the cluster ball `C ∩ B_ρ`, `√d 3^j ≤ ρ`. -/
theorem clusterCubeOsc_le (hd : 0 < d) {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    {j : ℕ} {ρ : ℝ} (hsub : ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hρ : Real.sqrt d * 3 ^ j ≤ ρ) :
    clusterCubeOsc C u j ≤
      Real.sqrt ((ρ / 3 ^ j) ^ d) * ⨅ a : ℝ, clusterBallVolumeL2 C ρ (u - fun _ => a) := by
  rw [Real.mul_iInf_of_nonneg (Real.sqrt_nonneg _)]
  exact le_ciInf fun a => (clusterCubeOsc_le_clusterCubeL2 C u j a).trans
    (clusterCubeL2_le_clusterBallVolumeL2 hd C u hsub hρ a)

/-- A ball between `□_{m - d - 2}` and `□_m`: for `√d ≤ r`, `2 r ≤ 3^m < 6 r`, the normalized norm
on the lattice ball `B_r` is at most `ballCubeFactor d` times the one on `□_m`. -/
theorem componentBallL2_le_ballCubeFactor [NeZero d] {r : ℝ} {m : ℕ} (hr0 : 0 < r)
    (hrd : Real.sqrt d ≤ r) (hm1 : 2 * r ≤ 3 ^ m) (hm2 : (3 : ℝ) ^ m < 6 * r)
    (g : Vertex d → ℝ) :
    componentBallL2 (latticeComponent d) 0 r (fun x => g x.val) ≤
      ballCubeFactor d * cubeL2 d m g := by
  have hsub : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r →
        y ∈ triadicCubeFinset d m 0 := fun y hy => mem_cubeFinset_of_dist_lt (by linarith)
  exact (componentBallL2_le_cubeL2 hsub (dist_lt_of_mem_cubeFinset_sub hr0 hrd hm2) g).trans
    (mul_le_mul_of_nonneg_right (sqrt_ratio_le_ballCubeFactor m) (cubeL2_nonneg _ _))

/-- The arithmetic of `coarseComparison_of_cubeEstimates`. -/
theorem comparison_arith {V F₁ W K₂ t Γ F₂ I s₁ s₂ K r : ℝ} (hV : V ≤ F₁ * W)
    (hW : W ≤ K₂ / t * Γ) (hΓ : Γ ≤ F₂ * I) (hF₁ : F₁ ≤ s₁) (ht : K₂ / t ≤ K₂ / (6 * r))
    (hF₂ : F₂ ≤ s₂) (hF₁0 : 0 ≤ F₁) (hKt : 0 ≤ K₂ / t) (hΓ0 : 0 ≤ Γ) (hI0 : 0 ≤ I)
    (hs₁ : 0 ≤ s₁) (hKr : 0 ≤ K₂ / (6 * r)) (hK : K₂ * s₁ * s₂ / 6 ≤ K) (hr : 0 < r) :
    V ≤ K / r * I := by
  have h1 : F₁ * W ≤ F₁ * (K₂ / t * Γ) := mul_le_mul_of_nonneg_left hW hF₁0
  have h2 : K₂ / t * Γ ≤ K₂ / (6 * r) * (F₂ * I) := mul_le_mul ht hΓ hΓ0 hKr
  have h3 : F₁ * (K₂ / t * Γ) ≤ s₁ * (K₂ / (6 * r) * (F₂ * I)) :=
    mul_le_mul hF₁ h2 (mul_nonneg hKt hΓ0) hs₁
  have h4 : K₂ / (6 * r) * (F₂ * I) ≤ K₂ / (6 * r) * (s₂ * I) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hF₂ hI0) hKr
  have h5 : s₁ * (K₂ / (6 * r) * (s₂ * I)) = K₂ * s₁ * s₂ / 6 / r * I := by
    rw [div_div]; ring
  have h6 : K₂ * s₁ * s₂ / 6 / r * I ≤ K / r * I :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK hr.le) hI0
  calc V ≤ F₁ * W := hV
    _ ≤ F₁ * (K₂ / t * Γ) := h1
    _ ≤ s₁ * (K₂ / (6 * r) * (F₂ * I)) := h3
    _ ≤ s₁ * (K₂ / (6 * r) * (s₂ * I)) := mul_le_mul_of_nonneg_left h4 hs₁
    _ = K₂ * s₁ * s₂ / 6 / r * I := h5
    _ ≤ K / r * I := h6

set_option maxHeartbeats 400000 in
/-- The comparison (ii) of `cubeHarmonicApproximationAt_of_cubeEstimates` at one radius. -/
theorem coarseComparison_of_cubeEstimates (hd : 0 < d) {ω : Configuration d}
    (C : OpenComponent ω) (u : C → ℝ) {L K₂ K A X₀ R r : ℝ} (hLd : Real.sqrt d ≤ L)
    (hA : 4374 * L ≤ A) (hK₂ : 0 ≤ K₂)
    (hK2 : K₂ * Real.sqrt (18 ^ d) * Real.sqrt ((A / 162) ^ d) / 6 ≤ K) (hX₀r : X₀ ≤ r)
    (hr1 : 1 ≤ r) (hAr : A * r ≤ R)
    (hsub : ∀ j : ℕ, X₀ ≤ 3 ^ j → ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hgeo : ∀ (m : ℕ) (r : ℝ), X₀ ≤ r → 2 * r ≤ 3 ^ m → ∀ x : C,
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding (0 : Vertex d)) < r →
        x.val ∈ crossingClusterVertices ω ⟨m + 1, 0⟩)
    (hS3 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
      clusterCubeL2 ω j (fun x => Rigidity.Section3.extend C u x - partitionCoarse C u x) ≤
        K₂ / 3 ^ j * clusterCubeOsc C u (j + 3)) :
    clusterBallVolumeL2 C r (u - fun x => partitionCoarse C u x.val) ≤
      K / r * ⨅ a : ℝ, clusterBallVolumeL2 C (A * r) (u - fun _ => a) := by
  have hr0 : 0 < r := by linarith
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := hsd.trans hLd
  have hA0 : 0 ≤ A := (mul_nonneg (by norm_num) hL0).trans hA
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near hr1
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hX₀m : X₀ ≤ 3 ^ m := by linarith
  have e4 : (3 : ℝ) ^ (m + 4) = 81 * 3 ^ m := by ring
  have e1 : (3 : ℝ) ^ (m + 1 + 3) = 81 * 3 ^ m := by ring
  have hdom : L * 3 ^ (m + 1 + 3) ≤ R := by
    rw [e1]
    have h1 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 81 * L)
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have hLr : 0 ≤ L * r := mul_nonneg hL0 hr0.le
    linarith
  have hX₀m1 : X₀ ≤ 3 ^ (m + 1) :=
    hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hX₀m4 : X₀ ≤ 3 ^ (m + 4) :=
    hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hS3 := hS3 (m + 1) hX₀m1 hdom
  have hm4Ar : Real.sqrt d * 3 ^ (m + 4) ≤ A * r := by
    rw [e4]
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have h3 := mul_le_mul_of_nonneg_right hLd hr0.le
    have h4 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 81 * Real.sqrt d)
    have hLr : 0 ≤ L * r := mul_nonneg hL0 hr0.le
    linarith
  have hΓ := clusterCubeOsc_le hd C u (hsub (m + 4) hX₀m4) hm4Ar
  -- the cluster ball `C ∩ B_r` inside `C_*(□_{m + 1})`
  have hsum : ∑ x ∈ componentEuclideanBall C 0 r,
      (u x - partitionCoarse C u x.val) ^ 2 ≤
      ∑ x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩,
        (Rigidity.Section3.extend C u x - partitionCoarse C u x) ^ 2 := by
    have e : ∑ x ∈ componentEuclideanBall C 0 r, (u x - partitionCoarse C u x.val) ^ 2 =
        ∑ y ∈ (componentEuclideanBall C 0 r).image Subtype.val,
          (Rigidity.Section3.extend C u y - partitionCoarse C u y) ^ 2 := by
      rw [sum_image fun _ _ _ _ h => Subtype.val_injective h]
      refine sum_congr rfl fun x _ => ?_
      simp only [extend_val_of_mem]
    rw [e]
    refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
    rw [mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hgeo m r hX₀r hm1 x ((mem_componentEuclideanBall C 0 r x).1 hx)
  have h31 : (0 : ℝ) < 3 ^ (m + 1) := by positivity
  obtain ⟨G, hGdef⟩ : ∃ G : Vertex d → ℝ,
      G = fun x => Rigidity.Section3.extend C u x - partitionCoarse C u x := ⟨_, rfl⟩
  rw [← hGdef] at hS3
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : ℝ, F₁ = Real.sqrt (((3 : ℝ) ^ (m + 1) / r) ^ d) := ⟨_, rfl⟩
  have hcmp : clusterBallVolumeL2 C r (u - fun x => partitionCoarse C u x.val) ≤
      F₁ * clusterCubeL2 ω (m + 1) G := by
    rw [hF₁, hGdef]
    unfold clusterCubeL2 clusterBallVolumeL2
    simp only [Pi.sub_apply]
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_pow, div_mul_div_comm, mul_comm (((3 : ℝ) ^ (m + 1)) ^ d),
      mul_div_mul_right _ _ (pow_ne_zero d h31.ne')]
    exact div_le_div_of_nonneg_right hsum (by positivity)
  -- the factors
  have hf1 : F₁ ≤ Real.sqrt (18 ^ d) := by
    rw [hF₁]
    apply Real.sqrt_le_sqrt
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ hr0]
    have : (3 : ℝ) ^ (m + 1) = 3 * 3 ^ m := by ring
    linarith
  have hf2 : Real.sqrt ((A * r / 3 ^ (m + 4)) ^ d) ≤ Real.sqrt ((A / 162) ^ d) := by
    apply Real.sqrt_le_sqrt
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by norm_num), e4]
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 81 * A)
    linarith
  have hf3 : K₂ / 3 ^ (m + 1) ≤ K₂ / (6 * r) := by
    apply div_le_div_of_nonneg_left hK₂ (by positivity)
    have : (3 : ℝ) ^ (m + 1) = 3 * 3 ^ m := by ring
    linarith
  have hI0 := clusterBallVolumeL2_iInf_nonneg C (A * r) u
  have hΓ0 := clusterCubeOsc_nonneg C u (m + 4)
  have e5 : m + 1 + 3 = m + 4 := by ring
  rw [e5] at hS3
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ⨅ a : ℝ, clusterBallVolumeL2 C (A * r) (u - fun _ => a) :=
    ⟨_, rfl⟩
  rw [← hIdef] at hΓ hI0 ⊢
  have hF₁0 : 0 ≤ F₁ := by rw [hF₁]; exact Real.sqrt_nonneg _
  exact comparison_arith hcmp hS3 hΓ hf1 hf3 hf2 hF₁0 (div_nonneg hK₂ h31.le) hΓ0 hI0
    (Real.sqrt_nonneg _) (div_nonneg hK₂ (by positivity)) hK2 hr0

/-- The bound (iii) of `cubeHarmonicApproximationAt_of_cubeEstimates` at one radius. -/
theorem coarseBound_of_cubeEstimates [NeZero d] {ω : Configuration d} (C : OpenComponent ω)
    (u : C → ℝ) {L K₃ K A X₀ R r : ℝ} (hLd : Real.sqrt d ≤ L) (hA : 4374 * L ≤ A)
    (hK₃ : 0 ≤ K₃) (hK3 : ballCubeFactor d * K₃ * Real.sqrt ((A / 54) ^ d) ≤ K)
    (hX₀r : X₀ ≤ r) (hr1 : 1 ≤ r) (hrd : Real.sqrt d ≤ r) (hAr : A * r ≤ R)
    (hsub : ∀ j : ℕ, X₀ ≤ 3 ^ j → ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hS2 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R → ∀ a : ℝ,
      cubeL2 d j (fun y => partitionCoarse C u y - a) ≤
        K₃ * clusterCubeL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - a)) (a : ℝ) :
    componentBallL2 (latticeComponent d) 0 r (fun x => partitionCoarse C u x.val - a) ≤
      K * clusterBallVolumeL2 C (A * r) (u - fun _ => a) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hr0 : 0 < r := by linarith
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := hsd.trans hLd
  have hA0 : 0 ≤ A := (mul_nonneg (by norm_num) hL0).trans hA
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near hr1
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hX₀m : X₀ ≤ 3 ^ m := by linarith
  have e3 : (3 : ℝ) ^ (m + 3) = 27 * 3 ^ m := by ring
  have hdom : L * 3 ^ (m + 3) ≤ R := by
    rw [e3]
    have h1 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 27 * L)
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have hLr : 0 ≤ L * r := mul_nonneg hL0 hr0.le
    linarith
  have hX₀m3 : X₀ ≤ 3 ^ (m + 3) :=
    hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hS2 := hS2 m hX₀m hdom a
  have hm3Ar : Real.sqrt d * 3 ^ (m + 3) ≤ A * r := by
    rw [e3]
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have h3 := mul_le_mul_of_nonneg_right hLd hr0.le
    have h4 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 27 * Real.sqrt d)
    have hLr : 0 ≤ L * r := mul_nonneg hL0 hr0.le
    linarith
  have hc := clusterCubeL2_le_clusterBallVolumeL2 hd C u (hsub (m + 3) hX₀m3) hm3Ar a
  have hball := componentBallL2_le_ballCubeFactor hr0 hrd hm1 hm2
    (fun y => partitionCoarse C u y - a)
  have hf : Real.sqrt ((A * r / 3 ^ (m + 3)) ^ d) ≤ Real.sqrt ((A / 54) ^ d) := by
    apply Real.sqrt_le_sqrt
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by norm_num), e3]
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 27 * A)
    linarith
  have hV0 : 0 ≤ clusterBallVolumeL2 C (A * r) (u - fun _ => a) := Real.sqrt_nonneg _
  have hF0 := ballCubeFactor_nonneg d
  calc componentBallL2 (latticeComponent d) 0 r (fun x => partitionCoarse C u x.val - a)
      ≤ ballCubeFactor d * cubeL2 d m (fun y => partitionCoarse C u y - a) := hball
    _ ≤ ballCubeFactor d *
          (K₃ * clusterCubeL2 ω (m + 3) (fun x => Rigidity.Section3.extend C u x - a)) :=
        mul_le_mul_of_nonneg_left hS2 hF0
    _ ≤ ballCubeFactor d * (K₃ * (Real.sqrt ((A * r / 3 ^ (m + 3)) ^ d) *
          clusterBallVolumeL2 C (A * r) (u - fun _ => a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hK₃) hF0
    _ ≤ ballCubeFactor d * (K₃ * (Real.sqrt ((A / 54) ^ d) *
          clusterBallVolumeL2 C (A * r) (u - fun _ => a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hf hV0) hK₃) hF0
    _ = ballCubeFactor d * K₃ * Real.sqrt ((A / 54) ^ d) *
          clusterBallVolumeL2 C (A * r) (u - fun _ => a) := by ring
    _ ≤ K * clusterBallVolumeL2 C (A * r) (u - fun _ => a) :=
        mul_le_mul_of_nonneg_right hK3 hV0

/-- The constant `K` of `cubeHarmonicApproximationAt_of_cubeEstimates`. -/
noncomputable def cubeApproxConst (d : ℕ) (L K₂ K₃ : ℝ) : ℝ :=
  max (Real.sqrt ((27 * L) ^ d))
    (max (K₂ * Real.sqrt (18 ^ d) * Real.sqrt ((4374 * L / 162) ^ d) / 6)
      (ballCubeFactor d * K₃ * Real.sqrt ((4374 * L / 54) ^ d)))

/-- **Armstrong–Dario, Lemma 7.1, in dimension `d`, from the estimates on triadic cubes.** If,
above a scale `X₀ ≥ 1`, the crossing clusters of the cubes lie in `C`, the cluster balls
`C ∩ B_r` with `B_r ⊆ □_m` lie in `C_*(□_{m + 1})`, and every `u` harmonic on `C ∩ B_R` satisfies
`CubeEstimates` on the cubes `□_j` with `L 3^{j + 3} ≤ R`, `L ≥ max(1, √d)`, then `C` satisfies
`CubeHarmonicApproximationAt` with `A = 4374 L`, the exponent `α / 2`, the constant
`cubeApproxConst d L K₂ K₃`, above the scale `max X₀ (cubeScale d A L C₁ K₂ α)`. -/
theorem cubeHarmonicApproximationAt_of_cubeEstimates [NeZero d] {L C₁ K₂ K₃ α : ℝ}
    (hL : 1 ≤ L) (hLd : Real.sqrt d ≤ L) (hC₁ : 0 ≤ C₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hα : 0 < α) {ω : Configuration d} (C : OpenComponent ω) {X₀ : ℝ} (hX₀ : 1 ≤ X₀)
    (hsub : ∀ j : ℕ, X₀ ≤ 3 ^ j → ∀ x ∈ crossingClusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hgeo : ∀ (m : ℕ) (r : ℝ), X₀ ≤ r → 2 * r ≤ 3 ^ m → ∀ x : C,
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding (0 : Vertex d)) < r →
        x.val ∈ crossingClusterVertices ω ⟨m + 1, 0⟩)
    (hest : ∀ R : ℝ, ∀ u : C → ℝ, IsHarmonicInBall C R u → ∀ j : ℕ, X₀ ≤ 3 ^ j →
      L * 3 ^ (j + 3) ≤ R → CubeEstimates C C₁ K₂ K₃ α j u) :
    CubeHarmonicApproximationAt C (4374 * L) (α / 2) (cubeApproxConst d L K₂ K₃)
      (max X₀ (cubeScale d (4374 * L) L C₁ K₂ α)) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set A := 4374 * L with hAdef
  set K := cubeApproxConst d L K₂ K₃ with hKdef
  set X := max X₀ (cubeScale d A L C₁ K₂ α) with hXdef
  have hA : 4374 * L ≤ A := le_of_eq hAdef.symm
  have hA0 : 0 < A := by linarith
  have hX₀X : X₀ ≤ X := by rw [hXdef]; exact le_max_left _ _
  have hsX : cubeScale d A L C₁ K₂ α ≤ X := by rw [hXdef]; exact le_max_right _ _
  have hX1 : 1 ≤ X := hX₀.trans hX₀X
  have hXd : Real.sqrt d ≤ X :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hsX
  have hKL : Real.sqrt ((27 * L) ^ d) ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK2 : K₂ * Real.sqrt (18 ^ d) * Real.sqrt ((A / 162) ^ d) / 6 ≤ K := by
    rw [hKdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hK3 : ballCubeFactor d * K₃ * Real.sqrt ((A / 54) ^ d) ≤ K := by
    rw [hKdef]; exact (le_max_right _ _).trans (le_max_right _ _)
  intro R hR u hu
  have hR0 : 0 < R := lt_of_lt_of_le (mul_pos hA0 (by linarith)) hR
  set I := ⨅ a : ℝ, clusterBallVolumeL2 C R (u - fun _ => a) with hIdef
  have hI0 : 0 ≤ I := clusterBallVolumeL2_iInf_nonneg C R u
  set B := Real.sqrt ((27 * L) ^ d) * I with hBdef
  have hB0 : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) hI0
  refine ⟨?_, ?_, ?_⟩
  · -- the harmonic approximation hypothesis on the balls of the lattice
    have H2 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
        clusterCubeOsc C u j ≤ cubeOsc d j (partitionCoarse C u) +
          K₂ / 3 ^ j * clusterCubeOsc C u (j + 3) := by
      intro j hj hjR
      have hS3 := (hest R u hu j hj hjR).2.1
      have hle : ∀ a : ℝ, clusterCubeOsc C u j - K₂ / 3 ^ j * clusterCubeOsc C u (j + 3) ≤
          cubeL2 d j (fun y => partitionCoarse C u y - a) := by
        intro a
        have h1 := clusterCubeOsc_le_clusterCubeL2 C u j a
        have e : (fun x => Rigidity.Section3.extend C u x - a) = fun x =>
            (partitionCoarse C u x - a) +
              (Rigidity.Section3.extend C u x - partitionCoarse C u x) := by
          funext x; ring
        rw [e] at h1
        have h2 := clusterCubeL2_add_le ω j (fun x => partitionCoarse C u x - a)
          (fun x => Rigidity.Section3.extend C u x - partitionCoarse C u x)
        have h3 := clusterCubeL2_le_cubeL2 ω j (fun y => partitionCoarse C u y - a)
        linarith
      have := le_ciInf hle
      unfold cubeOsc
      linarith
    have H3 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ j ≤ R → R < 27 * L * 3 ^ j →
        clusterCubeOsc C u j ≤ R / 3 ^ j * B := by
      intro j hj hjR hjR'
      have h3 : (0 : ℝ) < 3 ^ j := by positivity
      have hdj : Real.sqrt d * 3 ^ j ≤ R :=
        (mul_le_mul_of_nonneg_right hLd h3.le).trans hjR
      have h1 := clusterCubeOsc_le hd C u (hsub j hj) hdj
      have hfac : Real.sqrt ((R / 3 ^ j) ^ d) ≤ Real.sqrt ((27 * L) ^ d) := by
        apply Real.sqrt_le_sqrt
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_iff₀ h3]; linarith
      have hRj : 1 ≤ R / 3 ^ j := by
        rw [le_div_iff₀ h3]; nlinarith
      calc clusterCubeOsc C u j ≤ Real.sqrt ((R / 3 ^ j) ^ d) * I := h1
        _ ≤ Real.sqrt ((27 * L) ^ d) * I := mul_le_mul_of_nonneg_right hfac hI0
        _ = B := rfl
        _ ≤ R / 3 ^ j * B := le_mul_of_one_le_left hB0 hRj
    have hHA := harmonicApproximation_of_cubes (f := partitionCoarse C u)
      (Γ := clusterCubeOsc C u) (clusterCubeOsc_nonneg C u) hL hLd hA hC₁ hK₂ hα hX₀X hsX hB0
      (fun m hm hmR => (hest R u hu m hm hmR).1) H2 H3
    refine hHA.mono_E (by linarith) ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKL hI0) hR0.le
  · intro r hr hrA
    exact coarseComparison_of_cubeEstimates hd C u hLd hA hK₂ hK2 (hX₀X.trans hr)
      (hX1.trans hr) (by rw [le_div_iff₀ hA0] at hrA; linarith) hsub hgeo
      (fun j hj hjR => (hest R u hu j hj hjR).2.1)
  · intro r hr hrA a
    exact coarseBound_of_cubeEstimates C u hLd hA hK₃ hK3 (hX₀X.trans hr) (hX1.trans hr)
      (hXd.trans hr) (by rw [le_div_iff₀ hA0] at hrA; linarith) hsub
      (fun j hj hjR => (hest R u hu j hj hjR).2.2) a

end Rigidity.Proofs.Regularity
