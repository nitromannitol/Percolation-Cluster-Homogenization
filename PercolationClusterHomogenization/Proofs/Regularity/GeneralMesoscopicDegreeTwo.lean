import PercolationClusterHomogenization.Proofs.Regularity.GeneralMesoscopicTwoMain
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds
import PercolationClusterHomogenization.Proofs.Regularity.OrderOneOriginTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicDegreeTwo

/-!
# Lemma 7.3 at `k = 2` in every dimension, almost surely

Armstrong and Dario (arXiv:1609.09431v2), Lemma 7.3, (7.18) at `k = 2`, for supercritical bond
percolation in every dimension `d ≥ 2` (`MesoscopicDegreeTwoAt d p`, and
`ArmstrongDarioMesoscopicDegreeTwo`), with no hypothesis, from:

* Lemma 7.1 in every dimension (`cubeHarmonicApproximation_holds`), in the ball form of the proof
  of Lemma 7.3 (`CubeHarmonicApproximationAt`), above a minimal scale `𝒳 ≤ O_s(θ)`;
* the minimal scales of Proposition 2.4 for the sizes of the partition cubes
  (`cubeMinimalScales_holds`), with the exponents `t = 1` and `t = d` for the moments and a large
  exponent `t` for the sizes: on a ball `B_R` the cube bounds give sides at most `9 R^{α/d}` and
  moments `∑ 3^s ≤ 9^d K₁ R^d`, `∑ 3^{d s} ≤ 9^d K₂ R^d` (`cube_boundsD`);
* the density of `𝒞_∞` in cubes (`exists_clusterCubeDensity_of_concentration` with
  `cluster_density_concentration`) and the almost sure existence of the partition.

`mesoscopicDegreeTwo_coreD` then gives (7.18) with `δ = α / 2`, `α ≤ 1` the exponent of
Lemma 7.1. This is the planar `mesoscopicDegreeTwoAt_of_inputs` in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- **The partition cubes on `B_R`** from the minimal scales: sides at most `9 R^β`, and moments
of orders one and `d` at most `9^d K R^d`. -/
theorem cube_boundsD [NeZero d] {ω : Configuration d} {K₁ K₂ β R M₁ M₂ M₃ t : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ht : (d : ℝ) / (d + t) ≤ β) (hR : 1 ≤ R)
    (hM₁ : M₁ ≤ R) (hM₂ : M₂ ≤ R) (hM₃ : M₃ ≤ R)
    (h₁ : ∀ m : ℕ, M₁ ≤ 3 ^ m →
      (∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
          ((3 : ℝ) ^ (partitionCube ω x).scale) ^ (1 : ℝ)) / ((3 : ℝ) ^ m) ^ d ≤ K₁)
    (h₂ : ∀ m : ℕ, M₂ ≤ 3 ^ m →
      (∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
          ((3 : ℝ) ^ (partitionCube ω x).scale) ^ (d : ℝ)) / ((3 : ℝ) ^ m) ^ d ≤ K₂)
    (h₃ : ∀ m : ℕ, M₃ ≤ 3 ^ m → ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
      (3 : ℝ) ^ (partitionCube ω x).scale ≤ (3 : ℝ) ^ ((d : ℝ) * m / (d + t))) :
    (∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R →
        (3 : ℝ) ^ (partitionCube ω y).scale ≤ 9 * R ^ β) ∧
    (∑ y ∈ latticeBallPointsD 0 R, (3 : ℝ) ^ (partitionCube ω y).scale ≤ 9 ^ d * K₁ * R ^ d) ∧
    ∑ y ∈ latticeBallPointsD 0 R, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d ≤
      9 ^ d * K₂ * R ^ d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ 2 * R + 1)
    (by norm_num : (1 : ℝ) < 3)
  have hm : 2 * R + 1 ≤ (3 : ℝ) ^ (n + 1) := hn2.le
  have hm9 : (3 : ℝ) ^ (n + 1) ≤ 9 * R := by rw [pow_succ]; linarith
  have hm0 : (0 : ℝ) < 3 ^ (n + 1) := by positivity
  have hmem : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R →
        y ∈ triadicCubeFinset d (n + 1) 0 := fun y hy =>
    mem_cubeFinset_of_dist_lt (by linarith)
  have hsub : latticeBallPointsD 0 R ⊆ (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices := by
    intro y hy
    rw [toIntegerCube_vertices_zero_eq]
    exact hmem y (mem_latticeBallPointsD.1 hy)
  have hcube : ((3 : ℝ) ^ (n + 1)) ^ d ≤ 9 ^ d * R ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hm0.le hm9 d
  have hmom : ∀ (K : ℝ) (f : Vertex d → ℝ), (∀ x, 0 ≤ f x) →
      (∑ x ∈ (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices, f x) /
        ((3 : ℝ) ^ (n + 1)) ^ d ≤ K →
      ∑ y ∈ latticeBallPointsD 0 R, f y ≤ 9 ^ d * K * R ^ d := by
    intro K f hf hK
    have hK0 : 0 ≤ K := le_trans (div_nonneg (sum_nonneg fun x _ => hf x) (by positivity)) hK
    have h1 : ∑ x ∈ (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices, f x ≤
        K * ((3 : ℝ) ^ (n + 1)) ^ d := by
      rwa [div_le_iff₀ (by positivity)] at hK
    calc ∑ y ∈ latticeBallPointsD 0 R, f y
        ≤ ∑ x ∈ (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices, f x :=
          sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hf x
      _ ≤ K * ((3 : ℝ) ^ (n + 1)) ^ d := h1
      _ ≤ K * (9 ^ d * R ^ d) := mul_le_mul_of_nonneg_left hcube hK0
      _ = 9 ^ d * K * R ^ d := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hyv : y ∈ (⟨n + 1, 0⟩ : TriadicCube d).vertices :=
      mem_cubeFinset_iff_vertices.1 (hmem y hy)
    have h1 := h₃ (n + 1) (by linarith) y hyv
    have e : (3 : ℝ) ^ ((d : ℝ) * ((n + 1 : ℕ) : ℝ) / (d + t)) =
        ((3 : ℝ) ^ (n + 1)) ^ ((d : ℝ) / (d + t)) := by
      rw [← Real.rpow_natCast (3 : ℝ) (n + 1), ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    rw [e] at h1
    have h31 : (1 : ℝ) ≤ 3 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have h2 : ((3 : ℝ) ^ (n + 1)) ^ ((d : ℝ) / (d + t)) ≤ ((3 : ℝ) ^ (n + 1)) ^ β :=
      Real.rpow_le_rpow_of_exponent_le h31 ht
    have h3 : ((3 : ℝ) ^ (n + 1)) ^ β ≤ (9 * R) ^ β :=
      Real.rpow_le_rpow (by positivity) hm9 hβ0
    have h4 : (9 * R) ^ β = (9 : ℝ) ^ β * R ^ β := Real.mul_rpow (by norm_num) (by linarith)
    have h5 : (9 : ℝ) ^ β ≤ 9 := by
      calc (9 : ℝ) ^ β ≤ 9 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
        _ = 9 := Real.rpow_one 9
    have h6 : 0 ≤ R ^ β := Real.rpow_nonneg (by linarith) _
    calc (3 : ℝ) ^ (partitionCube ω y).scale ≤ ((3 : ℝ) ^ (n + 1)) ^ β := h1.trans h2
      _ ≤ (9 * R) ^ β := h3
      _ = (9 : ℝ) ^ β * R ^ β := h4
      _ ≤ 9 * R ^ β := mul_le_mul_of_nonneg_right h5 h6
  · refine hmom K₁ (fun x => (3 : ℝ) ^ (partitionCube ω x).scale) (fun _ => by positivity) ?_
    have := h₁ (n + 1) (by linarith)
    simpa only [Real.rpow_one] using this
  · refine hmom K₂ (fun x => ((3 : ℝ) ^ (partitionCube ω x).scale) ^ d)
      (fun _ => by positivity) ?_
    have := h₂ (n + 1) (by linarith)
    simpa only [Real.rpow_natCast] using this

/-- Lemma 7.1 in the ball form for an exponent gives it for a smaller exponent. -/
theorem CubeHarmonicApproximationAt.mono_exponent [NeZero d] {ω : Configuration d}
    {C : OpenComponent ω} {A α α' K X : ℝ} (H : CubeHarmonicApproximationAt C A α K X)
    (hA : 2 ≤ A) (hK : 0 ≤ K) (hX : 1 ≤ X) (hαα : α' ≤ α) :
    CubeHarmonicApproximationAt C A α' K X := by
  intro R hR u hu
  obtain ⟨h1, h2, h3⟩ := H R hR u hu
  have hR0 : 0 ≤ R := le_trans (mul_nonneg (by linarith) (by linarith)) hR
  exact ⟨h1.mono_exponent hX (by linarith) (mul_nonneg (div_nonneg hK hR0)
    (iInf_nonneg_of_nonneg fun _ => Real.sqrt_nonneg _)) hαα, h2, h3⟩

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in every dimension `d ≥ 2`, for one
supercritical law**, with no hypothesis. -/
theorem mesoscopicDegreeTwoAt_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : MesoscopicDegreeTwoAt d p := by
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 hd1
  obtain ⟨s₁, θ₁, A, α, K, hs₁, hθ₁, hA, hα, hK, X₁, hX₁m, hX₁1, hX₁os, hae₁⟩ :=
    cubeHarmonicApproximation_holds hd p hpc hp1
  obtain ⟨α', hα'⟩ : ∃ x : ℝ, x = min α 1 := ⟨_, rfl⟩
  have hα'0 : 0 < α' := by rw [hα']; exact lt_min hα one_pos
  have hα'1 : α' ≤ 1 := by rw [hα']; exact min_le_right _ _
  have hα'α : α' ≤ α := by rw [hα']; exact min_le_left _ _
  obtain ⟨β, hβ⟩ : ∃ x : ℝ, x = α' / d := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβ12 : β ≤ 1 / 2 := by
    rw [hβ, div_le_iff₀ (by linarith)]; linarith
  have hβ1 : β ≤ 1 := by linarith
  obtain ⟨tb, htb⟩ : ∃ x : ℝ, x = (d : ℝ) ^ 2 / α' := ⟨_, rfl⟩
  have htb1 : 1 ≤ tb := by
    rw [htb, le_div_iff₀ hα'0]; nlinarith
  have htbβ : (d : ℝ) / (d + tb) ≤ β := by
    have htb0 : 0 < tb := by linarith
    calc (d : ℝ) / (d + tb) ≤ d / tb :=
          div_le_div_of_nonneg_left (by linarith) htb0 (by linarith)
      _ = β := by rw [htb, hβ]; field_simp
  -- the minimal scales of the partition cubes
  obtain ⟨r₁, K₁, hr₁, hK₁, M₁, hM₁m, hM₁0, hM₁os, hae₂⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc 1 le_rfl
  obtain ⟨r₂, K₂, hr₂, hK₂, M₂, hM₂m, hM₂0, hM₂os, hae₃⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc (d : ℝ) hd1
  obtain ⟨r₃, K₃, hr₃, hK₃, M₃, hM₃m, hM₃0, hM₃os, hae₄⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc tb htb1
  -- the density of the cluster in cubes
  have hθp : 0 < LatticeProb.Percolation.theta d p := theta_pos_of_criticalProbability_lt d p hpc
  set κ := LatticeProb.Percolation.theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hΛ24 := le_quadLocality hd0 (capFraction_pos hd0 hκ)
  have hΛ0 : 0 < quadLocality d (capFraction d κ) := lt_of_lt_of_le (by positivity) hΛ24
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (quadLocality d (capFraction d κ))
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hae₅⟩ := hcube 0
  -- the core
  set cS := Real.sqrt ((36 * Real.sqrt d) ^ d) with hcS
  have hcS0 : 0 ≤ cS := Real.sqrt_nonneg _
  obtain ⟨C, r₀, hC, hr₀, hcore⟩ := mesoscopicDegreeTwo_coreD (d := d) (K₁ := 9 ^ d * K₁)
    (K₂ := 9 ^ d * K₂) (κ := κ) (cS := cS) hA hα'0 hα'1 hK (by positivity) (by positivity) hκ
    hcS0
  obtain ⟨c₀, hc₀⟩ : ∃ x : ℝ,
      x = r₀ + quadLocality d (capFraction d κ) + 1296 * d + 1 := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; linarith
  have hc₀r : r₀ ≤ c₀ := by rw [hc₀]; linarith
  have hc₀Λ : quadLocality d (capFraction d κ) ≤ c₀ := by rw [hc₀]; linarith
  have hc₀d : 1296 * (d : ℝ) ≤ c₀ := by rw [hc₀]; linarith
  have hc₀1 : 1 ≤ c₀ := by rw [hc₀]; linarith
  -- the random scale
  obtain ⟨s, hsdef⟩ : ∃ x : ℝ, x = min s₁ (min r₁ (min r₂ (min r₃ s₄))) := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hsdef]; exact lt_min hs₁ (lt_min hr₁ (lt_min hr₂ (lt_min hr₃ hs₄)))
  have hs1 : s ≤ s₁ := by rw [hsdef]; exact min_le_left _ _
  have hs2 : s ≤ r₁ := by rw [hsdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ r₂ := by
    rw [hsdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : s ≤ r₃ := by
    rw [hsdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hs5 : s ≤ s₄ := by
    rw [hsdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have h1os := IsOsBond.mono_exponent hs hs1 hX₁m hX₁os
  have h2os := IsOsBond.mono_exponent hs hs2 hM₁m hM₁os
  have h3os := IsOsBond.mono_exponent hs hs3 hM₂m hM₂os
  have h4os := IsOsBond.mono_exponent hs hs4 hM₃m hM₃os
  have h5os := IsOsBond.mono_exponent hs hs5 hM₄m hM₄os
  have h45 := IsOsBond.max hs (by positivity) (by positivity) hM₃m hM₄m h4os h5os
  have h345 := IsOsBond.max hs (by positivity) (by positivity) hM₂m (hM₃m.max hM₄m) h3os h45
  have h2345 := IsOsBond.max hs (by positivity) (by positivity) hM₁m
    (hM₂m.max (hM₃m.max hM₄m)) h2os h345
  have h12345 := IsOsBond.max hs (by positivity) (by positivity) hX₁m
    (hM₁m.max (hM₂m.max (hM₃m.max hM₄m))) h1os h2345
  have hXos := IsOsBond.const_mul hc₀0 h12345
  refine ⟨s, _, α' / 2, hs, by positivity, by positivity,
    fun ω => c₀ * max (X₁ ω) (max (M₁ ω) (max (M₂ ω) (max (M₃ ω) (M₄ ω)))),
    (hX₁m.max (hM₁m.max (hM₂m.max (hM₃m.max hM₄m)))).const_mul c₀,
    fun ω => mul_nonneg hc₀0.le ((zero_le_one.trans (hX₁1 ω)).trans (le_max_left _ _)), hXos,
    C, ?_⟩
  filter_upwards [hae₁, hae₂, hae₃, hae₄, hae₅, (partition_estimates hd hpc).1] with
    ω h₁ h₂ h₃ h₄ h₅ hP
  intro h R hR u hu r hr hrR
  obtain ⟨mx, hmx⟩ : ∃ x : ℝ, x = max (X₁ ω) (max (M₁ ω) (max (M₂ ω) (max (M₃ ω) (M₄ ω)))) :=
    ⟨_, rfl⟩
  have hR' : 2 * (c₀ * mx) ≤ R := by rw [hmx]; exact hR
  have hr' : c₀ * mx ≤ r := by rw [hmx]; exact hr
  have hmX : X₁ ω ≤ mx := by rw [hmx]; exact le_max_left _ _
  have hm1 : M₁ ω ≤ mx := by rw [hmx]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hm2 : M₂ ω ≤ mx := by
    rw [hmx]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hm3 : M₃ ω ≤ mx := by
    rw [hmx]; exact (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)
  have hm4 : M₄ ω ≤ mx := by
    rw [hmx]; exact (((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)
  have hX1 := hX₁1 ω
  have hmx1 : 1 ≤ mx := hX1.trans hmX
  have hcm : mx ≤ c₀ * mx := le_mul_of_one_le_left (by linarith) hc₀1
  have hr₀X : r₀ * X₁ ω ≤ c₀ * mx := mul_le_mul hc₀r hmX (by linarith) hc₀0.le
  have hRX : r₀ * X₁ ω ≤ R := by linarith
  have hrX : r₀ * X₁ ω ≤ r := by linarith
  have hRq : quadLocality d (capFraction d κ) * max (M₄ ω) 1 ≤ R := by
    have h1 : max (M₄ ω) 1 ≤ mx := max_le hm4 hmx1
    have h2 := mul_le_mul hc₀Λ h1 (zero_le_one.trans (le_max_right _ _)) hc₀0.le
    linarith
  have hR1 : 1 ≤ R := by linarith
  have hRd : 1296 * (d : ℝ) ≤ R := by
    have := mul_le_mul hc₀d hmx1 zero_le_one hc₀0.le
    linarith
  obtain ⟨hsize, hmo₁, hmo₂⟩ := cube_boundsD (ω := ω) hβ0 hβ1 htbβ hR1
    (by linarith) (by linarith) (by linarith)
    (fun m hm => (h₂ m hm).1) (fun m hm => (h₃ m hm).1) (fun m hm => (h₄ m hm).2)
  -- the side bound `S' = 9 R^β`
  have hRβ : R ^ β ≤ Real.sqrt R := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hR1 hβ12
  have hRβ0 : 0 ≤ R ^ β := Real.rpow_nonneg (by linarith) _
  have hS'0 : (0 : ℝ) ≤ 9 * R ^ β := by positivity
  have hS' : Real.sqrt d * (9 * R ^ β) ≤ R / 4 := by
    have hsq : 36 * Real.sqrt d ≤ Real.sqrt R := by
      rw [← Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 36 * Real.sqrt d)]
      apply Real.sqrt_le_sqrt
      have : (36 * Real.sqrt d) * (36 * Real.sqrt d) = 1296 * d := by
        rw [show (36 * Real.sqrt d) * (36 * Real.sqrt d) = 1296 * (Real.sqrt d * Real.sqrt d) by
          ring, Real.mul_self_sqrt (by positivity)]
      linarith
    have hRR : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt (by linarith)
    have h1 : Real.sqrt d * (9 * R ^ β) ≤ Real.sqrt d * (9 * Real.sqrt R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 36 * Real.sqrt d * Real.sqrt R ≤ Real.sqrt R * Real.sqrt R :=
      mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
    have e1 : Real.sqrt d * (9 * Real.sqrt R) = 36 * Real.sqrt d * Real.sqrt R / 4 := by ring
    linarith only [h1, h2, e1, hRR]
  have hS'c : Real.sqrt ((4 * Real.sqrt d * (9 * R ^ β)) ^ d) ≤ cS * R ^ (α' / 2) := by
    have e : (4 * Real.sqrt d * (9 * R ^ β)) ^ d = (36 * Real.sqrt d) ^ d * R ^ α' := by
      rw [show 4 * Real.sqrt d * (9 * R ^ β) = 36 * Real.sqrt d * R ^ β by ring, mul_pow,
        ← Real.rpow_natCast (R ^ β), ← Real.rpow_mul (by linarith), hβ]
      congr 2
      field_simp
    rw [e, Real.sqrt_mul (by positivity), hcS, Real.sqrt_eq_rpow (R ^ α'),
      ← Real.rpow_mul (by linarith)]
    apply le_of_eq
    congr 2
    ring
  exact hcore ω hP h (X₁ ω) (M₄ ω) R (9 * R ^ β) u hX1 hRX hRq hu
    ((h₁ h).mono_exponent hA hK hX1 hα'α) hS'0 hS' hS'c hsize
    hmo₁ hmo₂ (h₅ h) r hrX hrR

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in every dimension `d ≥ 2`**, with no
hypothesis. -/
theorem armstrongDarioMesoscopicDegreeTwo_holds : ArmstrongDarioMesoscopicDegreeTwo :=
  fun _ _ hd _ hpc hp1 => mesoscopicDegreeTwoAt_holds hd hpc hp1

end Rigidity.Proofs.Regularity
