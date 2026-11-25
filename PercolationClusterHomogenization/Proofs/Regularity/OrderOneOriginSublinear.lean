import PercolationClusterHomogenization.Proofs.Regularity.GeneralMesoscopicDegreeTwo

/-!
# Regularity of order one at the origin from (7.18) and the sublinearity of the correctors

`CorrectorSublinearL2At d p` is the bound (1.18) of Armstrong and Dario (arXiv:1609.09431v2), the
case `k = 1` of Theorem 2 (ii), for bond percolation of parameter `p` in dimension `d`: almost
surely, for every slope `q` there is `u ∈ 𝒜_1(𝒞_∞)` whose corrector `u - q · x` satisfies
`‖u - q · x‖_{L̲²(𝒞_∞ ∩ B_r)} ≤ K |q|₁ r^{1-δ}` for every `r ≥ 𝒳`, with `𝒳 ≤ O_s(θ)`; its planar
case is `PlanarCorrectorSublinearL2Two`.

`orderOneOrigin_of_mesoscopicDegreeTwoAt_of_sublinear` proves Theorem 2 (iii) at `k = 1` at the
origin for one dimension and one law from (7.18) at `k = 2` and (1.18), by the endpoint iteration
`exists_forall_le_of_orderOneEndpoint`: the functions `u` of (1.18) for the slopes `eᵢ` lift the
affine functions with relative error `ε` in `L̲²` on `B_t` above the scale `(C √d / ε + 1)^{1/δ}`
(`orderOneEndpointData_clusterL2`, the endpoint data of `orderOneEndpointData_cluster` with the
lift bound in `L̲²`). With (7.18) at `k = 2` in every dimension (`mesoscopicDegreeTwoAt_holds`)
this gives `Rigidity.External.ArmstrongDarioOrderOneOrigin` from (1.18) alone
(`armstrongDarioOrderOneOrigin_of_correctorSublinear`): the corrector inputs
`CorrectorQuantitativeInput` and `SupercriticalBondCorrectorInput` of
`armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo` are not used, the source deducing
Theorem 2 (iii) from Lemma 7.3 and Theorem 2 (ii) by the argument of Armstrong, Kuusi and Mourrat,
Proposition 3.1.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ} {ω : Configuration d}

/-- **Armstrong–Dario, (1.18)** (Theorem 2 (ii) at `k = 1` in `L̲²`) for one dimension and one law. -/
def CorrectorSublinearL2At (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∃ s δ θ K : ℝ, 0 < s ∧ 0 < δ ∧ 0 < θ ∧ 0 ≤ K ∧
    ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin d → ℝ,
        ∃ u : uniqueInfiniteComponent h → ℝ,
          u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 ∧
          ∀ r : ℝ, X ω ≤ r →
            componentBallL2 (uniqueInfiniteComponent h) 0 r
                (fun x => u x - componentSlope (uniqueInfiniteComponent h) q x) ≤
              K * (∑ i, |q i|) * r ^ (1 - δ)

theorem componentBallL2_zero_fun (C : OpenComponent ω) (z : Vertex d) (r : ℝ) :
    componentBallL2 C z r (fun _ => 0) = 0 := by
  simp [componentBallL2]

/-- The normalized norm of a finite linear combination. -/
theorem componentBallL2_sum_mul_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (f : ι → C → ℝ) :
    componentBallL2 C z r (fun x => ∑ i ∈ s, c i * f i x) ≤
      ∑ i ∈ s, |c i| * componentBallL2 C z r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [componentBallL2_zero_fun]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : (fun x => ∑ i ∈ insert a s, c i * f i x) =
        c a • f a + fun x => ∑ i ∈ s, c i * f i x := by
      funext x
      rw [Finset.sum_insert ha]
      rfl
    rw [e]
    refine (Rigidity.Proofs.S2.componentBallL2_add_le C z r _ _).trans ?_
    rw [componentBallL2_smul]
    linarith

/-- **The endpoint data on the cluster with the lift bound in `L̲²`**: the data of
`orderOneEndpointData_cluster` from `‖gᵢ - xᵢ‖_{L̲²(C ∩ B_t)} ≤ ε t / √d`. -/
theorem orderOneEndpointData_clusterL2 (C : OpenComponent ω) (hd : 0 < d) {κ ℓc X R A δ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓc κ)
    (hX : quadLocality d (capFraction d κ) * max ℓc 1 ≤ X)
    {g : Fin d → C → ℝ} (hgharm : ∀ i, g i ∈ harmonicGrowthSpace C 1)
    (hg : ∀ t, X ≤ t → t ≤ R → ∀ i,
      componentBallL2 C 0 t (fun x => g i x - latticeEuclideanEmbedding x.val i) ≤
        ε / Real.sqrt d * t)
    (hmeso : ∀ r w, 2 * X ≤ r → r ≤ R → ClusterBallHarmonic C r w → ∀ v, X ≤ v → v ≤ r / 2 →
      ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) v w ≤
        A * (v / r) ^ 3 * ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) r w +
          A * v ^ (-δ) * (v / r) * componentBallSeminorm C 0 r w) :
    OrderOneEndpointData (componentBallSeminorm C 0) (clusterHarmonicQuadratic C)
      (clusterAffineMap C) (clusterLiftMap C g) (clusterQuadMap C) affineSize quadSize
      (ClusterBallHarmonic C) X R A δ (Real.sqrt (clusterVolumeConst d κ)) ((d : ℝ) / 2) d
      (clusterPolyConst d κ) ε := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have D₀ := orderOneEndpointData_cluster C hd (ε := Real.sqrt d) (g := fun _ _ => 0) (R := R)
    (A := A) (δ := δ) hκ hsd.le hcube hX (fun _ => const_mem_harmonicGrowthSpace C 1 0)
    (fun t _ _ i x hx => by
      have hxt := norm_lt_of_mem_componentEuclideanBall hx
      have h1 := PiLp.norm_apply_le (latticeEuclideanEmbedding x.val) i
      rw [Real.norm_eq_abs] at h1
      rw [div_self hsd.ne', one_mul, zero_sub, abs_neg]
      linarith) hmeso
  exact
    { D₀ with
      lift_le := by
        intro t ht htR ℓ
        rw [componentBallSeminorm_apply]
        have e : clusterLiftMap C g ℓ - clusterAffineMap C ℓ =
            fun x => ∑ i, ℓ.2 i * (g i x - latticeEuclideanEmbedding x.val i) := by
          funext x
          show (ℓ.1 + ∑ i, ℓ.2 i * g i x) - (ℓ.1 + inner ℝ ℓ.2 (latticeEuclideanEmbedding x.val)) = _
          rw [inner_eq_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e]
        refine (componentBallL2_sum_mul_le C 0 t Finset.univ _ _).trans ?_
        have h1 : ∑ i, |ℓ.2 i| * componentBallL2 C 0 t
            (fun x => g i x - latticeEuclideanEmbedding x.val i) ≤
            ∑ i, |ℓ.2 i| * (ε / Real.sqrt d * t) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg t ht htR i) (abs_nonneg _)
        have h2 : ∑ i, |ℓ.2 i| * (ε / Real.sqrt d * t) =
            (∑ i, |ℓ.2 i|) * (ε / Real.sqrt d * t) := (Finset.sum_mul _ _ _).symm
        have h3 := sum_abs_le_sqrt_mul_norm ℓ.2
        have hX0 : 0 < X := by
          have hδc := capFraction_pos hd hκ
          have hΛ := le_quadLocality hd hδc
          have hm : (1 : ℝ) ≤ max ℓc 1 := le_max_right _ _
          have : 0 < quadLocality d (capFraction d κ) * max ℓc 1 :=
            mul_pos (lt_of_lt_of_le (by positivity) hΛ) (by linarith)
          linarith
        have ht0 : 0 < t := hX0.trans_le ht
        have h4 : (∑ i, |ℓ.2 i|) * (ε / Real.sqrt d * t) ≤
            (Real.sqrt d * ‖ℓ.2‖) * (ε / Real.sqrt d * t) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
        have h5 : (Real.sqrt d * ‖ℓ.2‖) * (ε / Real.sqrt d * t) = ε * (t * ‖ℓ.2‖) := by
          field_simp
        have h6 : ε * (t * ‖ℓ.2‖) ≤ ε * affineSize t ℓ := by
          unfold affineSize
          exact mul_le_mul_of_nonneg_left (by linarith only [abs_nonneg ℓ.1]) hε
        linarith only [h1, h2, h4, h5, h6]
      harm_sub := by
        intro r w ℓ hw z hz hzn
        rw [componentLaplacian_sub, hw z hz hzn,
          ((mem_harmonicGrowthSpace_iff C 1 _).1
            (clusterLiftMap_mem_harmonicGrowthSpace C hgharm ℓ)).1 z, sub_zero] }

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in one dimension and for one
law**, from (7.18) at `k = 2` and the sublinearity (1.18) of the correctors. -/
theorem orderOneOrigin_of_mesoscopicDegreeTwoAt_of_sublinear {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hmeso : MesoscopicDegreeTwoAt d p)
    (hsub : CorrectorSublinearL2At d p) :
    ∃ s C₀ : ℝ, 0 < s ∧ 0 < C₀ ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s C₀ ∧
      ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∃ φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1,
            ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
              componentBallL2 (uniqueInfiniteComponent h) 0 r (u - φ) ≤
                C * (r / R) ^ 2 * componentBallL2 (uniqueInfiniteComponent h) 0 R u := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rcases (theta_nonneg d p).eq_or_lt with hθ0 | hθp
  · refine ⟨1, 1 * 3 ^ ((1 : ℝ) / 1), one_pos, by positivity, fun _ => 1, measurable_const,
      fun _ => zero_le_one, isOsBond_const one_pos one_pos, 0, ?_⟩
    filter_upwards [ae_not_hasUniqueInfiniteOpenComponent_of_theta_eq_zero p hθ0.symm] with ω hω h
    exact absurd h hω
  obtain ⟨s₁, C₁, δ, hs₁, hC₁, hδ, X₁, hX₁m, hX₁0, hX₁os, A₀, hae₁⟩ := hmeso
  set κ := theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  set Λ := quadLocality d (capFraction d κ) with hΛdef
  have hΛ24 := le_quadLocality hd0 (capFraction_pos hd0 hκ)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd0)
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨s₂, C₂, hs₂, hC₂, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) Λ
  obtain ⟨M₂, hM₂m, hM₂0, hM₂os, hae₂⟩ := hcube 0
  obtain ⟨s₃, δ₃, θ₃, C₃, hs₃, hδ₃, hθ₃, hC₃, M₃, hM₃m, hM₃0, hM₃os, hae₃⟩ := hsub
  -- deterministic constants
  set K := clusterVolumeConst d κ with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef, clusterVolumeConst]; positivity
  set CV := Real.sqrt K with hCV
  set γ : ℝ := (d : ℝ) / 2 with hγ
  set CL := clusterPolyConst d κ with hCLdef
  have hCL : 0 ≤ CL := by
    have h1 := capFraction_pos hd0 hκ
    have h2 := quadLowerConst_pos hd0 hκ h1
    rw [hCLdef, clusterPolyConst]
    positivity
  set A := Real.sqrt K * max A₀ 1 with hAdef
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (le_max_right _ _))
  set θ := 1 / (4 * A + 2) with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hθ2 : θ ≤ 1 / 2 := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hAθ : A * θ ≤ 1 / 4 := by
    rw [hθdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set B := endpointSlopeConst A CV γ CL θ with hBdef
  have hB : 0 ≤ B := by
    rw [hBdef, endpointSlopeConst]
    have : 0 ≤ (1 / θ) ^ γ := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ CV := Real.sqrt_nonneg _
    positivity
  set ε := 1 / (4 * B + 2 * CL + 1) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]; linarith
  have hεB : ε * B ≤ 1 / 4 := by
    rw [hεdef, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hCLε : CL * ε ≤ 1 / 2 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set T := (C₃ * Real.sqrt d / ε + 1) ^ (1 / δ₃) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  set c₀ := 2 * Λ + T + 2 with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  -- the random scale
  set s := min s₁ (min s₂ s₃) with hsdef
  have hs : 0 < s := lt_min hs₁ (lt_min hs₂ hs₃)
  have hs1 : s ≤ s₁ := min_le_left _ _
  have hs2 : s ≤ s₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ s₃ := (min_le_right _ _).trans (min_le_right _ _)
  have h1os := IsOsBond.mono_exponent hs hs1 hX₁m hX₁os
  have h2os := IsOsBond.mono_exponent hs hs2 hM₂m hM₂os
  have h3os := IsOsBond.mono_exponent hs hs3 hM₃m hM₃os
  have h4os := isOsBond_const (d := d) (p := p) one_pos hs
  have h34 := IsOsBond.max hs (by positivity) (by positivity) hM₃m measurable_const h3os h4os
  have h234 := IsOsBond.max hs (by positivity) (by positivity) hM₂m
    (hM₃m.max measurable_const) h2os h34
  have h1234 := IsOsBond.max hs (by positivity) (by positivity) hX₁m
    (hM₂m.max (hM₃m.max measurable_const)) h1os h234
  have hXos := IsOsBond.const_mul hc₀0 h1234
  set Xs : Configuration d → ℝ := fun ω => c₀ * max (X₁ ω) (max (M₂ ω) (max (M₃ ω) 1)) with hXs
  refine ⟨s, _, hs, by positivity, Xs,
    (hX₁m.max (hM₂m.max (hM₃m.max measurable_const))).const_mul c₀, fun ω => ?_, hXos,
    singlePolynomialConst CV (2 * CL * (1 + ε)) γ 1 * endpointFitConst A δ CV γ d CL θ, ?_⟩
  · have : 0 ≤ max (X₁ ω) (max (M₂ ω) (max (M₃ ω) 1)) :=
      (hX₁0 ω).trans (le_max_left _ _)
    exact mul_nonneg hc₀0.le this
  filter_upwards [hae₁, hae₂, hae₃] with ω h₁ h₂ h₃
  intro h R hR u hu
  set Cl := uniqueInfiniteComponent h with hCl
  have hc := h₂ h
  set m := max (X₁ ω) (max (M₂ ω) (max (M₃ ω) 1)) with hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmX₁ : X₁ ω ≤ m := le_max_left _ _
  have hmM₂ : max (M₂ ω) 1 ≤ m :=
    max_le ((le_max_left _ _).trans (le_max_right _ _))
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have hmM₃ : M₃ ω ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hXω : Xs ω = c₀ * m := rfl
  have hc₀1 : 1 ≤ c₀ := by rw [hc₀]; linarith
  have hmc : m ≤ c₀ * m := le_mul_of_one_le_left (by linarith) hc₀1
  have hcm : c₀ ≤ Xs ω := by rw [hXω]; exact le_mul_of_one_le_right hc₀0.le hm1
  have hXX₁ : X₁ ω ≤ Xs ω := by rw [hXω]; linarith only [hmX₁, hmc]
  have hXM₃ : M₃ ω ≤ Xs ω := by rw [hXω]; linarith only [hmM₃, hmc]
  have hXT : T ≤ Xs ω := by linarith only [hcm, hc₀, hΛ0]
  have hX2 : 2 ≤ Xs ω := by linarith only [hcm, hc₀, hΛ0, hT0]
  have hXΛ : 2 * Λ * max (M₂ ω) 1 ≤ Xs ω := by
    rw [hXω]
    have h1 : 2 * Λ * max (M₂ ω) 1 ≤ 2 * Λ * m := mul_le_mul_of_nonneg_left hmM₂ (by positivity)
    have h2 : 2 * Λ * m ≤ c₀ * m := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hmax0 : 1 ≤ max (M₂ ω) 1 := le_max_right _ _
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd0)
  have hΛ1 : 1 ≤ Λ * max (M₂ ω) 1 := by
    have : Λ ≤ Λ * max (M₂ ω) 1 := le_mul_of_one_le_right hΛ0.le hmax0
    linarith only [this, hΛ24, hsd1]
  have hXΛ1 : Λ * max (M₂ ω) 1 ≤ Xs ω := by linarith only [hXΛ, hΛ1]
  have hXR : 2 * Xs ω ≤ R := hR
  have hX1 : 1 ≤ Xs ω := by linarith
  -- geometry of the balls of the cluster
  have hcube24 := hc.of_le Cl 0 hΛ24
  have h24 : 24 * Real.sqrt d * max (M₂ ω) 1 ≤ Λ * max (M₂ ω) 1 :=
    mul_le_mul_of_nonneg_right hΛ24 (by linarith)
  have h6 : 6 * Real.sqrt d * max (M₂ ω) 1 ≤ 24 * Real.sqrt d * max (M₂ ω) 1 := by
    have : 0 ≤ Real.sqrt d * max (M₂ ω) 1 := mul_nonneg hsd.le (by linarith)
    linarith
  have hvol := clusterBallVolumeComparison_of_clusterCubeDensity Cl 0 R hd0 hκ hcube24
  have hcapR := clusterBallCapDensity_of_clusterCubeDensity Cl 0 R hd0 hκ hcube24
  -- the lifts of the affine functions from (1.18)
  choose g hg using fun i : Fin d => h₃ h (Pi.single i 1)
  have hgharm : ∀ i, g i ∈ harmonicGrowthSpace Cl 1 := fun i => (hg i).1
  have hglift : ∀ t, Xs ω ≤ t → t ≤ R → ∀ i,
      componentBallL2 Cl 0 t (fun x => g i x - latticeEuclideanEmbedding x.val i) ≤
        ε / Real.sqrt d * t := by
    intro t ht _ i
    have ht0 : 0 < t := by linarith
    have ht1 : 1 ≤ t := by linarith
    have hb := (hg i).2 t (hXM₃.trans ht)
    simp only [sum_abs_single, mul_one] at hb
    have he : (fun x => g i x - componentSlope Cl (Pi.single i 1) x) =
        fun x => g i x - latticeEuclideanEmbedding x.val i := by
      funext x
      rw [componentSlope, sum_single_mul]
      rfl
    rw [he] at hb
    refine hb.trans ?_
    -- `C₃ t^{1-δ} ≤ ε t / √d` above `T`
    have hTt : T ≤ t := hXT.trans ht
    have hδ0 : 0 < δ₃ := hδ₃
    have hpow : C₃ * Real.sqrt d / ε + 1 ≤ t ^ δ₃ := by
      have h1 : ((C₃ * Real.sqrt d / ε + 1) ^ (1 / δ₃)) ^ δ₃ = C₃ * Real.sqrt d / ε + 1 := by
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ0.ne', Real.rpow_one]
      rw [← h1]
      exact Real.rpow_le_rpow (by positivity) hTt hδ0.le
    have htδ : t ^ (1 - δ₃) * t ^ δ₃ = t := by
      rw [← Real.rpow_add ht0, sub_add_cancel, Real.rpow_one]
    have hpos : 0 < t ^ δ₃ := Real.rpow_pos_of_pos ht0 _
    have h2 : C₃ * Real.sqrt d ≤ ε * t ^ δ₃ := by
      have := mul_le_mul_of_nonneg_left hpow hε.le
      have e : ε * (C₃ * Real.sqrt d / ε + 1) = C₃ * Real.sqrt d + ε := by field_simp
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hsd]
    have h3 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht0.le (1 - δ₃))
    calc C₃ * t ^ (1 - δ₃) * Real.sqrt d = t ^ (1 - δ₃) * (C₃ * Real.sqrt d) := by ring
      _ ≤ t ^ (1 - δ₃) * (ε * t ^ δ₃) := h3
      _ = ε * t := by rw [mul_left_comm, htδ]
  -- the mesoscopic estimate in the normalized norms
  have hmeso' : ∀ r w, 2 * Xs ω ≤ r → r ≤ R → ClusterBallHarmonic Cl r w →
      ∀ v, Xs ω ≤ v → v ≤ r / 2 →
        ballExcess (componentBallSeminorm Cl 0) (clusterHarmonicQuadratic Cl) v w ≤
          A * (v / r) ^ 3 * ballExcess (componentBallSeminorm Cl 0) (clusterHarmonicQuadratic Cl)
            r w + A * v ^ (-δ) * (v / r) * componentBallSeminorm Cl 0 r w := by
    intro r w hr hrR hw v hv hvr
    have hv0 : 0 < v := by linarith
    have h7 := h₁ h r (by linarith) w hw v (hXX₁.trans hv) hvr
    have hcardv := (hcapR v (by linarith) (by linarith)).1
    have hvolv : ClusterBallVolumeComparison Cl 0 (6 * Real.sqrt d * max (M₂ ω) 1) R
        ((5 * (6 * Real.sqrt d)) ^ d / κ) := hvol
    have := ballExcess_le_of_clusterBallVolumeL2 Cl hK0 hvolv (by linarith) (by linarith) hrR hv0
      hcardv h7
    rw [hAdef]
    exact this
  have hD := orderOneEndpointData_clusterL2 Cl hd0 (δ := δ) (A := A) hκ hε.le hc hXΛ1 hgharm
    hglift hmeso'
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  obtain ⟨ℓ, hℓ⟩ := exists_forall_le_of_orderOneEndpoint hD hX1 hA (Real.sqrt_nonneg _) hγ0
    (Nat.cast_pos.2 hd0) hCL hδ hθ hθ2 hAθ hε.le hε1 hεB hCLε hXR hu
  refine ⟨clusterLiftMap Cl g ℓ, clusterLiftMap_mem_harmonicGrowthSpace Cl hgharm ℓ, ?_⟩
  intro r hr hrR
  have := hℓ r hr hrR
  simpa only [componentBallSeminorm_apply] using this


/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in every dimension**, from the
sublinearity (1.18) of the correctors; (7.18) at `k = 2` is `mesoscopicDegreeTwoAt_holds`. -/
theorem armstrongDarioOrderOneOrigin_of_correctorSublinear
    (hsub : ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
      criticalProbability d < (p : ℝ) → (p : ℝ) < 1 → CorrectorSublinearL2At d p) :
    ArmstrongDarioOrderOneOrigin := fun d _ hd p hpc hp1 =>
  orderOneOrigin_of_mesoscopicDegreeTwoAt_of_sublinear hd hpc hp1
    (mesoscopicDegreeTwoAt_holds hd hpc hp1) (hsub d hd p hpc hp1)

end Rigidity.Proofs.Regularity
