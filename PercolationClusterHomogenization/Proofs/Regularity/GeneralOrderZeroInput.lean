import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicApproximationAS
import PercolationClusterHomogenization.Proofs.Percolation.BondUniqueness

/-!
# The order-zero regularity input in every dimension from Lemma 7.1

`armstrongDarioOrderZero_of_cubeHarmonicApproximation` proves the order-zero input
`LatticeProb.External.ArmstrongDarioOrderZero` (Armstrong–Dario, arXiv:1609.09431v2, Theorem 2
(iii) for `k = 0`) from Lemma 7.1 in every dimension `d ≥ 2`, in the form
`CubeHarmonicApproximation d`. The other ingredients are proved: the almost sure uniqueness of the
infinite cluster (`Rigidity.Percolation.supercritical_bond_uniqueness`), the density of the
infinite cluster in triadic cubes (Dario–Gu, Proposition A.1,
`Rigidity.Proofs.S2.cluster_density_concentration`), which gives `|𝒞_∞ ∩ B_s| ≥ κ s^d` above a
minimal scale (`card_ball_ge_of_clusterCubeDensity_pow`), the decay with constants of
`exists_cubeOrderZeroDecay`, and the Liouville argument `armstrongDarioOrderZero_of_decay`. The
minimal scale is `A² max(𝒳, a max(𝓜, 1), c₁) ≤ O_s(θ)`, `a = 6 √d + 6`, by the stability of `O_s`
under maxima and multiples. The planar form is
`armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

set_option maxHeartbeats 400000 in
/-- **Density of the cluster balls** from the density in cubes: if every triadic cube of size
`3^m ≥ ℓ` inside `B_{Λ 3^m}`, `Λ = 3 √d + 3`, carries `κ 3^{dm}` vertices of `C`, then
`|C ∩ B_s| ≥ κ (2 / a)^d s^d` for `s ≥ a max(ℓ, 1)`, `a = 6 √d + 6`. -/
theorem card_ball_ge_of_clusterCubeDensity_pow {ω : Configuration d} (C : OpenComponent ω)
    {ℓ κ : ℝ} (hκ : 0 ≤ κ) (hcube : ClusterCubeDensity C 0 (3 * Real.sqrt d + 3) ℓ κ) {s : ℝ}
    (hs : (6 * Real.sqrt d + 6) * max ℓ 1 ≤ s) :
    κ * (2 / (6 * Real.sqrt d + 6)) ^ d * s ^ d ≤ (componentEuclideanBall C 0 s).card := by
  classical
  set a := 6 * Real.sqrt d + 6 with hadef
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have ha : 6 ≤ a := by rw [hadef]; linarith
  have ha0 : 0 < a := by linarith
  have h1 : 1 ≤ s / a := by
    rw [le_div_iff₀ ha0]; have := le_max_right ℓ 1; nlinarith
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near h1
  have hℓ : ℓ ≤ 3 ^ m := by
    have h := le_max_left ℓ 1
    have : max ℓ 1 ≤ s / a := by rw [le_div_iff₀ ha0]; linarith
    linarith
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  have hs0 : 0 < s := by linarith [mul_pos ha0 (lt_of_lt_of_le one_pos (le_max_right ℓ 1))]
  have hw : dist (latticeEuclideanEmbedding (0 : Vertex d)) (latticeEuclideanEmbedding 0) +
      Real.sqrt d * 3 ^ m < s := by
    rw [dist_self, zero_add]
    have hsa : Real.sqrt d * (6 * (s / a)) < s := by
      have : Real.sqrt d * 6 < a := by rw [hadef]; linarith
      have hsa0 : 0 < s / a := by positivity
      calc Real.sqrt d * (6 * (s / a)) = Real.sqrt d * 6 * (s / a) := by ring
        _ < a * (s / a) := mul_lt_mul_of_pos_right this hsa0
        _ = s := by field_simp
    calc Real.sqrt d * 3 ^ m ≤ Real.sqrt d * (6 * (s / a)) :=
          mul_le_mul_of_nonneg_left hm2.le hsd
      _ < s := hsa
  have hρ : s ≤ (3 * Real.sqrt d + 3) * 3 ^ m := by
    have e : (3 * Real.sqrt d + 3) * (2 * (s / a)) = s := by
      have hane : a ≠ 0 := ha0.ne'
      have ha2 : 2 * (3 * Real.sqrt d + 3) = a := by rw [hadef]; ring
      calc (3 * Real.sqrt d + 3) * (2 * (s / a)) = 2 * (3 * Real.sqrt d + 3) * s / a := by ring
        _ = a * s / a := by rw [ha2]
        _ = s := by field_simp
    calc s = (3 * Real.sqrt d + 3) * (2 * (s / a)) := e.symm
      _ ≤ (3 * Real.sqrt d + 3) * 3 ^ m := mul_le_mul_of_nonneg_left hm1 (by positivity)
  have h := le_card_filter_of_clusterCubeDensity C 0 hcube hℓ hw hρ (fun _ => True)
    fun _ _ => trivial
  rw [filter_true_of_mem fun _ _ => trivial] at h
  have hm : (3 : ℝ) ^ (d * m) = (3 ^ m) ^ d := by rw [← pow_mul, mul_comm]
  rw [hm] at h
  have hs2 : 2 / a * s ≤ 3 ^ m := by
    calc 2 / a * s = 2 * (s / a) := by ring
      _ ≤ 3 ^ m := hm1
  calc κ * (2 / a) ^ d * s ^ d = κ * (2 / a * s) ^ d := by rw [mul_pow]; ring
    _ ≤ κ * (3 ^ m) ^ d := by gcongr
    _ ≤ _ := h

set_option maxHeartbeats 400000 in
/-- The order-zero decay with constants in dimension `d` (the statement of
`ArmstrongDarioOrderZeroDecay` for one `d`), from Lemma 7.1 in dimension `d`. -/
theorem orderZeroDecay_of_cubeHarmonicApproximation [NeZero d] (hd : 2 ≤ d)
    (hHA : CubeHarmonicApproximation d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration d → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        MeasureTheory.Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s))
          (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω, ∀ R : ℝ, 2 * X ω ≤ R →
              ∀ u : uniqueInfiniteComponent h' → ℝ,
                IsHarmonicInBall (uniqueInfiniteComponent h') R u →
                ∃ c : ℝ, ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                  componentBallL2 (uniqueInfiniteComponent h') 0 r (u - fun _ => c) ≤
                    C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u := by
  obtain ⟨s₁, θ₁, A, α, K, hs₁, hθ₁, hA, hα, hK, X, hXm, hX1, hXos, hae⟩ := hHA p hpc hp1
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₂, C₂, hs₂, hC₂, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (3 * Real.sqrt d + 3)
  obtain ⟨M, hMm, hM0, hMos, hMae⟩ := hcube 0
  set a := 6 * Real.sqrt d + 6 with hadef
  have ha0 : 0 < a := by rw [hadef]; positivity
  set κ := theta d p / 2 * (2 / a) ^ d with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨c₁, K', hc₁, hK', hdecay⟩ := exists_cubeOrderZeroDecay (d := d) hA hα hK hκ
  have hA0 : 0 < A := by linarith
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le one_pos hc₁
  -- the minimal scale and its stretched exponential moment
  set s := min s₁ s₂ with hsdef
  have hs : 0 < s := lt_min hs₁ hs₂
  have h1 := IsOsBond.mono_exponent hs (by rw [hsdef]; exact min_le_left _ _) hXm hXos
  have hM1 := IsOsBond.max hs₂ hC₂ (by positivity) hMm measurable_const hMos
    (isOsBond_const (p := p) (d := d) one_pos hs₂)
  have hMa := IsOsBond.const_mul ha0 hM1
  have hMam : Measurable fun ω => a * max (M ω) 1 := (hMm.max measurable_const).const_mul a
  have h2 := IsOsBond.mono_exponent hs (by rw [hsdef]; exact min_le_right _ _) hMam hMa
  have h12 := IsOsBond.max hs (by positivity) (by positivity) hXm hMam h1 h2
  have h3 := isOsBond_const (p := p) (d := d) hc₁0 hs
  have h12m : Measurable fun ω => max (X ω) (a * max (M ω) 1) := hXm.max hMam
  have h123 := IsOsBond.max hs (by positivity) (by positivity) h12m measurable_const h12 h3
  have hY := IsOsBond.const_mul (by positivity : (0 : ℝ) < A ^ 2) h123
  set Y : Configuration d → ℝ := fun ω => A ^ 2 * max (max (X ω) (a * max (M ω) 1)) c₁
    with hYdef
  have hYm : Measurable Y := (h12m.max measurable_const).const_mul _
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => by
    simp only [hYdef]
    exact mul_nonneg (sq_nonneg _) (hc₁0.le.trans (le_max_right _ _))
  obtain ⟨θY, hθY, hint, hle⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond d p Y s θ := ⟨_, by positivity, hY⟩
  have e : (fun ω => Real.exp (Real.rpow (max (Y ω / θY) 0) s)) =
      fun ω => Real.exp (Real.rpow (Y ω / θY) s) := by
    funext ω
    rw [max_eq_left (div_nonneg (hY0 ω) hθY.le)]
  refine ⟨s, θY, K', hs, hθY, hK', Y, hYm, hY0, by rw [← e]; exact hint, by rw [← e]; exact hle,
    ?_⟩
  -- almost surely
  have hUae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ uniqueInfiniteComponentEvent d :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent d).nullMeasurableSet).2
      (by rw [measure_univ]
          exact Rigidity.Percolation.supercritical_bond_uniqueness.2 d hd p hpc hp1)
  filter_upwards [hUae, hae, hMae] with ω hU hω₁ hω₂
  refine ⟨hU, fun h' => ?_⟩
  have hdens : ∀ t : ℝ, a * max (M ω) 1 ≤ t →
      κ * t ^ d ≤ (componentEuclideanBall (uniqueInfiniteComponent h') 0 t).card := by
    intro t ht
    have := card_ball_ge_of_clusterCubeDensity_pow _ (by positivity) (hω₂ h') ht
    rw [hκdef]; exact this
  exact hdecay (uniqueInfiniteComponent h') (X ω) (a * max (M ω) 1) (hX1 ω) (hω₁ h') hdens

/-- **The order-zero decay with constants in every dimension** (`ArmstrongDarioOrderZeroDecay`)
from Lemma 7.1 in every dimension. -/
theorem armstrongDarioOrderZeroDecay_of_cubeHarmonicApproximation
    (hHA : ∀ (d : ℕ) [NeZero d], 2 ≤ d → CubeHarmonicApproximation d) :
    ArmstrongDarioOrderZeroDecay :=
  fun d _ hd p hpc hp1 => orderZeroDecay_of_cubeHarmonicApproximation hd (hHA d hd) p hpc hp1

/-- **The order-zero regularity input of Armstrong–Dario** (`ArmstrongDarioOrderZero`, Theorem 2
(iii) for `k = 0`, every `d ≥ 2`) from Lemma 7.1 in every dimension. -/
theorem armstrongDarioOrderZero_of_cubeHarmonicApproximation
    (hHA : ∀ (d : ℕ) [NeZero d], 2 ≤ d → CubeHarmonicApproximation d) :
    LatticeProb.External.ArmstrongDarioOrderZero :=
  armstrongDarioOrderZero_of_decay (armstrongDarioOrderZeroDecay_of_cubeHarmonicApproximation hHA)

end Rigidity.Proofs.Regularity
