import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderOneHolds
import PercolationClusterHomogenization.Proofs.Regularity.PlanarStretchedScales
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseBoundTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarRestrictBadOs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorOsc

/-!
# (1.22) on the infinite cluster of `ℤᵈ`: the oscillation of the correctors on the balls

`CorrectorOscSublinear d` is (1.22) of Armstrong and Dario (arXiv:1609.09431v2) in the oscillation
form, in dimension `d`: for `R ≥ 1` there is a measurable `Z_R ≥ 0` of class `O_s(C R^{1-δ})`
such that almost surely, for every corrected plane `ℓ` of slope `q` and all `a, b` of the infinite
cluster in the ball of radius `R`, `|χ(a) - χ(b)| ≤ |q|₁ Z_R` with `χ = ℓ - q · x`.
`correctorOscSublinear_holds` proves it in every dimension `d ≥ 2`, with no hypothesis:

* `exists_isOsBond_scale_le_three_os`: the maximum of the local minimal scales over the triadic
  boxes, with a minimal scale of class `O_s` (a union bound);
* `exists_corrector_sup_os`: the uniform bound `|χ(x)| ≤ C |q|₁ E^{1-η}` on `{|x_i| ≤ E}`,
  `E = 3^m`, above a minimal scale of class `O_s`, from (1.18) with a minimal scale of class `O_s`
  (`correctorSublinearL2At_holds`) and `abs_corrector_le_of_scales`;
* a corrected plane differs from the function of (1.18) of the same slope by a constant
  (`supercriticalBondCorrectorInput_holds`), and `Z_R = 18 C R^{1-η} max(𝒳, 1)`.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal

variable {d : ℕ}

/-- **The maximum of the local minimal scales over the triadic boxes, of class `O_s`.** -/
theorem exists_isOsBond_scale_le_three_os [NeZero d] {p : unitInterval}
    {Y : Vertex d → Configuration d → ℝ} {s θ γ : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hγ : 0 < γ)
    (hYm : ∀ z, Measurable (Y z))
    (hYi : ∀ z, Integrable (fun ω => Real.exp (Real.rpow (Y z ω / θ) s)) (latticeBondLaw d p))
    (hYb : ∀ z, (∫ ω, Real.exp (Real.rpow (Y z ω / θ) s) ∂latticeBondLaw d p) ≤ 2) :
    ∃ r θ' : ℝ, 0 < r ∧ 0 < θ' ∧ ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
      IsOsBond d p X r θ' ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ k : ℕ, X ω < 3 ^ k → ∀ z ∈ triScaleBox d k,
        Y z ω ≤ (3 : ℝ) ^ ((k : ℝ) * γ) := by
  set E : ℕ → Set (Configuration d) := fun k =>
    ⋃ z ∈ triScaleBox d k, {ω | (3 : ℝ) ^ ((k : ℝ) * γ) < Y z ω} with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    Finset.measurableSet_biUnion _ fun z _ => measurableSet_lt measurable_const (hYm z)
  set c : ℝ := θ⁻¹ ^ s with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨K, hK, hKb⟩ := exists_rpow_mul_exp_le (a := (d : ℝ)) hc0 (mul_pos hγ hs)
  have hP : ∀ k : ℕ, latticeBondLaw d p (E k) ≤ ENNReal.ofReal (2 * 27 ^ d * K) *
      ENNReal.ofReal (Real.exp (-(c / 2) * ((3 : ℝ) ^ k) ^ (γ * s))) := by
    intro k
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine (measure_biUnion_le_card_mul _ _ (b := 2 * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s)))
      fun z _ => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · refine (measure_lt_le_of_exp_rpow_moment (latticeBondLaw d p) hθ hs (hYi z) (hYb z)
        (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_of_eq ?_)) (by norm_num)
      rw [Real.div_rpow (by positivity) hθ.le, ← Real.rpow_natCast (3 : ℝ) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), hc,
        Real.inv_rpow hθ.le]
      ring_nf
    · have hcard := card_triScaleBox_le (d := d) k
      have hd3 : ((3 : ℝ) ^ d) ^ k = ((3 : ℝ) ^ k) ^ (d : ℝ) := by
        rw [Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
      have h27 : (3 : ℝ) ^ (3 * d) = 27 ^ d := by
        rw [pow_mul]; norm_num
      have hx1 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
      have h := hKb ((3 : ℝ) ^ k) hx1
      calc ((triScaleBox d k).card : ℝ) * (2 * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s)))
          ≤ (3 : ℝ) ^ (3 * d) * ((3 : ℝ) ^ d) ^ k *
              (2 * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s))) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * 27 ^ d * (((3 : ℝ) ^ k) ^ (d : ℝ) * Real.exp (-c * ((3 : ℝ) ^ k) ^ (γ * s))) := by
            rw [hd3, h27]; ring
        _ ≤ 2 * 27 ^ d * (K * Real.exp (-(c / 2) * ((3 : ℝ) ^ k) ^ (γ * s))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 * 27 ^ d * K * Real.exp (-(c / 2) * ((3 : ℝ) ^ k) ^ (γ * s)) := by ring
  obtain ⟨θ', hθ', X, hXm, hX0, hXos, hXae⟩ := exists_isOsBond_of_events E hEm
    ENNReal.ofReal_ne_top (mul_pos hγ hs) (by positivity) hP
  refine ⟨γ * s, θ', mul_pos hγ hs, hθ', X, hXm, hX0, hXos, ?_⟩
  filter_upwards [hXae] with ω hω k hk z hz
  have h := hω k hk
  simp only [hE, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at h
  exact h z hz

/-- **The uniform bound of the correctors above a minimal scale of class `O_s`** (Armstrong and
Dario, Remark after (1.19)), in every dimension `d ≥ 2`. -/
theorem exists_corrector_sup_os [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ s θ η Cs : ℝ, 0 < s ∧ 0 < θ ∧ 0 < η ∧ η ≤ 1 / 4 ∧ 0 ≤ Cs ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin d → ℝ,
        ∃ u : uniqueInfiniteComponent h → ℝ, u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 ∧
          ∀ m : ℕ, X ω ≤ 3 ^ m → ∀ x : uniqueInfiniteComponent h,
            (∀ i, |((x.val i : ℤ) : ℝ)| ≤ 3 ^ m) →
            |u x - componentSlope (uniqueInfiniteComponent h) q x| ≤
              Cs * (∑ i, |q i|) * ((3 : ℝ) ^ m) ^ (1 - η) := by
  obtain ⟨s₁, δ₁, θ₁, K, hs₁, hδ₁, hθ₁, hK, X₁, hX₁m, -, hX₁os, hae₁⟩ :=
    correctorSublinearL2At_holds hd hpc hp1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₁ 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδ₁ one_pos
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
  have hδδ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = δ / (2 * d) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η * d = δ := by rw [hηdef]; field_simp
  have h3η : 3 * η ≤ δ := by nlinarith
  have hη4 : η ≤ 1 / 4 := by nlinarith
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = η / (2 * d + 1) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  have hγη : γ * (2 * d + 1) = η := by rw [hγdef]; field_simp
  have hγle : γ ≤ η := by rw [hγdef]; exact div_le_self hη0.le (by linarith)
  have ht₀ : (1 : ℝ) ≤ d / γ := by rw [le_div_iff₀ hγ0]; linarith
  have hdt : (d : ℝ) / (d + d / γ) ≤ γ := by
    have e : γ * ((d : ℝ) / γ) = d := mul_div_cancel₀ _ hγ0.ne'
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨s₃, θ₃, C₀, hs₃, hθ₃, hC₀, Y, hYm, -, hYi, hYb, hae₃⟩ :=
    exists_all_centres_constant_approximation hd p hpc hp1
  obtain ⟨rB, θB, hrB, hθB, XB, hXBm, -, hXBos, haeB⟩ :=
    exists_isOsBond_scale_le_three_os hs₃ hθ₃ hγ0 hYm hYi hYb
  obtain ⟨s₅, C₅, hs₅, hC₅, M₅, hM₅m, -, hM₅os, hM₅ae⟩ :=
    Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc ((d : ℝ) / γ) ht₀
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) ((d : ℝ) * (14 * 3 ^ (d + 1) + 1) + 1)
  obtain ⟨M₄, hM₄m, -, hM₄os, hM₄ae⟩ := hcube 0
  set κ : ℝ := theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  -- the minimal scale
  have hM₄os' := IsOsBond.const_mul (c := (3 : ℝ) ^ (d + 1)) (by positivity) hM₄os
  obtain ⟨θa, hθa, ha⟩ := exists_isOsBond_max hs₁ hrB hθ₁ hθB hX₁m hXBm hX₁os hXBos
  obtain ⟨θb, hθb, hb⟩ := exists_isOsBond_max hs₅ hs₄ hC₅ (by positivity) hM₅m
    (measurable_const.mul hM₄m) hM₅os hM₄os'
  obtain ⟨θc, hθc, hc⟩ := exists_isOsBond_max (lt_min hs₁ hrB) (lt_min hs₅ hs₄) hθa hθb
    (hX₁m.max hXBm) (hM₅m.max (measurable_const.mul hM₄m)) ha hb
  set s := min (min s₁ rB) (min s₅ s₄) with hs
  have hs0 : 0 < s := lt_min (lt_min hs₁ hrB) (lt_min hs₅ hs₄)
  have hconst := isOsBond_const (d := d) (p := p)
    (by positivity : (0 : ℝ) < max 100 (3 ^ (d + 1))) hs0
  obtain ⟨θd, hθd, hd'⟩ := exists_isOsBond_max hs0 hs0 hθc (by positivity)
    ((hX₁m.max hXBm).max (hM₅m.max (measurable_const.mul hM₄m))) measurable_const hc hconst
  refine ⟨_, θd, η,
    2 * d * 21 ^ d * (10 * 13 ^ d * C₀ *
          (15 * d * Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * K + 1) + 1) +
        Real.sqrt (2 * 21 ^ d * (33 * d) ^ d * (15 * d * K) ^ 2) +
        Real.sqrt 2 * d * (2 * d * 21 ^ d * (10 * 13 ^ d * C₀ *
          (15 * d * Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * K + 1) + 1)),
    lt_min hs0 hs0, hθd, hη0, hη4, by positivity,
    fun ω => max (max (max (X₁ ω) (XB ω)) (max (M₅ ω) (3 ^ (d + 1) * M₄ ω)))
      (max 100 (3 ^ (d + 1))),
    ((hX₁m.max hXBm).max (hM₅m.max (measurable_const.mul hM₄m))).max measurable_const,
    fun ω => (by positivity : (0 : ℝ) ≤ max 100 (3 ^ (d + 1))).trans (le_max_right _ _),
    hd', ?_⟩
  filter_upwards [hae₁, hae₃, haeB, hM₅ae, hM₄ae, ae_partitionEvent hd hpc] with
    ω hω₁ hω₃ hωB hω₅ hω₄ hP
  intro h q
  obtain ⟨u, hu, hL2⟩ := hω₁ h q
  refine ⟨u, hu, fun m hm x hx => ?_⟩
  obtain ⟨-, hω₃'⟩ := hω₃
  have hLip := hω₃' h
  have hinf := uniqueInfiniteComponent_infinite h
  have hX₁ : X₁ ω ≤ 3 ^ m :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hm
  have hXB : XB ω ≤ 3 ^ m :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hm
  have hM₅ : M₅ ω ≤ 3 ^ m :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hm
  have hM₄ : 3 ^ (d + 1) * M₄ ω ≤ 3 ^ m :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hm
  have hE100 : (100 : ℝ) ≤ 3 ^ m :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmd : d + 1 ≤ m := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1
    (((le_max_right _ _).trans (le_max_right _ _)).trans hm)
  exact abs_corrector_le_of_scales hd hP (uniqueInfiniteComponent h) hinf q u hu hK hC₀ hκ hδδ
    h2η h3η hη4 hγ0 hγη hγle hdt hL2 (Y := fun z => Y z ω) (fun z => hLip z) hmd
    (fun z hz => hωB (m + 1) (hXB.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))) z hz)
    ((hω₅ (m + 3) (hM₅.trans (pow_le_pow_right₀ (by norm_num) (by omega)))).2)
    (hω₄ h) hM₄ hX₁ hE100 x hx

/-- **Armstrong–Dario, (1.22), in dimension `d`**, in the oscillation form: the correctors of the
corrected planes oscillate on `𝒞_∞ ∩ B_R` by at most `|q|₁ Z_R`, `Z_R ≤ O_s(C R^{1-δ})`. -/
def CorrectorOscSublinear (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s δ C : ℝ, 0 < s ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ Z : Configuration d → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond d p Z s (C * R ^ (1 - δ)) ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ (q : Fin d → ℝ)
          (ℓ : uniqueInfiniteComponent h → ℝ), IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
          ∀ a b : uniqueInfiniteComponent h,
            ‖latticeEuclideanEmbedding a.val‖ < R → ‖latticeEuclideanEmbedding b.val‖ < R →
            |(ℓ a - ∑ i, q i * (a.val i : ℝ)) - (ℓ b - ∑ i, q i * (b.val i : ℝ))| ≤
              (∑ i, |q i|) * Z ω

/-- `max(R, max(X, 1))^{1-η} ≤ R^{1-η} max(X, 1)` for `R ≥ 1`. -/
theorem max_rpow_le_mul {R X η : ℝ} (hR : 1 ≤ R) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    (max R (max X 1)) ^ (1 - η) ≤ R ^ (1 - η) * max X 1 := by
  have hX1 : 1 ≤ max X 1 := le_max_right _ _
  have h1 : max R (max X 1) ≤ max X 1 * R := by
    refine max_le ?_ ?_
    · exact le_mul_of_one_le_left (by linarith) hX1
    · exact le_mul_of_one_le_right (by linarith) hR
  have h2 : (max R (max X 1)) ^ (1 - η) ≤ (max X 1 * R) ^ (1 - η) :=
    Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h3 : (max X 1) ^ (1 - η) ≤ max X 1 := by
    calc (max X 1) ^ (1 - η) ≤ (max X 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = max X 1 := Real.rpow_one _
  rw [Real.mul_rpow (by positivity) (by positivity)] at h2
  calc _ ≤ (max X 1) ^ (1 - η) * R ^ (1 - η) := h2
    _ ≤ max X 1 * R ^ (1 - η) := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by ring

/-- **(1.22) in every dimension `d ≥ 2`**, with no hypothesis. -/
theorem correctorOscSublinear_holds [NeZero d] (hd : 2 ≤ d) : CorrectorOscSublinear d := by
  intro p hpc hp1
  obtain ⟨s, θ, η, Cs, hs, hθ, hη, hη4, hCs, X, hXm, -, hXos, hae⟩ :=
    exists_corrector_sup_os hd p hpc hp1
  have hc1 := isOsBond_const (d := d) (p := p) one_pos hs
  obtain ⟨θ', hθ', hX'⟩ := exists_isOsBond_max hs hs hθ (by positivity) hXm measurable_const
    hXos hc1
  refine ⟨min s s, η, 18 * (Cs + 1) * θ', lt_min hs hs, hη, by linarith, by positivity,
    fun R hR => ?_⟩
  refine ⟨fun ω => 18 * (Cs + 1) * R ^ (1 - η) * max (X ω) 1,
    measurable_const.mul (hXm.max measurable_const), fun ω => by positivity, ?_, ?_⟩
  · have hc : (0 : ℝ) < 18 * (Cs + 1) * R ^ (1 - η) := by positivity
    have h := IsOsBond.const_mul hc hX'
    have e : 18 * (Cs + 1) * θ' * R ^ (1 - η) = 18 * (Cs + 1) * R ^ (1 - η) * θ' := by ring
    rw [e]
    exact h
  · filter_upwards [hae, supercriticalBondCorrectorInput_holds d hd p hpc hp1] with ω hω hU
    intro h q ℓ hℓ a b ha hb
    obtain ⟨u, hu, hsup⟩ := hω h q
    set Q : ℝ := ∑ i, |q i| with hQ
    have hQ0 : 0 ≤ Q := by positivity
    -- the scale of the ball
    set T : ℝ := max R (max (X ω) 1) with hT
    have hT1 : 1 ≤ T := hR.trans (le_max_left _ _)
    obtain ⟨m, hm1, hm2⟩ := exists_three_pow_between hT1
    have hXm2 : X ω ≤ 3 ^ (m + 2) := by
      have : X ω ≤ T := (le_max_left _ _).trans (le_max_right _ _)
      have e : (3 : ℝ) ^ (m + 2) = 9 * 3 ^ m := by ring
      rw [e]; linarith
    have hbox : ∀ x : (uniqueInfiniteComponent h), ‖latticeEuclideanEmbedding x.val‖ < R →
        ∀ i, |((x.val i : ℤ) : ℝ)| ≤ 3 ^ (m + 2) := by
      intro x hx i
      have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex d) i
      have e0 : latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
        ext j; simp [latticeEuclideanEmbedding]
      rw [e0, dist_zero_right] at h1
      simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h1
      have e : (3 : ℝ) ^ (m + 2) = 9 * 3 ^ m := by ring
      have hRT : R ≤ T := le_max_left _ _
      rw [e]; linarith
    have hsa := hsup (m + 2) hXm2 a (hbox a ha)
    have hsb := hsup (m + 2) hXm2 b (hbox b hb)
    -- the bound at the scale
    have hscale : ((3 : ℝ) ^ (m + 2)) ^ (1 - η) ≤ 9 * R ^ (1 - η) * max (X ω) 1 := by
      have e : (3 : ℝ) ^ (m + 2) = 9 * 3 ^ m := by ring
      rw [e]
      have h1 : (9 * (3 : ℝ) ^ m) ^ (1 - η) ≤ (9 * T) ^ (1 - η) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have h2 : (9 * T) ^ (1 - η) ≤ 9 * T ^ (1 - η) := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (9 : ℝ) ^ (1 - η) ≤ (9 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 9 := Real.rpow_one 9
      have h3 := max_rpow_le_mul (X := X ω) hR hη.le (by linarith)
      calc (9 * (3 : ℝ) ^ m) ^ (1 - η) ≤ 9 * T ^ (1 - η) := h1.trans h2
        _ ≤ 9 * (R ^ (1 - η) * max (X ω) 1) := mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 9 * R ^ (1 - η) * max (X ω) 1 := by ring
    -- the corrected plane differs from `u` by a constant
    obtain ⟨m₀, hm₀⟩ := eventually_le_three_pow (X ω)
    have hslope : componentSlopeAsymptotics (uniqueInfiniteComponent h) q u :=
      componentSlopeAsymptotics_of_scale_bound (uniqueInfiniteComponent h) q u (c := Cs * Q) hη
        (by positivity) (m₀ := m₀) fun m' hm' x hx => hsup m' (hm₀ m' hm') x hx
    have hcp : IsCorrectedPlane (uniqueInfiniteComponent h) q u := ⟨hu, hslope⟩
    obtain ⟨hnorm, -⟩ := hU h
    have hdiff : ℓ a - ℓ b = u a - u b := by
      have hℓ' := isCorrectedPlane_sub (uniqueInfiniteComponent h) hℓ
        (isCorrectedPlane_const (uniqueInfiniteComponent h) (ℓ b))
      rw [sub_zero] at hℓ'
      have hu' := isCorrectedPlane_sub (uniqueInfiniteComponent h) hcp
        (isCorrectedPlane_const (uniqueInfiniteComponent h) (u b))
      rw [sub_zero] at hu'
      have h1 := (hnorm q b).unique ⟨hℓ', by simp⟩ ⟨hu', by simp⟩
      have := congrFun h1 a
      simp only [Pi.sub_apply] at this
      linarith
    set ga := u a - componentSlope (uniqueInfiniteComponent h) q a with hga
    set gb := u b - componentSlope (uniqueInfiniteComponent h) q b with hgb
    have e : (ℓ a - ∑ i, q i * (a.val i : ℝ)) - (ℓ b - ∑ i, q i * (b.val i : ℝ)) = ga - gb := by
      simp only [hga, hgb, componentSlope]; linarith
    rw [e]
    have hQs : 0 ≤ Cs * Q := by positivity
    calc |ga - gb| ≤ |ga| + |gb| := abs_sub _ _
      _ ≤ 2 * (Cs * Q * ((3 : ℝ) ^ (m + 2)) ^ (1 - η)) := by linarith
      _ ≤ 2 * (Cs * Q * (9 * R ^ (1 - η) * max (X ω) 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale hQs) (by norm_num)
      _ ≤ Q * (18 * (Cs + 1) * R ^ (1 - η) * max (X ω) 1) := by
          have h0 : 0 ≤ R ^ (1 - η) * max (X ω) 1 := by positivity
          have h1 : 0 ≤ Q * (R ^ (1 - η) * max (X ω) 1) := mul_nonneg hQ0 h0
          nlinarith

end Rigidity.Proofs.Regularity.GeneralDim
