import PercolationClusterHomogenization.Proofs.Cluster.GeneralWeakConvOrigin
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuStationary

/-!
# Lemma 5.7 of Armstrong and Dario in every dimension

For `d ≥ 2` and `p > p_c(d)` there is `C` such that for every triadic cube `V` of scale `n` and
every slope `q`,

`E[∑_j (|V|⁻¹ ⟨e_j, ∇[u(·, V, q)]_𝒫⟩_V - (ā_{□_n}⁻¹ q)_j)²] ≤ C |q|² (τ_n + 3^{-n/4})`

(`exists_lintegral_cubeMuGradAvg_sub_le`, display (5.25) of Lemma 5.7). Armstrong and Dario state
it for `□_n` and use it for every `z + □_n`, the law of `μ` being stationary:

* for the cube `□_n` centred at the origin and `n ≥ 8d`, this is
  `exists_lintegral_cubeMuGradAvg_origin_le`;
* for every triadic cube `V` of scale `n`, the spatial average on `V` at `ω` equals the spatial
  average on `□_n` at the configuration translated by `-c`, `c` the centre of `V`, on the event that
  the partition agrees with the capped partition on both cubes (`cubeMuGradAvg_shift_eq_of_good`),
  whose complement has probability at most `C exp(-c 3ⁿ)`; the translation preserves the law of
  the bonds;
* the spatial average and its mean are bounded by `2d K² 3^{(2d-1)n} |q|₁`, which covers the
  finitely many scales `n < 8d` and the exceptional event.

The two-dimensional version is `Rigidity.Proofs.Cluster.planarWeakConvergence_holds`.
-/

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Translation of the spatial average.** On the event that the partition agrees with the capped
partition on `V` at `ω` and on the translated cube at the translated configuration, the spatial
average moves with the translation. -/
theorem cubeMuGradAvg_shift_eq_of_good (hd : 0 < d) {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) {ω : Configuration d} (hω : CubeLocalGood ω V)
    (hω' : CubeLocalGood (configurationTranslation z ω) (V.shift z)) (q : Fin d → ℝ)
    (j : Fin d) :
    cubeMuGradAvg (configurationTranslation z ω) (V.shift z) q j = cubeMuGradAvg ω V q j := by
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hpart : ∀ x ∈ V.vertices, partitionCube (configurationTranslation z ω) (x + z) =
      (partitionCube ω x).shift z := by
    intro x hx
    rw [partitionCube_eq_cappedCube hω' ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      partitionCube_eq_cappedCube hω hx]
    exact cappedCube_goodCubes_translation hz' ω x
  by_cases hres : PartitionResolved ω V
  · have hres' := (partitionResolved_shift_iff hz hpart).2 hres
    rw [cubeMuGradAvg, cubeMuGradAvg, cubeCoarsePairing_cubeMuMinimizer_div hd hω'.1 hres',
      cubeCoarsePairing_cubeMuMinimizer_div hd hω.1 hres,
      cubeMu_shift_translation_of_partition hres hz hpart,
      cubeMu_shift_translation_of_partition hres hz hpart,
      cubeMu_shift_translation_of_partition hres hz hpart]
  · have hres' : ¬ PartitionResolved (configurationTranslation z ω) (V.shift z) :=
      fun h => hres ((partitionResolved_shift_iff hz hpart).1 h)
    have h0 : cubeMuMinimizer ω V q = 0 := by
      rw [cubeMuMinimizer, dif_neg fun h => hres h.2.2]
    have h0' : cubeMuMinimizer (configurationTranslation z ω) (V.shift z) q = 0 := by
      rw [cubeMuMinimizer, dif_neg fun h => hres' h.2.2]
    rw [cubeMuGradAvg, cubeMuGradAvg, h0, h0', map_zero, map_zero, zero_div, zero_div]

/-- On the stationary good event, the spatial average on `V` is the spatial average on the cube
at the origin at the configuration translated by minus the centre of `V`. -/
theorem cubeMuGradAvg_eq_atOrigin_of_good (hd : 0 < d) {V : TriadicCube d}
    {ω : Configuration d} (h : CubeStatGood ω V) (q : Fin d → ℝ) (j : Fin d) :
    cubeMuGradAvg ω V q j =
      cubeMuGradAvg (configurationTranslation (-V.center) ω) V.atOrigin q j := by
  have hω : configurationTranslation V.center (configurationTranslation (-V.center) ω) = ω := by
    rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have h2 : CubeLocalGood (configurationTranslation V.center
      (configurationTranslation (-V.center) ω)) (V.atOrigin.shift V.center) := by
    rw [hω, V.atOrigin_shift_center]
    exact h.1
  have := cubeMuGradAvg_shift_eq_of_good hd V.atOrigin_side_dvd_center h.2 h2 q j
  rw [hω, V.atOrigin_shift_center] at this
  exact this

/-- The quantity of display (5.25). -/
noncomputable def cubeWeakConvError (p : unitInterval) (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d, (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p V.scale *ᵥ q) j) ^ 2

theorem measurable_cubeWeakConvError (hd : 0 < d) (p : unitInterval) (V : TriadicCube d)
    (q : Fin d → ℝ) : Measurable fun ω => cubeWeakConvError p ω V q :=
  Finset.measurable_sum _ fun j _ =>
    ((measurable_cubeMuGradAvg hd V q j).sub measurable_const).pow_const 2

/-- **The mean is bounded like the spatial average**: `|(ā_{□_n}⁻¹ q)_j| ≤ 2d K² 3^{(2d-1)n} |q|₁`. -/
theorem abs_cubeAhomInvFinite_mulVec_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (n : ℕ) (q : Fin d → ℝ) (j : Fin d) :
    |(cubeAhomInvFinite p n *ᵥ q) j| ≤
      2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ n) ^ (2 * d - 1) * 1 * ∑ i, |q i| := by
  have hd0 : 0 < d := by omega
  set B := 2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ n) ^ (2 * d - 1) * 1 * ∑ i, |q i|
  have hb : ∀ ω, |cubeMuGradAvg ω ⟨n, 0⟩ q j| ≤ B := fun ω =>
    abs_cubeMuGradAvg_le hd0 ω (⟨n, 0⟩ : TriadicCube d) q j
  have hint : Integrable (fun ω => cubeMuGradAvg ω ⟨n, 0⟩ q j) (latticeBondLaw d p) :=
    Integrable.of_bound (measurable_cubeMuGradAvg hd0 _ q j).aestronglyMeasurable B
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  rw [← integral_cubeMuGradAvg_origin hd hpc]
  calc |∫ ω, cubeMuGradAvg ω ⟨n, 0⟩ q j ∂(latticeBondLaw d p)|
      ≤ ∫ ω, |cubeMuGradAvg ω ⟨n, 0⟩ q j| ∂(latticeBondLaw d p) := abs_integral_le_integral_abs
    _ ≤ ∫ _ω, B ∂(latticeBondLaw d p) :=
        integral_mono hint.abs (integrable_const B) fun ω => hb ω
    _ = B := by simp

/-- **A deterministic bound for the quantity of display (5.25).** -/
theorem cubeWeakConvError_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) :
    cubeWeakConvError p ω V q ≤
      4 * d * (2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ V.scale) ^ (2 * d - 1) * 1 *
        ∑ i, |q i|) ^ 2 := by
  have hd0 : 0 < d := by omega
  set B := 2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ V.scale) ^ (2 * d - 1) * 1 * ∑ i, |q i|
  have hterm : ∀ j : Fin d, (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p V.scale *ᵥ q) j) ^ 2 ≤
      4 * B ^ 2 := by
    intro j
    have h1 := abs_cubeMuGradAvg_le hd0 ω V q j
    have h2 := abs_cubeAhomInvFinite_mulVec_le hd hpc V.scale q j
    have h3 : |cubeMuGradAvg ω V q j - (cubeAhomInvFinite p V.scale *ᵥ q) j| ≤ 2 * B :=
      (abs_sub _ _).trans (by linarith)
    rw [← sq_abs]
    calc _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = 4 * B ^ 2 := by ring
  unfold cubeWeakConvError
  calc _ ≤ ∑ _j : Fin d, 4 * B ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = 4 * d * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Transfer to every cube.** The expectation of the quantity of display (5.25) on a cube `V`
exceeds that on the cube of the same scale at the origin by at most the deterministic bound times
the probability of the failure of the stationary good event. -/
theorem lintegral_cubeWeakConvError_le_atOrigin [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V : TriadicCube d) (q : Fin d → ℝ) :
    ∫⁻ ω, ENNReal.ofReal (cubeWeakConvError p ω V q) ∂(latticeBondLaw d p) ≤
      ∫⁻ ω, ENNReal.ofReal (cubeWeakConvError p ω V.atOrigin q) ∂(latticeBondLaw d p) +
        ENNReal.ofReal (4 * d * (2 * d * coarseGradConstant d ^ 2 *
          ((3 : ℝ) ^ V.scale) ^ (2 * d - 1) * 1 * ∑ i, |q i|) ^ 2) *
          latticeBondLaw d p {ω | ¬ CubeStatGood ω V} := by
  have hd0 : 0 < d := by omega
  have hB : MeasurableSet {ω : Configuration d | ¬ CubeStatGood ω V} :=
    (measurableSet_cubeStatGood V).compl
  have hscale : V.atOrigin.scale = V.scale := rfl
  refine (lintegral_le_lintegral_add_of_le_off (latticeBondLaw d p) hB
    (g := fun ω => ENNReal.ofReal (cubeWeakConvError p (configurationTranslation (-V.center) ω)
      V.atOrigin q))
    (fun ω => ENNReal.ofReal_le_ofReal (cubeWeakConvError_le hd hpc ω V q))
    (fun ω hω => ?_)).trans (le_of_eq ?_)
  · have hgood : CubeStatGood ω V := by
      simp only [Set.mem_setOf_eq, not_not] at hω
      exact hω
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    unfold cubeWeakConvError
    rw [hscale]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cubeMuGradAvg_eq_atOrigin_of_good hd0 hgood q j]
  · congr 1
    exact (measurePreserving_configurationTranslation p (-V.center)).lintegral_comp
      ((measurable_cubeWeakConvError hd0 p _ q).ennreal_ofReal)

/-- **Lemma 5.7 of Armstrong and Dario** (display (5.25), every dimension `d ≥ 2`,
`p > p_c(d)`), for every triadic cube `V` of scale `n`:
`E[∑_j (|V|⁻¹ ⟨e_j, ∇[u(·, V, q)]_𝒫⟩_V - (ā_{□_n}⁻¹ q)_j)²] ≤ C |q|² (τ_n + 3^{-n/4})`. -/
theorem exists_lintegral_cubeMuGradAvg_sub_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube d) (q : Fin d → ℝ),
      ∫⁻ ω, ENNReal.ofReal (∑ j : Fin d,
          (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p V.scale *ᵥ q) j) ^ 2)
          ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) *
          (cubeTau (d := d) p V.scale + (3 : ℝ) ^ (-(V.scale : ℝ) / 4))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C₀, hC₀, horig⟩ := exists_lintegral_cubeMuGradAvg_origin_le hd hpc
  obtain ⟨Cs, hCs, cs, hcs, hstat⟩ := exists_measure_not_cubeStatGood_le hd hpc
  obtain ⟨KB, hKB, hKBk⟩ := exists_exp_neg_rpow_le_inv_pow hcs one_pos (4 * d + 1)
  set K₄ := coarseGradConstant d ^ 4 with hK₄
  set A : ℝ := 16 * d ^ 3 * K₄ * d with hA
  set C₁ : ℝ := A * (2 * Cs.toReal) * KB with hC₁
  set C₂ : ℝ := A * 3 ^ (32 * d ^ 2) * 3 ^ (2 * d) with hC₂
  refine ⟨C₀ + C₁ + C₂, by positivity, fun V q => ?_⟩
  set n := V.scale with hn
  set P := ∑ i, q i ^ 2 with hP
  set Q := ∑ i, |q i| with hQ
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hQP : Q ^ 2 ≤ d * P := sum_abs_sq_le q
  set τx := cubeTau (d := d) p n + (3 : ℝ) ^ (-(n : ℝ) / 4) with hτx
  have hτ0 := cubeTau_nonneg (d := d) p n
  have hx0 : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℝ) / 4) := by positivity
  have hxτ : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ τx := by rw [hτx]; linarith
  set t : ℝ := (3 : ℝ) ^ n with ht
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  set B := 4 * d * (2 * d * coarseGradConstant d ^ 2 * t ^ (2 * d - 1) * 1 * Q) ^ 2 with hBdef
  have hBle : B ≤ A * t ^ (4 * d) * P := by
    have e : B = 16 * d ^ 3 * K₄ * (t ^ (2 * d - 1)) ^ 2 * Q ^ 2 := by
      rw [hBdef, hK₄]
      ring
    have ht2 : (t ^ (2 * d - 1)) ^ 2 ≤ t ^ (4 * d) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ ht1 (by omega)
    rw [e, hA]
    have h1 : 16 * (d : ℝ) ^ 3 * K₄ * (t ^ (2 * d - 1)) ^ 2 * Q ^ 2 ≤
        16 * d ^ 3 * K₄ * t ^ (4 * d) * (d * P) := by
      have h0 : (0 : ℝ) ≤ 16 * d ^ 3 * K₄ := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left ht2 h0) hQP (sq_nonneg _) (by positivity)
    linarith
  have hτx0 : 0 ≤ τx := le_trans hx0.le hxτ
  by_cases hbig : 8 * d ≤ n
  · have h0 := horig n hbig q
    have htr := lintegral_cubeWeakConvError_le_atOrigin hd hpc V q
    have hstatV := hstat V
    unfold cubeWeakConvError at htr
    have hVo : V.atOrigin = ⟨n, 0⟩ := rfl
    rw [hVo] at htr
    refine htr.trans ?_
    refine (add_le_add h0 (mul_le_mul_of_nonneg_left hstatV zero_le)).trans ?_
    have hexp : Real.exp (-cs * t) ≤ KB * (t⁻¹) ^ (4 * d + 1) := by
      have := hKBk n
      rwa [Real.rpow_one] at this
    rw [← ENNReal.ofReal_toReal hCs, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hbad : B * (2 * Cs.toReal * Real.exp (-cs * t)) ≤ C₁ * P * τx := by
      have hpow : t ^ (4 * d) * (t⁻¹) ^ (4 * d + 1) = t⁻¹ := by
        rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity), one_pow, one_mul]
      have htx : t⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by
        rw [ht]
        exact inv_three_pow_le_three_rpow n
      calc B * (2 * Cs.toReal * Real.exp (-cs * t))
          ≤ (A * t ^ (4 * d) * P) * (2 * Cs.toReal * (KB * (t⁻¹) ^ (4 * d + 1))) :=
            mul_le_mul hBle (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
              (by positivity)
        _ = C₁ * P * (t ^ (4 * d) * (t⁻¹) ^ (4 * d + 1)) := by rw [hC₁]; ring
        _ = C₁ * P * t⁻¹ := by rw [hpow]
        _ ≤ C₁ * P * τx := mul_le_mul_of_nonneg_left (htx.trans hxτ) (by positivity)
    have e : (C₀ + C₁ + C₂) * P * τx = C₀ * P * τx + C₁ * P * τx + C₂ * P * τx := by ring
    rw [e]
    have hC₂0 : 0 ≤ C₂ * P * τx := by positivity
    have hB0 : (0 : ℝ) ≤ 4 * d * (2 * d * coarseGradConstant d ^ 2 * t ^ (2 * d - 1) * 1 * Q) ^ 2 :=
      by positivity
    change C₀ * P * τx + B * (2 * Cs.toReal * Real.exp (-cs * (3 : ℝ) ^ n)) ≤ _
    rw [← ht]
    linarith
  · have hsmall : n < 8 * d := not_le.1 hbig
    have hdet : ∀ ω, ENNReal.ofReal (∑ j : Fin d,
        (cubeMuGradAvg ω V q j - (cubeAhomInvFinite p V.scale *ᵥ q) j) ^ 2) ≤ ENNReal.ofReal B :=
      fun ω => ENNReal.ofReal_le_ofReal (cubeWeakConvError_le hd hpc ω V q)
    refine (lintegral_mono hdet).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have ht8 : t ^ (4 * d) ≤ 3 ^ (32 * d ^ 2) := by
      rw [ht, ← pow_mul]
      refine pow_le_pow_right₀ (by norm_num) ?_
      have : n * (4 * d) ≤ 8 * d * (4 * d) := Nat.mul_le_mul_right _ hsmall.le
      nlinarith
    have h1x : (1 : ℝ) ≤ 3 ^ (2 * d) * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      apply Real.one_le_rpow (by norm_num)
      have : (n : ℝ) < 8 * d := by exact_mod_cast hsmall
      push_cast
      linarith
    calc B ≤ A * t ^ (4 * d) * P := hBle
      _ ≤ A * 3 ^ (32 * d ^ 2) * P := by gcongr
      _ ≤ A * 3 ^ (32 * d ^ 2) * P * (3 ^ (2 * d) * (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
          le_mul_of_one_le_right (by positivity) h1x
      _ = C₂ * P * (3 : ℝ) ^ (-(n : ℝ) / 4) := by rw [hC₂]; ring
      _ ≤ C₂ * P * τx := mul_le_mul_of_nonneg_left hxτ (by positivity)
      _ ≤ (C₀ + C₁ + C₂) * P * τx := by
          have : 0 ≤ (C₀ + C₁) * P * τx := by positivity
          nlinarith

end Rigidity.Percolation
