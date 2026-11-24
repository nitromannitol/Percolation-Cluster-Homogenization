import PercolationClusterHomogenization.External.ClusterDensity
import PercolationClusterHomogenization.Proofs.Density.ScaleInputsFaithful
import LatticeProb.Prob.Percolation.OpenGraphTranslation
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Proposition 2.6, step:2.6-inputs: the density of the infinite cluster from Dario–Gu

The density input of Proposition 2.6 (paper L508-511 of the corrected draft; correction C35) from
the concentration of the density of the infinite cluster in triadic cubes
(`Rigidity.External.ClusterDensityConcentrationInput`, Dario–Gu, arXiv:1909.10439v4,
Proposition A.1), by a union bound over triadic cubes.

* A triadic cube `□` of size `3^m` is *bad* if `| |𝒞_∞ ∩ □|/|□| - θ | ≥ θ/2`; by Proposition A.1
  and Markov's inequality, `P[□ bad] ≤ 2 exp(-((θ/2C) 3^{dm/2})^{s₀})`, `s₀ = 2(d-1)/(3d²+2d-1)`
  (`measure_badCubeEvent_le`).
* At the scale `3^m ≤ r/(100d) < 3^{m+1}`, every ball of radius `r/100` whose centre is within
  `r/100` of `x` contains a triadic cube of size `3^m` among the `K_d = (6d+5)^d` cubes `nearCubes x m`;
  if that cube is good, the ball contains at least `(θ/2) 3^{dm} ≥ (θ/2)(300d)^{-d} r^d` vertices
  of `𝒞_∞`.
* The minimal scale is `M(x) = 100d · 3^{N(x)}`, `N(x)` the first scale from which every scale is
  good (`exists_minimalScale_of_summable`; Borel–Cantelli). `E[exp(M^s)] < ∞` uniformly in `x`, for
  `s = d s₀/4`, because `P[scale m bad] ≤ 2 K_d exp(-B 3^{2sm})` beats `exp((100d 3^{m+1})^s)`.
* If `θ(p) = 0`, almost surely there is no infinite cluster (translation invariance), and the
  statement is empty.

Main results.
* `clusterDensityInputFaithful_of_concentration`: Proposition A.1 gives the printed density
  sentence `ClusterDensityInputFaithful`.
* `clusterDensityInputProposed_of_concentration`: Proposition A.1 gives
  `ClusterDensityInputProposed` (with `clusterDensityInputProposed_of_faithful`).
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Steps.S2 Classical

variable {d : ℕ}

/-! ### Triadic cubes -/

/-- `3^m = 2j + 1` with `j = (3^m - 1)/2`. -/
theorem three_pow_eq_two_mul_half_add_one (m : ℕ) :
    (3 : ℤ) ^ m = 2 * (((3 : ℤ) ^ m - 1) / 2) + 1 := by
  obtain ⟨j, hj⟩ : Odd ((3 : ℤ) ^ m) := Odd.pow ⟨1, by norm_num⟩
  omega

/-- The coordinate condition of a triadic cube in integers. -/
theorem abs_sub_lt_three_pow_half_iff (m : ℕ) (a b : ℤ) :
    |(a : ℝ) - 3 ^ m * (b : ℝ)| < 3 ^ m / 2 ↔
      3 ^ m * b - ((3 : ℤ) ^ m - 1) / 2 ≤ a ∧ a ≤ 3 ^ m * b + ((3 : ℤ) ^ m - 1) / 2 := by
  have hQ := three_pow_eq_two_mul_half_add_one m
  set j : ℤ := ((3 : ℤ) ^ m - 1) / 2
  have hr : (3 : ℝ) ^ m = 2 * (j : ℝ) + 1 := by exact_mod_cast hQ
  have key : (a : ℝ) - 3 ^ m * (b : ℝ) = ((a - 3 ^ m * b : ℤ) : ℝ) := by push_cast; ring
  rw [key, hr, abs_lt]
  set t : ℤ := a - 3 ^ m * b with ht
  have e1 : (t : ℝ) < (2 * j + 1) / 2 ↔ 2 * t < 2 * j + 1 := by
    constructor
    · intro h
      have h' : (2 * t : ℝ) < 2 * j + 1 := by linarith
      exact_mod_cast h'
    · intro h
      have h' : (2 * t : ℝ) < 2 * j + 1 := by exact_mod_cast h
      linarith
  have e2 : -((2 * (j : ℝ) + 1) / 2) < (t : ℝ) ↔ -(2 * j + 1) < 2 * t := by
    constructor
    · intro h
      have h' : -(2 * (j : ℝ) + 1) < 2 * t := by linarith
      exact_mod_cast h'
    · intro h
      have h' : -(2 * (j : ℝ) + 1) < 2 * t := by exact_mod_cast h
      linarith
  rw [e1, e2]
  omega

/-- The triadic cube `□_m(3^m k)` as a product of integer intervals. -/
noncomputable def triadicCubeFinset (d m : ℕ) (k : Vertex d) : Finset (Vertex d) :=
  Fintype.piFinset fun i =>
    Finset.Icc (3 ^ m * k i - ((3 : ℤ) ^ m - 1) / 2) (3 ^ m * k i + ((3 : ℤ) ^ m - 1) / 2)

theorem coe_triadicCubeFinset (m : ℕ) (k : Vertex d) :
    (triadicCubeFinset d m k : Set (Vertex d)) = triadicCube d m k := by
  ext y
  simp only [Finset.mem_coe, triadicCubeFinset, Fintype.mem_piFinset, Finset.mem_Icc, triadicCube,
    Set.mem_setOf_eq, abs_sub_lt_three_pow_half_iff]

theorem card_triadicCubeFinset (m : ℕ) (k : Vertex d) :
    (triadicCubeFinset d m k).card = 3 ^ (d * m) := by
  have hQ := three_pow_eq_two_mul_half_add_one m
  have hc : ∀ i, (Finset.Icc (3 ^ m * k i - ((3 : ℤ) ^ m - 1) / 2)
      (3 ^ m * k i + ((3 : ℤ) ^ m - 1) / 2)).card = 3 ^ m := by
    intro i
    rw [Int.card_Icc]
    have h3 : ((3 ^ m : ℕ) : ℤ) = (3 : ℤ) ^ m := by norm_num
    have e : 3 ^ m * k i + ((3 : ℤ) ^ m - 1) / 2 + 1 - (3 ^ m * k i - ((3 : ℤ) ^ m - 1) / 2) =
        ((3 ^ m : ℕ) : ℤ) := by rw [h3]; omega
    rw [e, Int.toNat_natCast]
  rw [triadicCubeFinset, Fintype.card_piFinset]
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm]

/-- `|□| = 3^{dm}` for a triadic cube of size `3^m`. -/
theorem ncard_triadicCube (m : ℕ) (k : Vertex d) : (triadicCube d m k).ncard = 3 ^ (d * m) := by
  rw [← coe_triadicCubeFinset, Set.ncard_coe_finset, card_triadicCubeFinset]

theorem infiniteClusterCount_triadicCube (m : ℕ) (k : Vertex d) (ω : Configuration d) :
    infiniteClusterCount (triadicCube d m k) ω =
      ((triadicCubeFinset d m k).filter fun y => ω ∈ infiniteComponentEvent y).card := by
  rw [infiniteClusterCount, ← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, ← coe_triadicCubeFinset, Finset.mem_coe]

theorem measurable_infiniteClusterCount_triadicCube (m : ℕ) (k : Vertex d) :
    Measurable fun ω : Configuration d => (infiniteClusterCount (triadicCube d m k) ω : ℝ) := by
  have e : (fun ω : Configuration d => (infiniteClusterCount (triadicCube d m k) ω : ℝ)) =
      fun ω => ∑ y ∈ triadicCubeFinset d m k,
        (infiniteComponentEvent y).indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    rw [infiniteClusterCount_triadicCube, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : ω ∈ infiniteComponentEvent y <;> simp [hy]
  rw [e]
  exact Finset.measurable_sum _ fun y _ =>
    measurable_const.indicator (measurableSet_infiniteComponentEvent y)

/-! ### Markov's inequality, translation invariance -/

/-- `X ≤ O_s(τ)` gives `P[X ≥ t] ≤ 2 exp(-(t/τ)^s)`. -/
theorem measure_le_le_of_isOsBond {p : unitInterval} {X : Configuration d → ℝ} {s τ t : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (ht : 0 ≤ t) (hX : IsOsBond d p X s τ) :
    latticeBondLaw d p {ω | t ≤ X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / τ) ^ s)) := by
  set ε := Real.exp ((t / τ) ^ s)
  have hε : 0 < ε := Real.exp_pos _
  have hsub : {ω | t ≤ X ω} ⊆
      {ω | ε ≤ Real.exp (Real.rpow (max (X ω / τ) 0) s)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (div_nonneg ht hτ.le)
      (le_max_of_le_left (div_le_div_of_nonneg_right hω hτ.le)) hs.le
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := latticeBondLaw d p)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hX.1 ε
  have h2 : (latticeBondLaw d p).real
      {ω | ε ≤ Real.exp (Real.rpow (max (X ω / τ) 0) s)} ≤ 2 * Real.exp (-(t / τ) ^ s) := by
    have h3 := hM.trans hX.2
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hε]
    linarith
  calc latticeBondLaw d p {ω | t ≤ X ω}
      ≤ latticeBondLaw d p {ω | ε ≤ Real.exp (Real.rpow (max (X ω / τ) 0) s)} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((latticeBondLaw d p).real
          {ω | ε ≤ Real.exp (Real.rpow (max (X ω / τ) 0) s)}) := (ofReal_measureReal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h2

theorem configurationTranslation_mem_infiniteComponentEvent_iff (z : Vertex d)
    (ω : Configuration d) (x : Vertex d) :
    configurationTranslation z ω ∈ infiniteComponentEvent x ↔
      ω ∈ infiniteComponentEvent (x - z) := by
  simp only [mem_infiniteComponentEvent_iff, openGraph_reachable_sub_translation_iff]
  constructor
  · intro h s
    obtain ⟨y, hy, hr⟩ := h (s.image (· + z))
    exact ⟨y - z, fun hs => hy (Finset.mem_image.mpr ⟨y - z, hs, sub_add_cancel y z⟩), hr⟩
  · intro h s
    obtain ⟨y, hy, hr⟩ := h (s.image (· - z))
    refine ⟨y + z, fun hs => hy (Finset.mem_image.mpr ⟨y + z, hs, add_sub_cancel_right y z⟩), ?_⟩
    rwa [add_sub_cancel_right]

/-- `P[x ∈ 𝒞_∞] = θ(p)` at every vertex (translation invariance). -/
theorem measure_infiniteComponentEvent_eq (p : unitInterval) (x : Vertex d) :
    latticeBondLaw d p (infiniteComponentEvent x) =
      latticeBondLaw d p (infiniteComponentEvent 0) := by
  have hpre : configurationTranslation (-x) ⁻¹' infiniteComponentEvent 0 =
      infiniteComponentEvent x := by
    ext ω
    simp only [Set.mem_preimage, configurationTranslation_mem_infiniteComponentEvent_iff,
      zero_sub, neg_neg]
  rw [← hpre, (measurePreserving_configurationTranslation p (-x)).measure_preimage
    (measurableSet_infiniteComponentEvent 0).nullMeasurableSet]

/-- If `θ(p) = 0`, almost surely there is no infinite open cluster. -/
theorem ae_not_hasUniqueInfiniteOpenComponent_of_theta_eq_zero (p : unitInterval)
    (hθ : theta d p = 0) :
    ∀ᵐ ω ∂latticeBondLaw d p, ¬ HasUniqueInfiniteOpenComponent ω := by
  have hnull : ∀ x : Vertex d, latticeBondLaw d p (infiniteComponentEvent x) = 0 := by
    intro x
    rw [measure_infiniteComponentEvent_eq p x]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hθ
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_iUnion_null hnull)] with ω hω h
  obtain ⟨v, hv⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  exact hω (Set.mem_iUnion.2 ⟨v, (mem_uniqueInfiniteComponent_iff h v).1 hv⟩)

/-! ### Exponents and summability -/

/-- `((θ/2) / (C 3^{-dm/2}))^{s₀} = (θ/2C)^{s₀} (e^{t m})²`, `t = (d s₀/4) log 3`. -/
theorem badCube_exponent_eq {θ C s₀ : ℝ} (d m : ℕ) (hθ : 0 < θ) (hC : 0 < C) :
    ((θ / 2) / (C * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2))) ^ s₀ =
      (θ / (2 * C)) ^ s₀ * Real.exp (s₀ * d / 4 * Real.log 3 * m) ^ 2 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) * (m : ℝ) / 2) := by positivity
  have h1 : (θ / 2) / (C * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2)) =
      (θ / (2 * C)) * (3 : ℝ) ^ ((d : ℝ) * (m : ℝ) / 2) := by
    rw [neg_div, Real.rpow_neg (by norm_num)]
    field_simp
  rw [h1, Real.mul_rpow (by positivity) h3.le, ← Real.rpow_mul (by norm_num),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), sq, ← Real.exp_add]
  congr 2
  ring

/-- `(L 3^{m+1})^s = (3L)^s e^{t m}`, `t = s log 3`. -/
theorem scale_exponent_eq {L s : ℝ} (hL : 0 ≤ L) (m : ℕ) :
    (L * 3 ^ (m + 1)) ^ s = (3 * L) ^ s * Real.exp (s * Real.log 3 * m) := by
  rw [pow_succ, show L * (3 ^ m * 3) = (3 * L) * 3 ^ m by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 2
  ring

/-- `∑_m exp(A v_m - B v_m²)` converges for `v_m = e^{t m}`, `B, t > 0`. -/
theorem summable_exp_mul_sub_sq (A B t : ℝ) (hB : 0 < B) (ht : 0 < t) :
    Summable fun m : ℕ => Real.exp (A * Real.exp (t * m) - B * Real.exp (t * m) ^ 2) := by
  set q := Real.exp (-(B * t))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.2 (by nlinarith)
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (A ^ 2 / (2 * B))))
  set v := Real.exp (t * m)
  have hv2 : 2 * (t * m) ≤ v ^ 2 := by
    have h := Real.add_one_le_exp (2 * (t * m))
    have e : v ^ 2 = Real.exp (2 * (t * m)) := by rw [sq, ← Real.exp_add]; ring_nf
    rw [e]
    linarith
  have h1 : A * v ≤ A ^ 2 / (2 * B) + B / 2 * v ^ 2 := by
    have h := sq_nonneg (A - B * v)
    have hB2 : 0 < 2 * B := by positivity
    rw [div_add' _ _ _ hB2.ne', le_div_iff₀ hB2]
    nlinarith
  have hq : q ^ m = Real.exp (m * (-(B * t))) := (Real.exp_nat_mul _ m).symm
  rw [hq, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

/-! ### The minimal scale -/

/-- The first scale from which every scale is good, `M = L 3^N`: `E[exp(M^s)]` is at most
`exp(L^s) + ∑_m b_m exp((L 3^{m+1})^s)` when `P[scale m bad] ≤ b_m`, and almost surely every scale
`m ≥ N` is good (Borel–Cantelli). -/
theorem exists_minimalScale_of_summable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Bad : ℕ → Set Ω) (hBad : ∀ m, MeasurableSet (Bad m))
    {L s : ℝ} (hL : 0 < L) (b : ℕ → ℝ) (hb0 : ∀ m, 0 ≤ b m)
    (hb : ∀ m, μ (Bad m) ≤ ENNReal.ofReal (b m))
    (hsum : Summable fun m => b m * Real.exp ((L * 3 ^ (m + 1)) ^ s)) :
    ∃ M : Ω → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      Integrable (fun ω => Real.exp (M ω ^ s)) μ ∧
      (∫ ω, Real.exp (M ω ^ s) ∂μ) ≤
        Real.exp (L ^ s) + ∑' m, b m * Real.exp ((L * 3 ^ (m + 1)) ^ s) ∧
      ∀ᵐ ω ∂μ, ∃ N : ℕ, M ω = L * 3 ^ N ∧ ∀ m, N ≤ m → ω ∉ Bad m := by
  set e : ℕ → ℝ := fun m => Real.exp ((L * 3 ^ (m + 1)) ^ s) with he
  have he1 : ∀ m, 1 ≤ e m := fun m => Real.one_le_exp (Real.rpow_nonneg (by positivity) _)
  have hbsum : Summable b :=
    Summable.of_nonneg_of_le hb0 (fun m => le_mul_of_one_le_right (hb0 m) (he1 m)) hsum
  have hμsum : (∑' m, μ (Bad m)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' m, b m)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hb0 hbsum]
    exact ENNReal.tsum_le_tsum hb
  have hBC := ae_eventually_notMem hμsum
  set bad : ℕ → Set Ω := fun n => ⋃ m, ⋃ (_ : n ≤ m), Bad m with hbad
  have hbadm : ∀ n, MeasurableSet (bad n) := fun n =>
    MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hBad m
  obtain ⟨N, hNm, hgood, hlt⟩ := exists_measurable_first_good bad hbadm
  set M : Ω → ℝ := fun ω => L * 3 ^ N ω with hM
  have hMm : Measurable M :=
    measurable_const.mul ((measurable_from_nat (f := fun n : ℕ => (3 : ℝ) ^ n)).comp hNm)
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by positivity
  have hex : ∀ᵐ ω ∂μ, ∃ n, ω ∉ bad n := by
    filter_upwards [hBC] with ω hω
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hω
    refine ⟨n₀, ?_⟩
    simp only [hbad, Set.mem_iUnion, not_exists]
    exact fun m hm => hn₀ m hm
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (Real.exp (M ω ^ s)) ≤
      ENNReal.ofReal (Real.exp (L ^ s)) +
        ∑' m, (Bad m).indicator (fun _ => ENNReal.ofReal (e m)) ω := by
    filter_upwards [hex] with ω hω
    have hg := hgood ω hω
    rcases hN : N ω with _ | n
    · simp only [hM, hN, pow_zero, mul_one]
      exact le_self_add
    · have h1 : ω ∈ bad n := hlt n ω (by omega)
      rw [hN] at hg
      have h2 : ω ∈ Bad n := by
        simp only [hbad, Set.mem_iUnion] at h1 hg
        obtain ⟨m, hnm, hm⟩ := h1
        rcases hnm.eq_or_lt with rfl | hlt'
        · exact hm
        · exact absurd ⟨m, hlt', hm⟩ hg
      refine le_add_left (le_trans ?_ (ENNReal.le_tsum n))
      rw [Set.indicator_of_mem h2]
      simp only [hM, hN, he, le_refl]
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (M ω ^ s)) ∂μ ≤
      ENNReal.ofReal (Real.exp (L ^ s) + ∑' m, b m * e m) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (M ω ^ s)) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (L ^ s)) +
            ∑' m, (Bad m).indicator (fun _ => ENNReal.ofReal (e m)) ω) ∂μ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (Real.exp (L ^ s)) + ∑' m, ENNReal.ofReal (e m) * μ (Bad m) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_tsum fun m => (measurable_const.indicator (hBad m)).aemeasurable]
          simp only [lintegral_indicator_const (hBad _)]
      _ ≤ ENNReal.ofReal (Real.exp (L ^ s)) + ∑' m, ENNReal.ofReal (b m * e m) := by
          refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun m => ?_)
          rw [ENNReal.ofReal_mul (hb0 m), mul_comm]
          gcongr; exact hb m
      _ = ENNReal.ofReal (Real.exp (L ^ s) + ∑' m, b m * e m) := by
          rw [ENNReal.ofReal_add (Real.exp_pos _).le
              (tsum_nonneg fun m => mul_nonneg (hb0 m) (Real.exp_pos _).le),
            ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (hb0 m) (Real.exp_pos _).le) hsum]
  have hmeasf : Measurable fun ω => Real.exp (M ω ^ s) := (hMm.pow_const s).exp
  have hint : Integrable (fun ω => Real.exp (M ω ^ s)) μ := by
    refine ⟨hmeasf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).2 ?_⟩
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨M, hMm, hM0, hint, ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeasf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal
      (add_nonneg (Real.exp_pos _).le
        (tsum_nonneg fun m => mul_nonneg (hb0 m) (Real.exp_pos _).le)) hlint
  · filter_upwards [hex] with ω hω
    refine ⟨N ω, rfl, fun m hm hmem => hgood ω hω ?_⟩
    simp only [hbad, Set.mem_iUnion]
    exact ⟨m, hm, hmem⟩

/-! ### The union bound -/

/-- The triadic cube `□_m(3^m k)` is *bad* if the density of `𝒞_∞` in it is at distance at least
`θ/2` from `θ`. -/
def badCubeEvent (d m : ℕ) (k : Vertex d) (θ : ℝ) : Set (Configuration d) :=
  {ω | θ / 2 ≤ |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
    ((triadicCube d m k).ncard : ℝ) - θ|}

theorem measurableSet_badCubeEvent (m : ℕ) (k : Vertex d) (θ : ℝ) :
    MeasurableSet (badCubeEvent d m k θ) :=
  measurableSet_le measurable_const
    (continuous_abs.measurable.comp
      (((measurable_infiniteClusterCount_triadicCube m k).div_const _).sub_const _))

/-- Proposition A.1 and Markov's inequality: `P[□ bad] ≤ 2 exp(-(θ/2C)^{s₀} e^{2tm})`. -/
theorem measure_badCubeEvent_le {p : unitInterval} {C s₀ : ℝ} (hC : 0 < C) (hs₀ : 0 < s₀)
    (hθ : 0 < theta d p) (m : ℕ) (k : Vertex d)
    (hX : IsOsBond d p (fun ω => |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((triadicCube d m k).ncard : ℝ) - theta d p|) s₀
      (C * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2))) :
    latticeBondLaw d p (badCubeEvent d m k (theta d p)) ≤
      ENNReal.ofReal (2 * Real.exp (-((theta d p / (2 * C)) ^ s₀ *
        Real.exp (s₀ * d / 4 * Real.log 3 * m) ^ 2))) := by
  have h := measure_le_le_of_isOsBond (by positivity) hs₀
    (by positivity : (0 : ℝ) ≤ theta d p / 2) hX
  rwa [badCube_exponent_eq d m hθ hC] at h

/-- A good triadic cube contains more than `(θ/2) 3^{dm}` vertices of `𝒞_∞`. -/
theorem lt_infiniteClusterCount_of_notMem_badCubeEvent {θ : ℝ} {m : ℕ} {k : Vertex d}
    {ω : Configuration d} (hgk : ω ∉ badCubeEvent d m k θ) :
    θ / 2 * (3 : ℝ) ^ (d * m) < (infiniteClusterCount (triadicCube d m k) ω : ℝ) := by
  simp only [badCubeEvent, Set.mem_setOf_eq, not_le, ncard_triadicCube] at hgk
  rw [abs_lt] at hgk
  have hpos : (0 : ℝ) < ((3 ^ (d * m) : ℕ) : ℝ) := by positivity
  have h' : θ / 2 < (infiniteClusterCount (triadicCube d m k) ω : ℝ) /
      ((3 ^ (d * m) : ℕ) : ℝ) := by linarith only [hgk.1]
  rw [lt_div_iff₀ hpos] at h'
  push_cast at h'
  linarith only [h']

end Rigidity.Proofs.S2
