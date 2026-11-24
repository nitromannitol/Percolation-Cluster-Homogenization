import PercolationClusterHomogenization.Proofs.Cluster.GeneralRhoLocal
import PercolationClusterHomogenization.Proofs.Cluster.BoundedChernoff

/-!
# Step 2 of the proof of Lemma 5.11 of Armstrong and Dario in every dimension, given the bound of
Lemma 5.9

The concentration step of the proof of Lemma 5.11: for the subcubes `z + □_n` of a large cube, the
average of the truncated stationary local versions `ρ_stat(z + □_n) ∧ C₁` exceeds `t` with small
probability, by the independence of the local versions, the exponential moment bound, and
`E[ρ_stat(□_n) ∧ C₁] ≤ C (1 + C₁) rⁿ` (`exists_integral_min_cubeRhoStat_le_of_decay`), which follows
from display (5.42) (`exists_cubeRho_majorant_of_decay`, given the bound of Lemma 5.9) and the
localization of the partition.

The local regions of neighbouring cubes overlap, so the subcubes are grouped by their position `a`
inside the triadic cube of scale `n + 3` containing them: the cubes `⟨n, a + 27 b⟩`, `b` ranging
over the indices of a cube of scale `j`, have pairwise disjoint local regions
(`disjoint_localRegion_add_smul`). Each of the `27ᵈ` groups is concentrated by the Chernoff bound
`Rigidity.Proofs.Cluster.measureReal_sum_ge_le_of_bounded`, and a union bound over the groups gives

`P[∑_a ∑_b ρ_stat(⟨n, a + 27 b⟩) ∧ C₁ > 27ᵈ 3^{dj} t]
  ≤ 27ᵈ exp(-3^{dj} (t - (e - 1) C (1 + C₁) rⁿ) / C₁)`

(`measureReal_sum_min_cubeRhoStat_gt_le_of_decay`). This is the general-dimensional form of
`Rigidity.Proofs.Cluster.planar_SIupgrade_step2`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped Classical Matrix ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- At the cube at the origin, the stationary version of `ρ` is the local version. -/
theorem cubeRhoStat_atOrigin (p : unitInterval) (V : TriadicCube d) (ω : Configuration d) :
    cubeRhoStat p V.atOrigin ω = cubeRhoLoc p V.atOrigin ω := by
  have hc : V.atOrigin.center = 0 := funext fun i => by
    simp [TriadicCube.center, TriadicCube.atOrigin]
  unfold cubeRhoStat
  rw [hc, neg_zero, configurationTranslation_zero]
  rfl

/-- `exp(-c 3ⁿ) ≤ c⁻¹ rⁿ` for `r ≥ 1/3`. -/
theorem exp_neg_mul_three_pow_le_inv_mul_pow {c r : ℝ} (hc : 0 < c) (hr : 1 / 3 ≤ r) (n : ℕ) :
    Real.exp (-c * (3 : ℝ) ^ n) ≤ c⁻¹ * r ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h1 : Real.exp (-c * (3 : ℝ) ^ n) ≤ (c * (3 : ℝ) ^ n)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    refine inv_anti₀ (by positivity) ?_
    have := Real.add_one_le_exp (c * (3 : ℝ) ^ n)
    linarith
  have h2 : ((3 : ℝ) ^ n)⁻¹ ≤ r ^ n := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (by rw [← one_div]; exact hr) n
  calc Real.exp (-c * (3 : ℝ) ^ n) ≤ (c * (3 : ℝ) ^ n)⁻¹ := h1
    _ = c⁻¹ * ((3 : ℝ) ^ n)⁻¹ := by rw [mul_inv]
    _ ≤ c⁻¹ * r ^ n := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc.le)

/-- **The expectation of the truncated stationary version** (every dimension `d ≥ 2`, given the
bound of Lemma 5.9): `E[ρ_stat(V) ∧ C₁] ≤ C (1 + C₁) r^n` for every triadic cube `V` of scale `n`,
from display (5.42) and the localization of the partition. -/
theorem exists_integral_min_cubeRhoStat_le_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ C r : ℝ, 0 ≤ C ∧ 1 / 3 ≤ r ∧ r < 1 ∧ ∀ (V : TriadicCube d) {C₁ : ℝ}, 0 ≤ C₁ →
      ∫ ω, min (cubeRhoStat p V ω) C₁ ∂(latticeBondLaw d p) ≤ C * (1 + C₁) * r ^ V.scale := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, r₀, hC, hr₀0, hr₀1, hM⟩ :=
    exists_cubeRho_majorant_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨Cg, hCg, c, hc, hloc⟩ := exists_measure_not_cubeLocalGood_le hd hpc
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = max r₀ (1 / 3) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_max_of_lt_left hr₀0
  have hr13 : 1 / 3 ≤ r := by rw [hr]; exact le_max_right _ _
  have hr1 : r < 1 := by rw [hr]; exact max_lt hr₀1 (by norm_num)
  refine ⟨C + Cg.toReal * c⁻¹, r, by positivity, hr13, hr1, fun V C₁ hC₁ => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set n := V.scale with hn
  have hg : Continuous fun y : ℝ => min y C₁ := continuous_id.min continuous_const
  have hmap := map_cubeRhoStat_shift p (V := V.atOrigin) (z := V.center)
    V.atOrigin_side_dvd_center
  rw [V.atOrigin_shift_center] at hmap
  have e1 : ∫ ω, min (cubeRhoStat p V ω) C₁ ∂μ =
      ∫ y, min y C₁ ∂(μ.map (cubeRhoStat p V)) :=
    (integral_map (measurable_cubeRhoStat p V).aemeasurable hg.aestronglyMeasurable).symm
  have e2 : ∫ ω, min (cubeRhoStat p V.atOrigin ω) C₁ ∂μ =
      ∫ y, min y C₁ ∂(μ.map (cubeRhoStat p V.atOrigin)) :=
    (integral_map (measurable_cubeRhoStat p _).aemeasurable hg.aestronglyMeasurable).symm
  rw [e1, hmap, ← e2]
  simp only [cubeRhoStat_atOrigin]
  set W : TriadicCube d := V.atOrigin with hW
  obtain ⟨Φ, hΦi, hΦle, hΦint⟩ := hM n
  have hpt : ∀ᵐ ω ∂μ, min (cubeRhoLoc p W ω) C₁ ≤
      Φ ω + {ω | ¬ CubeLocalGood ω W}.indicator (fun _ => C₁) ω := by
    filter_upwards [hΦle] with ω hω
    by_cases hgood : CubeLocalGood ω W
    · have h0 : {ω | ¬ CubeLocalGood ω W}.indicator (fun _ => C₁) ω = 0 := by
        simp [hgood]
      rw [h0, add_zero]
      refine (min_le_left _ _).trans ?_
      rw [cubeRhoLoc_eq_of_good p hgood]
      exact hω
    · have h1 : {ω | ¬ CubeLocalGood ω W}.indicator (fun _ => C₁) ω = C₁ := by
        simp [hgood]
      rw [h1]
      have hΦ0 : 0 ≤ Φ ω := (cubeRho_nonneg hd0 p ω _).trans hω
      linarith [min_le_right (cubeRhoLoc p W ω) C₁]
  have hS : MeasurableSet {ω | ¬ CubeLocalGood ω W} := (measurableSet_cubeLocalGood W).compl
  have hind : Integrable ({ω | ¬ CubeLocalGood ω W}.indicator (fun _ => C₁)) μ :=
    (integrable_const C₁).indicator hS
  have hmin_i : Integrable (fun ω => min (cubeRhoLoc p W ω) C₁) μ :=
    (integrable_const C₁).mono'
      ((measurable_cubeRhoLoc p W).min measurable_const).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (cubeRhoLoc_nonneg hd0 p W ω) hC₁)]
        exact min_le_right _ _)
  have hsum_i : Integrable (fun ω => Φ ω + {ω | ¬ CubeLocalGood ω W}.indicator (fun _ => C₁) ω)
      μ := hΦi.add hind
  have h1 := integral_mono_ae hmin_i hsum_i hpt
  rw [integral_add hΦi hind, integral_indicator_const _ hS,
    smul_eq_mul] at h1
  have hP : μ.real {ω | ¬ CubeLocalGood ω W} ≤ Cg.toReal * Real.exp (-c * (3 : ℝ) ^ n) := by
    have h := hloc W
    have hfin : Cg * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ W.scale)) ≠ ∞ := by finiteness
    calc μ.real {ω | ¬ CubeLocalGood ω W} = (μ {ω | ¬ CubeLocalGood ω W}).toReal := rfl
      _ ≤ (Cg * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ W.scale))).toReal :=
          ENNReal.toReal_mono hfin h
      _ = Cg.toReal * Real.exp (-c * (3 : ℝ) ^ n) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
          rfl
  have hexp := exp_neg_mul_three_pow_le_inv_mul_pow (r := r) hc
    (by rw [hr]; exact le_max_right _ _) n
  have hrr : r₀ ^ n ≤ r ^ n := pow_le_pow_left₀ hr₀0.le (by rw [hr]; exact le_max_left _ _) n
  have hCg0 : 0 ≤ Cg.toReal := ENNReal.toReal_nonneg
  have hrn : 0 ≤ r ^ n := by positivity
  have k1 : ∫ ω, Φ ω ∂μ ≤ C * r ^ n := hΦint.trans (mul_le_mul_of_nonneg_left hrr hC)
  have k2 : μ.real {ω | ¬ CubeLocalGood ω W} * C₁ ≤ Cg.toReal * c⁻¹ * r ^ n * C₁ := by
    have := mul_le_mul_of_nonneg_left hexp hCg0
    have h3 : μ.real {ω | ¬ CubeLocalGood ω W} ≤ Cg.toReal * c⁻¹ * r ^ n := by
      calc μ.real {ω | ¬ CubeLocalGood ω W} ≤ Cg.toReal * Real.exp (-c * (3 : ℝ) ^ n) := hP
        _ ≤ Cg.toReal * (c⁻¹ * r ^ n) := this
        _ = Cg.toReal * c⁻¹ * r ^ n := by ring
    exact mul_le_mul_of_nonneg_right h3 hC₁
  have k3 : C * r ^ n + Cg.toReal * c⁻¹ * r ^ n * C₁ ≤
      (C + Cg.toReal * c⁻¹) * (1 + C₁) * r ^ n := by
    have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    nlinarith [mul_nonneg (mul_nonneg hC hC₁) hrn, mul_nonneg (mul_nonneg hCg0 hci) hrn]
  linarith

/-- The cubes `⟨n, a + 27 b⟩` for distinct `b` have disjoint local regions. -/
theorem disjoint_localRegion_add_smul (n : ℕ) (a : Vertex d) {b b' : Vertex d}
    (hbb : b ≠ b') :
    Disjoint (⟨n, a + (27 : ℤ) • b⟩ : TriadicCube d).localRegion
      (⟨n, a + (27 : ℤ) • b'⟩ : TriadicCube d).localRegion := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hbb
  rw [Set.disjoint_left]
  intro y hy hy'
  have h1 := hy i
  have h2 := hy' i
  simp only [TriadicCube.center, TriadicCube.side, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at h1 h2
  set s : ℤ := (3 : ℤ) ^ n with hs
  have hs0 : 0 < s := by positivity
  have hd : 1 ≤ |b i - b' i| := Int.one_le_abs (sub_ne_zero.2 hi)
  have key : |s * (a i + 27 * b i) - s * (a i + 27 * b' i)| ≤ 14 * s := by
    calc |s * (a i + 27 * b i) - s * (a i + 27 * b' i)|
        = |(y i - s * (a i + 27 * b' i)) - (y i - s * (a i + 27 * b i))| := by ring_nf
      _ ≤ |y i - s * (a i + 27 * b' i)| + |y i - s * (a i + 27 * b i)| := abs_sub _ _
      _ ≤ 7 * s + 7 * s := add_le_add h2 h1
      _ = 14 * s := by ring
  have e : |s * (a i + 27 * b i) - s * (a i + 27 * b' i)| = 27 * s * |b i - b' i| := by
    rw [show s * (a i + 27 * b i) - s * (a i + 27 * b' i) = (27 * s) * (b i - b' i) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 27 * s)]
  rw [e] at key
  nlinarith

/-- **Step 2 of the proof of Lemma 5.11 of Armstrong and Dario** (every dimension `d ≥ 2`, given
the bound of Lemma 5.9): with `A` the indices of the cube of scale `3` and `B` those of the cube
of scale `j` at the origin,
`P[∑_{a ∈ A} ∑_{b ∈ B} ρ_stat(⟨n, a + 27 b⟩) ∧ C₁ > |A| |B| t]
  ≤ |A| exp(-|B| (t - (e - 1) C (1 + C₁) rⁿ) / C₁)`. -/
theorem measureReal_sum_min_cubeRhoStat_gt_le_of_decay [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ}
    (hC₉ : 0 ≤ C₉) (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ C r : ℝ, 0 ≤ C ∧ 1 / 3 ≤ r ∧ r < 1 ∧ ∀ (n j : ℕ) {C₁ : ℝ}, 0 < C₁ → ∀ t : ℝ,
      (latticeBondLaw d p).real {ω |
        ((⟨3, 0⟩ : TriadicCube d).toIntegerCube.vertices.card : ℝ) *
          ((⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices.card * t) <
        ∑ a ∈ (⟨3, 0⟩ : TriadicCube d).toIntegerCube.vertices,
          ∑ b ∈ (⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices,
            min (cubeRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁} ≤
        ((⟨3, 0⟩ : TriadicCube d).toIntegerCube.vertices.card : ℝ) *
          Real.exp (-(((⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices.card : ℝ) *
            (t - (Real.exp 1 - 1) * (C * (1 + C₁) * r ^ n))) / C₁) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, r, hC, hr13, hr1, hE⟩ :=
    exists_integral_min_cubeRhoStat_le_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  refine ⟨C, r, hC, hr13, hr1, fun n j C₁ hC₁ t => ?_⟩
  set A := (⟨3, 0⟩ : TriadicCube d).toIntegerCube.vertices with hA
  set B := (⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices with hB
  set X : Vertex d → Vertex d → Configuration d → ℝ := fun a b ω =>
    min (cubeRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁ with hX
  have hg : Measurable fun y : ℝ => min y C₁ := measurable_id.min measurable_const
  have hgroup : ∀ a ∈ A, (latticeBondLaw d p).real {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω} ≤
      Real.exp (-((B.card : ℝ) * (t - (Real.exp 1 - 1) * (C * (1 + C₁) * r ^ n))) / C₁) := by
    intro a _
    refine Rigidity.Proofs.Cluster.measureReal_sum_ge_le_of_bounded B (X a)
      (fun b => (measurable_cubeRhoStat p _).min measurable_const) hC₁
      (fun b ω => le_min (cubeRhoStat_nonneg hd0 p _ ω) hC₁.le) (fun b ω => min_le_right _ _)
      (fun b _ => hE ⟨n, a + (27 : ℤ) • b⟩ hC₁.le) (fun b hb T hT hbT => ?_) t
    exact indepFun_comp_cubeRhoStat_sum p (fun b => (⟨n, a + (27 : ℤ) • b⟩ : TriadicCube d)) hg
      (fun b _ b' _ hbb => disjoint_localRegion_add_smul n a hbb) hb hT hbT
  have hsub : {ω | (A.card : ℝ) * ((B.card : ℝ) * t) < ∑ a ∈ A, ∑ b ∈ B, X a b ω} ⊆
      ⋃ a ∈ A, {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω} := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hne
    have : ∑ a ∈ A, ∑ b ∈ B, X a b ω ≤ ∑ _a ∈ A, (B.card : ℝ) * t :=
      Finset.sum_le_sum fun a ha => (hne a ha).le
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact absurd hω (not_lt.2 this)
  calc (latticeBondLaw d p).real
        {ω | (A.card : ℝ) * ((B.card : ℝ) * t) < ∑ a ∈ A, ∑ b ∈ B, X a b ω}
      ≤ (latticeBondLaw d p).real (⋃ a ∈ A, {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ a ∈ A, (latticeBondLaw d p).real {ω | (B.card : ℝ) * t ≤ ∑ b ∈ B, X a b ω} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ A, Real.exp (-((B.card : ℝ) *
          (t - (Real.exp 1 - 1) * (C * (1 + C₁) * r ^ n))) / C₁) :=
        Finset.sum_le_sum hgroup
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Rigidity.Percolation
