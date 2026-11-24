import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaBound

/-!
# The expectation of the pointwise bound of the proof of Lemma 5.9, in every dimension

Let `X = ν(□_n, p) + 1{P, □_n res} (-μ(□_n, q)) - q · p`, whose expectation is the term of `D_n`.
Let `Bad` be a measurable set containing the event that some vertex of `□_{n+1}` has a partition
cube of scale larger than `ℓ`. Almost surely,

`X ≤ c₀ + 3 M_ν / |□_n| + K_n 4 |□_{n+1}| (F_v + F_u) + 1_Bad (ν(□_n, p) + 1{P, □_n res}(-μ) + |q · p|)
  + 3 D^μ_n / |□_n|`

(the pointwise bound on the complement of `Bad`, `cubeOmega_le_of_sizeLe`, and the nonnegativity of
the terms on `Bad`). All terms but the last are integrable; the last, the energy of the differences
of the minimizers of `μ`, enters through its lower integral (`integral_le_add_of_le_add`). This
gives the bound of `E[X]` of `integral_cubeOmegaX_le`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **An integral bounded through an integrable majorant and a lower integral.** If `X ≤ A + B`
almost everywhere with `X`, `A` integrable and `B ≥ 0`, then `E[X] ≤ E[A] + (∫⁻ B)`. -/
theorem integral_le_add_of_le_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X A B : Ω → ℝ} (hX : Integrable X μ) (hA : Integrable A μ) (hle : ∀ᵐ ω ∂μ, X ω ≤ A ω + B ω)
    {b : ℝ} (hb : 0 ≤ b) (hB : ∫⁻ ω, ENNReal.ofReal (B ω) ∂μ ≤ ENNReal.ofReal b) :
    ∫ ω, X ω ∂μ ≤ ∫ ω, A ω ∂μ + b := by
  have hXA := hX.sub hA
  have h1 : ∫ ω, (X ω - A ω) ∂μ ≤ ∫ ω, max (X ω - A ω) 0 ∂μ :=
    integral_mono hXA hXA.pos_part fun ω => le_max_left _ _
  have hm : AEStronglyMeasurable (fun ω => max (X ω - A ω) 0) μ :=
    (hXA.aestronglyMeasurable.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  have h2 : ∫ ω, max (X ω - A ω) 0 ∂μ = (∫⁻ ω, ENNReal.ofReal (X ω - A ω) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => max (X ω - A ω) 0)
      (ae_of_all _ fun ω => le_max_right _ _) hm]
    congr 1
    refine lintegral_congr fun ω => ?_
    rcases le_total (X ω - A ω) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  have h3 : ∫⁻ ω, ENNReal.ofReal (X ω - A ω) ∂μ ≤ ENNReal.ofReal b :=
    (lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal (by linarith))).trans hB
  have h4 : (∫⁻ ω, ENNReal.ofReal (X ω - A ω) ∂μ).toReal ≤ b := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    rwa [ENNReal.toReal_ofReal hb] at this
  rw [integral_sub hX hA] at h1
  linarith

variable {p : unitInterval}

/-- The integrand of a term of `D_n`. -/
noncomputable def cubeOmegaX (ω : Configuration d) (n : ℕ) (p' q : Fin d → ℝ) : ℝ :=
  cubeNu ω ⟨n, 0⟩ p' +
    (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
      -cubeMu ω ⟨n, 0⟩ q else 0) - ∑ i, q i * p' i

theorem integrable_cubeOmegaX [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (n : ℕ) (p' q : Fin d → ℝ) :
    Integrable (fun ω => cubeOmegaX ω n p' q) (latticeBondLaw d p) :=
  ((integrable_cubeNu p _ p').add (integrable_neg_cubeMu_indicator hd hpc _ q)).sub
    (integrable_const _)

/-- The exceptional count as a function of the configuration is measurable and integrable. -/
theorem integrable_card_filter_exceptionalMajorant (U : TriadicCube d) (n : ℕ) :
    Integrable (fun ω : Configuration d =>
      ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ))
      (latticeBondLaw d p) := by
  have e : (fun ω : Configuration d =>
      ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ)) =
      fun ω => ∑ x ∈ U.toIntegerCube.vertices,
        {ω' : Configuration d | ExceptionalMajorant ω' n x}.indicator 1 ω := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : ExceptionalMajorant ω n x
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω' | ExceptionalMajorant ω' n x} from h),
        Pi.one_apply]
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω' | ExceptionalMajorant ω' n x} from h)]
  rw [e]
  exact integrable_finsetSum _ fun x _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_exceptionalMajorant n x)

theorem integrable_nuDefectMajorant (n : ℕ) (p' : Fin d → ℝ) :
    Integrable (fun ω => nuDefectMajorant ω n p') (latticeBondLaw d p) := by
  unfold nuDefectMajorant
  refine ((integrable_finsetSum _ fun x _ => integrable_cubeNu p _ p').sub
    ((integrable_cubeNu p _ p').mul_const _)).add ?_
  exact (((integrable_card_filter_exceptionalMajorant _ n).const_mul _).add
    (integrable_const _)).const_mul _

/-- The energy of the differences of the maximizers of `ν` is at most its majorant. -/
theorem cubeNuDefect_le_nuDefectMajorant (hd : 0 < d) {ω : Configuration d}
    (hP : PartitionEvent ω) (n : ℕ) (p' : Fin d → ℝ) :
    cubeNuDefect ω ⟨n + 1, 0⟩ n p' ≤ nuDefectMajorant ω n p' := by
  have hsn : (0 : ℝ) < √3 ^ n := by positivity
  have h := cubeNuDefect_add_le hd hP (U := ⟨n + 1, 0⟩)
    (show n ≤ (⟨n + 1, 0⟩ : TriadicCube d).scale by change n ≤ n + 1; omega) p' hsn
  have hc := subcubeExceptionalCount_le hP (⟨n + 1, 0⟩ : TriadicCube d) n
  unfold nuDefectMajorant
  have hK : 0 ≤ 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hc hsn.le)
    ((⟨n + 1, 0⟩ : TriadicCube d).latticeVolume / √3 ^ n)) hK
  linarith

theorem integrable_of_lintegral_le {f : Configuration d → ℝ} (hm : Measurable f)
    (h0 : ∀ ω, 0 ≤ f ω) {b : ℝ} (hb : ∫⁻ ω, ENNReal.ofReal (f ω) ∂(latticeBondLaw d p) ≤
      ENNReal.ofReal b) : Integrable f (latticeBondLaw d p) := by
  have hfin : ∫⁻ ω, ENNReal.ofReal (f ω) ∂(latticeBondLaw d p) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have h := integrable_toReal_of_lintegral_ne_top hm.ennreal_ofReal.aemeasurable hfin
  exact h.congr (ae_of_all _ fun ω => ENNReal.toReal_ofReal (h0 ω))

/-- **The expectation of the pointwise bound** (proof of Lemma 5.9, every dimension `d ≥ 2`). -/
theorem integral_cubeOmegaX_le [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ ≤ n) (p' q ξ : Fin d → ℝ) {bv bu bD : ℝ}
    (hbv0 : 0 ≤ bv) (hbu0 : 0 ≤ bu) (hbD0 : 0 ≤ bD)
    (hFv : ∫⁻ ω, ENNReal.ofReal (cubeFlatnessError ⟨n + 1, 0⟩ (fun x => cubeExtend ω ⟨n + 1, 0⟩
        (cubeNuSolution ω ⟨n + 1, 0⟩ p') (partitionAnchor ω x)) ξ) ∂(latticeBondLaw d p) ≤
      ENNReal.ofReal bv)
    (hFu : ∫⁻ ω, ENNReal.ofReal (cubeFlatnessError ⟨n + 1, 0⟩ (fun x => cubeExtend ω ⟨n + 1, 0⟩
        (cubeMuMinimizer ω ⟨n + 1, 0⟩ q) (partitionAnchor ω x)) ξ) ∂(latticeBondLaw d p) ≤
      ENNReal.ofReal bu)
    (hDμ : ∫⁻ ω, ENNReal.ofReal (cubeMuDefect ω ⟨n + 1, 0⟩ n q) ∂(latticeBondLaw d p) ≤
      ENNReal.ofReal bD) :
    ∫ ω, cubeOmegaX ω n p' q ∂(latticeBondLaw d p) ≤
      omegaConst d n ℓ p' q +
        3 * (∫ ω, nuDefectMajorant ω n p' ∂(latticeBondLaw d p)) /
          (⟨n, 0⟩ : TriadicCube d).latticeVolume +
        caccioppoliFactor d n * (4 * (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume * (bv + bu)) +
        ∫ ω, (toMeasurable (latticeBondLaw d p)
            {ω : Configuration d | ¬ PartitionSizeLe ω ⟨n + 1, 0⟩ ℓ}).indicator
          (fun ω => cubeNu ω ⟨n, 0⟩ p' +
            (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
              -cubeMu ω ⟨n, 0⟩ q else 0) + |∑ i, q i * p' i|) ω ∂(latticeBondLaw d p) +
        3 * bD / (⟨n, 0⟩ : TriadicCube d).latticeVolume := by
  have hd0 : 0 < d := by omega
  set μ := latticeBondLaw d p with hμ
  set V : TriadicCube d := ⟨n, 0⟩ with hV
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  set Bad := toMeasurable μ {ω : Configuration d | ¬ PartitionSizeLe ω U ℓ} with hBad
  have hBadm : MeasurableSet Bad := measurableSet_toMeasurable _ _
  set Fv : Configuration d → ℝ := fun ω => cubeFlatnessError U (fun x => cubeExtend ω U
    (cubeNuSolution ω U p') (partitionAnchor ω x)) ξ with hFvdef
  set Fu : Configuration d → ℝ := fun ω => cubeFlatnessError U (fun x => cubeExtend ω U
    (cubeMuMinimizer ω U q) (partitionAnchor ω x)) ξ with hFudef
  have hF0 : ∀ (w : Vertex d → ℝ), 0 ≤ cubeFlatnessError U w ξ := fun w =>
    mul_nonneg (inv_nonneg.2 U.latticeVolume_pos.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hFvi : Integrable Fv μ := integrable_of_lintegral_le
    (measurable_cubeFlatnessError_cubeNuSolution hd0 U p' ξ) (fun ω => hF0 _) hFv
  have hFui : Integrable Fu μ := integrable_of_lintegral_le
    (measurable_cubeFlatnessError_cubeMuMinimizer hd0 U q ξ) (fun ω => hF0 _) hFu
  set Y : Configuration d → ℝ := fun ω => cubeNu ω V p' +
    (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) +
      |∑ i, q i * p' i| with hYdef
  have hYi : Integrable Y μ := ((integrable_cubeNu p _ p').add
    (integrable_neg_cubeMu_indicator hd hpc _ q)).add (integrable_const _)
  set c₀ := omegaConst d n ℓ p' q with hc₀
  set K := caccioppoliFactor d n with hK
  have hK0 : 0 ≤ K := caccioppoliFactor_nonneg d n
  set A : Configuration d → ℝ := fun ω => c₀ + 3 * nuDefectMajorant ω n p' / V.latticeVolume +
    K * (4 * U.latticeVolume * (Fv ω + Fu ω)) + Bad.indicator Y ω with hAdef
  set B : Configuration d → ℝ := fun ω => 3 * cubeMuDefect ω U n q / V.latticeVolume with hBdef
  have hvolV := V.latticeVolume_pos
  have hc00 : 0 ≤ c₀ := by
    rw [hc₀]
    unfold omegaConst
    have := comparisonCap_nonneg d ℓ
    have := coarseningConst_nonneg d
    have hq0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hp0 : 0 ≤ ∑ i, |p' i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hqq : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := U.latticeVolume_pos
    positivity
  have hAi : Integrable A μ := by
    refine (((integrable_const c₀).add (((integrable_nuDefectMajorant (p := p) n p').const_mul
      3).div_const _)).add (((hFvi.add hFui).const_mul _).const_mul K)).add
      (hYi.indicator hBadm)
  have hle : ∀ᵐ ω ∂μ, cubeOmegaX ω n p' q ≤ A ω + B ω := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hP
    by_cases hω : ω ∈ Bad
    · have hMν : 0 ≤ nuDefectMajorant ω n p' :=
        (cubeNuDefect_nonneg _ _ _).trans (cubeNuDefect_le_nuDefectMajorant hd0 hP n p')
      have hD0 : 0 ≤ cubeMuDefect ω U n q := cubeMuDefect_nonneg _ _ _ _
      simp only [hAdef, hBdef, Set.indicator_of_mem hω, hYdef]
      unfold cubeOmegaX
      have h1 : 0 ≤ 3 * nuDefectMajorant ω n p' / V.latticeVolume := by positivity
      have h2 : 0 ≤ K * (4 * U.latticeVolume * (Fv ω + Fu ω)) := by
        have := hF0 (fun x => cubeExtend ω U (cubeNuSolution ω U p') (partitionAnchor ω x))
        have := hF0 (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x))
        have := U.latticeVolume_pos
        positivity
      have h3 : 0 ≤ 3 * cubeMuDefect ω U n q / V.latticeVolume := by positivity
      have h4 := neg_abs_le (∑ i, q i * p' i)
      linarith
    · have hS : PartitionSizeLe ω U ℓ := by
        by_contra h
        exact hω (subset_toMeasurable _ _ h)
      have hb := cubeOmega_le_of_sizeLe hd0 hn hℓ hS p' q ξ
      have hVres : PartitionResolved ω V := hS.resolved (by
        intro x hx
        rw [mem_vertices_originCube_iff] at hx ⊢
        intro i
        have h1 := hx i
        have h2 : (3 : ℤ) ^ n ≤ 3 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
        linarith) hℓ
      simp only [hAdef, hBdef, Set.indicator_of_notMem hω, add_zero]
      unfold cubeOmegaX
      rw [if_pos ⟨hP, hVres⟩]
      have e : 3 * (nuDefectMajorant ω n p' + cubeMuDefect ω U n q) / V.latticeVolume =
          3 * nuDefectMajorant ω n p' / V.latticeVolume +
            3 * cubeMuDefect ω U n q / V.latticeVolume := by ring
      rw [e] at hb
      linarith
  have hB : ∫⁻ ω, ENNReal.ofReal (B ω) ∂μ ≤ ENNReal.ofReal (3 * bD / V.latticeVolume) := by
    have hpt : ∀ ω, ENNReal.ofReal (B ω) =
        ENNReal.ofReal (3 / V.latticeVolume) * ENNReal.ofReal (cubeMuDefect ω U n q) := by
      intro ω
      rw [← ENNReal.ofReal_mul (by positivity), hBdef]
      congr 1
      ring
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_of_nonneg_left hDμ zero_le).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  refine (integral_le_add_of_le_add (integrable_cubeOmegaX hd hpc n p' q) hAi hle
    (by positivity) hB).trans ?_
  have hint : ∫ ω, A ω ∂μ = c₀ + 3 * (∫ ω, nuDefectMajorant ω n p' ∂μ) / V.latticeVolume +
      K * (4 * U.latticeVolume * (∫ ω, Fv ω ∂μ + ∫ ω, Fu ω ∂μ)) +
      ∫ ω, Bad.indicator Y ω ∂μ := by
    have hM3 : Integrable (fun ω => 3 * nuDefectMajorant ω n p' / V.latticeVolume) μ :=
      ((integrable_nuDefectMajorant (p := p) n p').const_mul 3).div_const _
    have hFK : Integrable (fun ω => K * (4 * U.latticeVolume * (Fv ω + Fu ω))) μ :=
      ((hFvi.add hFui).const_mul _).const_mul K
    have e1 : ∫ ω, A ω ∂μ = ∫ ω, (c₀ + 3 * nuDefectMajorant ω n p' / V.latticeVolume +
        K * (4 * U.latticeVolume * (Fv ω + Fu ω))) ∂μ + ∫ ω, Bad.indicator Y ω ∂μ := by
      rw [hAdef]
      exact integral_add (((integrable_const c₀).add hM3).add hFK) (hYi.indicator hBadm)
    have e2 : ∫ ω, (c₀ + 3 * nuDefectMajorant ω n p' / V.latticeVolume +
        K * (4 * U.latticeVolume * (Fv ω + Fu ω))) ∂μ =
        ∫ ω, (c₀ + 3 * nuDefectMajorant ω n p' / V.latticeVolume) ∂μ +
          ∫ ω, K * (4 * U.latticeVolume * (Fv ω + Fu ω)) ∂μ :=
      integral_add ((integrable_const c₀).add hM3) hFK
    have e3 : ∫ ω, (c₀ + 3 * nuDefectMajorant ω n p' / V.latticeVolume) ∂μ =
        ∫ _ω, c₀ ∂μ + ∫ ω, 3 * nuDefectMajorant ω n p' / V.latticeVolume ∂μ :=
      integral_add (integrable_const c₀) hM3
    have e4 : ∫ ω, 3 * nuDefectMajorant ω n p' / V.latticeVolume ∂μ =
        3 * (∫ ω, nuDefectMajorant ω n p' ∂μ) / V.latticeVolume := by
      rw [integral_div, integral_const_mul]
    have e5 : ∫ ω, K * (4 * U.latticeVolume * (Fv ω + Fu ω)) ∂μ =
        K * (4 * U.latticeVolume * (∫ ω, Fv ω ∂μ + ∫ ω, Fu ω ∂μ)) := by
      rw [integral_const_mul, integral_const_mul, integral_add hFvi hFui]
    have e6 : ∫ _ω, c₀ ∂μ = c₀ := by simp
    rw [e1, e2, e3, e4, e5, e6]
  rw [hint]
  have hv : ∫ ω, Fv ω ∂μ ≤ bv := integral_le_of_lintegral_le_ofReal (fun ω => hF0 _)
    (measurable_cubeFlatnessError_cubeNuSolution hd0 U p' ξ) hbv0 hFv
  have hu : ∫ ω, Fu ω ∂μ ≤ bu := integral_le_of_lintegral_le_ofReal (fun ω => hF0 _)
    (measurable_cubeFlatnessError_cubeMuMinimizer hd0 U q ξ) hbu0 hFu
  have h4U : 0 ≤ 4 * U.latticeVolume := by have := U.latticeVolume_pos; positivity
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hv hu) h4U) hK0
  linarith

end Rigidity.Percolation
