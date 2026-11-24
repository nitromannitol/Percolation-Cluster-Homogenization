import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaIntegral
import PercolationClusterHomogenization.Proofs.Cluster.PlanarReachConcentrationHolds
import PercolationClusterHomogenization.Proofs.Partition.PartitionSize

/-!
# The expectations of the error terms of the proof of Lemma 5.9, in every dimension

* `integral_nuDefectMajorant_le`: the expectation of the subadditivity majorant of `D^ν_n` is at most
  `|□_{n+1}| (E[ν(□_n, p)] - E[ν(□_{n+1}, p)] + C |p|₁² 3^{-n/2})`;
* `exists_measure_omegaBad_le`: the event that some vertex of `□_{n+1}` has a partition cube of
  scale larger than `⌊n / 4d⌋` has probability at most `C 9^{-n}`;
* `exists_integral_omegaBad_le`: the contribution of that event to the expectation of a term of
  `D_n` is at most `C (1 + |p|₁² + |q · p| + |q|²) 3^{-n}`, by the bound `-μ(□_n, q) ≤ |q|² K_μ` of
  Lemma 4.4, the inequality `1_E S ≤ T 1_E + S² / T` and the moments of the partition sizes.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {p : unitInterval}

/-- **The expectation of the subadditivity majorant of `D^ν_n`.** -/
theorem exists_integral_nuDefectMajorant_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (p' : Fin d → ℝ),
      ∫ ω, nuDefectMajorant ω n p' ∂(latticeBondLaw d p) ≤
        (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume * (cubeNuMean p n p' -
          cubeNuMean p (n + 1) p' + C * (∑ i, |p' i|) ^ 2 / √3 ^ n) := by
  obtain ⟨C, hC, herr⟩ := exists_exceptional_error_le hd hpc
  refine ⟨3 ^ d / 4 * C, by positivity, fun n p' => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hU
  set t := √3 ^ n with ht
  have ht0 : 0 < t := by positivity
  have hvol := U.latticeVolume_pos
  have hInd : ∀ x, Integrable ({ω : Configuration d | ExceptionalMajorant ω n x}.indicator
      (1 : Configuration d → ℝ)) μ := fun x =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_exceptionalMajorant n x)
  have hcard : (fun ω : Configuration d =>
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
  have hGint := integrable_card_filter_exceptionalMajorant (p := p) U n
  have hGval : ∫ ω, ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) ∂μ =
      ∑ x ∈ U.toIntegerCube.vertices, (μ {ω | ExceptionalMajorant ω n x}).toReal := by
    rw [hcard, integral_finsetSum _ fun x _ => hInd x]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_indicator_one (measurableSet_exceptionalMajorant n x)]
    rfl
  have hint_s : Integrable (fun ω => ∑ x ∈ U.toIntegerCube.vertices,
      cubeNu ω (triadicCubeAt n x) p') μ :=
    integrable_finsetSum _ fun x _ => integrable_cubeNu p _ p'
  have hS : ∫ ω, ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p' ∂μ =
      U.latticeVolume * cubeNuMean p n p' := by
    rw [integral_finsetSum _ fun x _ => integrable_cubeNu p _ p',
      Finset.sum_congr rfl fun x _ => integral_cubeNu_eq_of_scale_eq (U := ⟨n, 0⟩) p
        (scale_triadicCubeAt n x).symm p', Finset.sum_const, nsmul_eq_mul,
      U.card_toIntegerCube_vertices]
    rfl
  have hint_U : Integrable (fun ω => cubeNu ω U p' * U.latticeVolume) μ :=
    (integrable_cubeNu p U p').mul_const _
  have hK0 : 0 ≤ 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 := by positivity
  have hint_G : Integrable (fun ω => 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 *
      (t * ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) +
        U.latticeVolume / t)) μ :=
    ((hGint.const_mul t).add (integrable_const _)).const_mul _
  have hval : ∫ ω, nuDefectMajorant ω n p' ∂μ = U.latticeVolume * cubeNuMean p n p' -
      cubeNuMean p (n + 1) p' * U.latticeVolume + 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 *
        (t * ∑ x ∈ U.toIntegerCube.vertices, (μ {ω | ExceptionalMajorant ω n x}).toReal +
          U.latticeVolume / t) := by
    have hsU : Integrable (fun ω => ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p' -
        cubeNu ω U p' * U.latticeVolume) μ := hint_s.sub hint_U
    have e1 : ∫ ω, nuDefectMajorant ω n p' ∂μ =
        ∫ ω, (∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p' -
          cubeNu ω U p' * U.latticeVolume) ∂μ +
        ∫ ω, 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 *
          (t * ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) +
            U.latticeVolume / t) ∂μ := by
      unfold nuDefectMajorant
      exact integral_add hsU hint_G
    have e2 : ∫ ω, (∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p' -
          cubeNu ω U p' * U.latticeVolume) ∂μ =
        ∫ ω, ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p' ∂μ -
          ∫ ω, cubeNu ω U p' * U.latticeVolume ∂μ := integral_sub hint_s hint_U
    have e3 : ∫ ω, cubeNu ω U p' * U.latticeVolume ∂μ = cubeNuMean p (n + 1) p' * U.latticeVolume :=
      integral_mul_const _ _
    have e4 : ∫ ω, 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 *
        (t * ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) +
          U.latticeVolume / t) ∂μ = 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 *
        (t * ∑ x ∈ U.toIntegerCube.vertices, (μ {ω | ExceptionalMajorant ω n x}).toReal +
          U.latticeVolume / t) := by
      rw [integral_const_mul]
      congr 1
      have e5 : ∫ ω, (t * ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) +
          U.latticeVolume / t) ∂μ =
          ∫ ω, t * ((U.toIntegerCube.vertices.filter (ExceptionalMajorant ω n)).card : ℝ) ∂μ +
            ∫ _ω, U.latticeVolume / t ∂μ :=
        integral_add (hGint.const_mul t) (integrable_const _)
      rw [e5, integral_const_mul, hGval]
      simp
    rw [e1, e2, e3, e4, hS]
  rw [hval]
  have hb := herr U n (by change n ≤ n + 1; omega)
  have hK := mul_le_mul_of_nonneg_left hb hK0
  have e1 : 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 * (t * ∑ x ∈ U.toIntegerCube.vertices,
      (μ {ω | ExceptionalMajorant ω n x}).toReal + U.latticeVolume / t) =
      U.latticeVolume * (3 ^ d / 4 * (∑ i, |p' i|) ^ 2 *
        (t * (∑ x ∈ U.toIntegerCube.vertices,
          (μ {ω | ExceptionalMajorant ω n x}).toReal) / U.latticeVolume + 1 / t)) := by
    field_simp
  rw [e1]
  have := mul_le_mul_of_nonneg_left hK hvol.le
  have e2 : U.latticeVolume * (3 ^ d / 4 * (∑ i, |p' i|) ^ 2 * (C / t)) =
      U.latticeVolume * (3 ^ d / 4 * C * (∑ i, |p' i|) ^ 2 / t) := by ring
  rw [e2] at this
  nlinarith

/-- The cap scale `⌊n / 4d⌋` of the proof of Lemma 5.9. -/
def omegaCap (d n : ℕ) : ℕ := n / (4 * d)

/-- The event that some vertex of `□_{n+1}` has a partition cube of scale larger than
`⌊n / 4d⌋`, made measurable. -/
def omegaBad (p : unitInterval) (d n : ℕ) : Set (Configuration d) :=
  toMeasurable (latticeBondLaw d p)
    {ω : Configuration d | ¬ PartitionSizeLe ω ⟨n + 1, 0⟩ (omegaCap d n)}

theorem measurableSet_omegaBad (p : unitInterval) (d n : ℕ) : MeasurableSet (omegaBad p d n) :=
  measurableSet_toMeasurable _ _

theorem omegaCap_le (d n : ℕ) : omegaCap d n ≤ n := Nat.div_le_self _ _

theorem four_mul_omegaCap_le (d n : ℕ) : 4 * d * omegaCap d n ≤ n := Nat.mul_div_le n (4 * d)

theorem lt_four_mul_omegaCap_succ (hd : 0 < d) (n : ℕ) : n < 4 * d * (omegaCap d n + 1) :=
  Nat.lt_mul_div_succ n (by positivity)

/-- **The bad event of the proof of Lemma 5.9 is rare**: `P[E_n] ≤ C 9^{-n}`. -/
theorem exists_measure_omegaBad_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (latticeBondLaw d p (omegaBad p d n)).toReal ≤ C / 9 ^ n := by
  have hd0 : 0 < d := by omega
  obtain ⟨a, ha, hm⟩ := measure_not_partitionSizeLe_le hd hpc
  obtain ⟨K, hK, hexp⟩ := exists_exp_neg_rpow_le_inv_pow ha one_pos (4 * d * (d + 3))
  refine ⟨2 * K, by positivity, fun n => ?_⟩
  set ℓ := omegaCap d n with hℓ
  have h1 : latticeBondLaw d p (omegaBad p d n) ≤
      ENNReal.ofReal ((⟨n + 1, 0⟩ : TriadicCube d).latticeVolume *
        (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)))) := by
    rw [omegaBad, measure_toMeasurable]
    exact hm _ _
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal (by have := (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume_pos; positivity)]
    at h2
  refine h2.trans ?_
  have he := hexp (ℓ + 3)
  rw [Real.rpow_one] at he
  have hnat : (n + 1) * (d + 3) ≤ (ℓ + 3) * (4 * d * (d + 3)) := by
    have h := lt_four_mul_omegaCap_succ hd0 n
    rw [← hℓ] at h
    have h' : n + 1 ≤ 4 * d * (ℓ + 3) := by
      have : 4 * d * (ℓ + 1) ≤ 4 * d * (ℓ + 3) := Nat.mul_le_mul_left _ (by omega)
      omega
    calc (n + 1) * (d + 3) ≤ 4 * d * (ℓ + 3) * (d + 3) := Nat.mul_le_mul_right _ h'
      _ = (ℓ + 3) * (4 * d * (d + 3)) := by ring
  have hpow : ((3 : ℝ) ^ (ℓ + 3))⁻¹ ^ (4 * d * (d + 3)) ≤ ((3 : ℝ) ^ ((n + 1) * (d + 3)))⁻¹ := by
    rw [inv_pow, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hnat)
  have hvol : (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume = (3 : ℝ) ^ ((n + 1) * d) := by
    change ((3 : ℝ) ^ (n + 1)) ^ d = _
    rw [← pow_mul]
  rw [hvol]
  have h3 : (3 : ℝ) ^ ((n + 1) * d) * ((3 : ℝ) ^ ((n + 1) * (d + 3)))⁻¹ = ((3 : ℝ) ^ (3 * (n + 1)))⁻¹ := by
    rw [show (n + 1) * (d + 3) = (n + 1) * d + 3 * (n + 1) by ring, pow_add, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have h4 : ((3 : ℝ) ^ (3 * (n + 1)))⁻¹ ≤ 1 / 9 ^ n := by
    rw [one_div]
    refine inv_anti₀ (by positivity) ?_
    calc (9 : ℝ) ^ n = 3 ^ (2 * n) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ (3 * (n + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)) ≤ K * ((3 : ℝ) ^ ((n + 1) * (d + 3)))⁻¹ :=
    he.trans (mul_le_mul_of_nonneg_left hpow hK)
  calc (3 : ℝ) ^ ((n + 1) * d) * (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)))
      ≤ (3 : ℝ) ^ ((n + 1) * d) * (2 * (K * ((3 : ℝ) ^ ((n + 1) * (d + 3)))⁻¹)) := by gcongr
    _ = 2 * K * ((3 : ℝ) ^ ((n + 1) * d) * ((3 : ℝ) ^ ((n + 1) * (d + 3)))⁻¹) := by ring
    _ ≤ 2 * K * (1 / 9 ^ n) := by rw [h3]; gcongr
    _ = 2 * K / 9 ^ n := by ring

/-- `1_E S ≤ T 1_E + S² / T`. -/
theorem indicator_mul_le_of_pos {S T : ℝ} (hS : 0 ≤ S) (hT : 0 < T) {e : ℝ} (he0 : 0 ≤ e)
    (he1 : e ≤ 1) : e * S ≤ T * e + S ^ 2 / T := by
  rcases le_total S T with h | h
  · have : e * S ≤ e * T := mul_le_mul_of_nonneg_left h he0
    have : 0 ≤ S ^ 2 / T := by positivity
    linarith
  · have h1 : e * S ≤ S := by nlinarith
    have h2 : S ≤ S ^ 2 / T := by
      rw [le_div_iff₀ hT]
      nlinarith
    have : 0 ≤ T * e := by positivity
    linarith

/-- **The contribution of the bad event to a term of `D_n`.** -/
theorem exists_integral_omegaBad_le [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (p' q : Fin d → ℝ),
      ∫ ω, (omegaBad p d n).indicator
          (fun ω => cubeNu ω ⟨n, 0⟩ p' +
            (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
              -cubeMu ω ⟨n, 0⟩ q else 0) + |∑ i, q i * p' i|) ω ∂(latticeBondLaw d p) ≤
        C * (1 + (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| + ∑ i, q i ^ 2) / 3 ^ n := by
  have hd0 : 0 < d := by omega
  obtain ⟨CB, hCB, hB⟩ := exists_measure_omegaBad_le hd hpc
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  set m := 4 * (d - 1) with hm
  set Kμ : ℝ := d * d * coarseGradConstant d ^ 2 with hKμ
  have hKμ0 : 0 ≤ Kμ := by positivity
  set Mθ : ℝ := 2 * (m.factorial : ℝ) * θ ^ m with hMθ
  have hMθ0 : 0 ≤ Mθ := by positivity
  refine ⟨3 ^ d * CB + CB + Kμ * (CB + Mθ), by positivity, fun n p' q => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set V : TriadicCube d := ⟨n, 0⟩ with hV
  set E := omegaBad p d n with hE
  have hEm : MeasurableSet E := measurableSet_omegaBad p d n
  set T : ℝ := (3 : ℝ) ^ n with hT
  have hT0 : 0 < T := by positivity
  have hvol := V.latticeVolume_pos
  set c : ℝ := 3 ^ d / 4 * (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| with hc
  have hc0 : 0 ≤ c := by positivity
  set Q : ℝ := (∑ i, q i ^ 2) * Kμ / V.latticeVolume with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set S : Configuration d → ℝ := fun ω => ∑ z ∈ V.toIntegerCube.vertices,
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ m with hSdef
  obtain ⟨hSint, hSle⟩ := hmom m V.toIntegerCube.vertices
  set F : Configuration d → ℝ := fun ω => E.indicator (fun _ => c) ω +
    Q * (T * V.latticeVolume * E.indicator (fun _ => (1 : ℝ)) ω + S ω / T) with hFdef
  have hFint : Integrable F μ :=
    ((integrable_const c).indicator hEm).add ((((integrable_const (1 : ℝ)).indicator
      hEm).const_mul _).add (hSint.div_const _) |>.const_mul Q)
  set Y : Configuration d → ℝ := fun ω => cubeNu ω V p' +
    (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) +
      |∑ i, q i * p' i| with hYdef
  have hYint : Integrable Y μ := ((integrable_cubeNu p _ p').add
    (integrable_neg_cubeMu_indicator hd hpc _ q)).add (integrable_const _)
  have hle : ∀ ω, E.indicator Y ω ≤ F ω := by
    intro ω
    have hS0 : 0 ≤ S ω := Finset.sum_nonneg fun z _ =>
      pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _
    by_cases hω : ω ∈ E
    · simp only [hFdef, hYdef, Set.indicator_of_mem hω]
      have hν := cubeNu_le (ω := ω) (U := V) p'
      have hμb : (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) ≤
          Q * (T * V.latticeVolume + S ω / T) := by
        split_ifs with h
        · refine (neg_cubeMu_le_cubeMuBound_mul hd0 h.1 h.2 q).trans ?_
          unfold cubeMuBound
          have hpt : ∀ z ∈ V.toIntegerCube.vertices,
              TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) ≤
                T + TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ m / T := by
            intro z _
            have h1 := indicator_mul_le_of_pos (pow_nonneg
              (TriadicCube.stoppingSize_nonneg (TriadicCube.goodCubes ω) z) (2 * (d - 1))) hT0
              zero_le_one le_rfl
            rw [← pow_mul, show 2 * (d - 1) * 2 = m by rw [hm]; ring] at h1
            linarith
          have hsum := Finset.sum_le_sum hpt
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            V.card_toIntegerCube_vertices, ← Finset.sum_div] at hsum
          have e : Kμ * (∑ z ∈ V.toIntegerCube.vertices,
              TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))) /
                V.latticeVolume * ∑ i, q i ^ 2 =
              (∑ i, q i ^ 2) * Kμ / V.latticeVolume *
                (∑ z ∈ V.toIntegerCube.vertices,
                  TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))) := by
            ring
          rw [← hKμ, e]
          refine mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq ?_)) hQ0
          rw [hSdef]
          ring
        · positivity
      have : Q * (T * V.latticeVolume + S ω / T) =
          Q * (T * V.latticeVolume * 1 + S ω / T) := by ring
      linarith
    · simp only [hFdef, Set.indicator_of_notMem hω]
      positivity
  have hmono := integral_mono (hYint.indicator hEm) hFint hle
  have hFval : ∫ ω, F ω ∂μ = c * (μ E).toReal +
      Q * (T * V.latticeVolume * (μ E).toReal + (∫ ω, S ω ∂μ) / T) := by
    have hI1 : Integrable (fun ω => T * V.latticeVolume * E.indicator (fun _ => (1 : ℝ)) ω) μ :=
      ((integrable_const (1 : ℝ)).indicator hEm).const_mul _
    have hI2 : Integrable (fun ω => S ω / T) μ := hSint.div_const _
    have e1 : ∫ ω, F ω ∂μ = ∫ ω, E.indicator (fun _ => c) ω ∂μ +
        ∫ ω, Q * (T * V.latticeVolume * E.indicator (fun _ => (1 : ℝ)) ω + S ω / T) ∂μ := by
      rw [hFdef]
      exact integral_add ((integrable_const c).indicator hEm) ((hI1.add hI2).const_mul Q)
    have e2 : ∫ ω, (T * V.latticeVolume * E.indicator (fun _ => (1 : ℝ)) ω + S ω / T) ∂μ =
        ∫ ω, T * V.latticeVolume * E.indicator (fun _ => (1 : ℝ)) ω ∂μ + ∫ ω, S ω / T ∂μ :=
      integral_add hI1 hI2
    rw [e1, integral_const_mul, e2, integral_const_mul, integral_div,
      integral_indicator_const _ hEm, integral_indicator_const _ hEm]
    simp only [smul_eq_mul, mul_one]
    rw [mul_comm c]
    rfl
  rw [hFval] at hmono
  refine hmono.trans ?_
  have hPE := hB n
  have hPE0 : 0 ≤ (μ E).toReal := ENNReal.toReal_nonneg
  have h9 : (9 : ℝ) ^ n = T * T := by rw [hT, ← mul_pow]; norm_num
  have hSc : ∫ ω, S ω ∂μ ≤ Mθ * V.latticeVolume := by
    rw [V.card_toIntegerCube_vertices] at hSle
    exact hSle
  have hpq0 : 0 ≤ |∑ i, q i * p' i| := abs_nonneg _
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hp0 : 0 ≤ (∑ i, |p' i|) ^ 2 := sq_nonneg _
  -- the three contributions
  have hA : c * (μ E).toReal ≤ (3 ^ d * CB + CB) * (1 + (∑ i, |p' i|) ^ 2 +
      |∑ i, q i * p' i| + ∑ i, q i ^ 2) / T := by
    have h1 : (μ E).toReal ≤ CB / T := by
      refine hPE.trans ?_
      rw [h9, div_le_div_iff₀ (by positivity) hT0]
      nlinarith [mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) :
        (1 : ℝ) ≤ T) hCB]
    have h2 : c ≤ (3 ^ d + 1) * (1 + (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| + ∑ i, q i ^ 2) := by
      rw [hc]
      have : (0 : ℝ) ≤ 3 ^ d := by positivity
      nlinarith
    calc c * (μ E).toReal ≤ ((3 ^ d + 1) * (1 + (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| +
          ∑ i, q i ^ 2)) * (CB / T) := mul_le_mul h2 h1 hPE0 (by positivity)
      _ = _ := by ring
  have hBq : Q * (T * V.latticeVolume * (μ E).toReal + (∫ ω, S ω ∂μ) / T) ≤
      Kμ * (CB + Mθ) * (∑ i, q i ^ 2) / T := by
    have h1 : T * V.latticeVolume * (μ E).toReal ≤ V.latticeVolume * CB / T := by
      have := mul_le_mul_of_nonneg_left hPE (by positivity : 0 ≤ T * V.latticeVolume)
      calc T * V.latticeVolume * (μ E).toReal ≤ T * V.latticeVolume * (CB / 9 ^ n) := this
        _ = V.latticeVolume * CB / T := by rw [h9]; field_simp
    have h2 : (∫ ω, S ω ∂μ) / T ≤ Mθ * V.latticeVolume / T :=
      div_le_div_of_nonneg_right hSc hT0.le
    calc Q * (T * V.latticeVolume * (μ E).toReal + (∫ ω, S ω ∂μ) / T)
        ≤ Q * (V.latticeVolume * CB / T + Mθ * V.latticeVolume / T) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hQ0
      _ = Kμ * (CB + Mθ) * (∑ i, q i ^ 2) / T := by
          rw [hQ]
          field_simp
  have hC : Kμ * (CB + Mθ) * (∑ i, q i ^ 2) / T ≤ Kμ * (CB + Mθ) *
      (1 + (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| + ∑ i, q i ^ 2) / T := by
    have : 0 ≤ Kμ * (CB + Mθ) := by positivity
    gcongr
    linarith
  have e : (3 ^ d * CB + CB + Kμ * (CB + Mθ)) *
      (1 + (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| + ∑ i, q i ^ 2) / 3 ^ n =
      (3 ^ d * CB + CB) * (1 + (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| + ∑ i, q i ^ 2) / T +
        Kμ * (CB + Mθ) * (1 + (∑ i, |p' i|) ^ 2 + |∑ i, q i * p' i| + ∑ i, q i ^ 2) / T := by
    rw [hT]
    ring
  rw [e]
  linarith

end Rigidity.Percolation
