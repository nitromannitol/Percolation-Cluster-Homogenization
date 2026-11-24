import PercolationClusterHomogenization.Proofs.Cluster.GeneralBoundN
import PercolationClusterHomogenization.Proofs.Cluster.OsTailCalculus

/-!
# The random error of Proposition 5.2 of Armstrong and Dario, in every dimension

For a triadic cube `V`, with `μ` and `ν` set to `0` off the event that the partition exists and
resolves `V` (the convention `u ≡ 0` of the source), let
`f_μ(q) = μ(V, q) + (1/2) q · ā⁻¹ q` (`cubeMuErr`) and `f_ν(q) = ν(V, ā⁻¹ q) - (1/2) q · ā⁻¹ q`
(`cubeNuErr`). Both are quadratic forms, so `|f_μ(q)| ≤ X(V) |q|²` and `|f_ν(q)| ≤ X(V) |q|²`
(`abs_cubeMuErr_le`, `abs_cubeNuErr_le`) for the measurable random variable `X(V)`
(`cubeSubaddErr`), the sum of the absolute values of the entries of their matrices. On the good
event of Proposition 5.2, `X(V) ≤ 6 d² K λ^{scale V}` (`cubeSubaddErr_le_of_good`); on the partition
event, `X(V) ≤ c (1 + M^{2(d-1)})` with `M` the largest partition size on `V`
(`cubeSubaddErr_le_sizeMax`), from the bound of `-μ` by the partition sizes and
`ν ≤ (3ᵈ/4) |ξ|₁²`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The error `μ(V, q) + (1/2) q · ā⁻¹ q`, with `μ = 0` off the event. -/
noncomputable def cubeMuErr (p : unitInterval) (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) : ℝ :=
  (if PartitionEvent ω ∧ PartitionResolved ω V then cubeMu ω V q else 0) +
    1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i

/-- The error `ν(V, ā⁻¹ q) - (1/2) q · ā⁻¹ q`, with `ν = 0` off the event. -/
noncomputable def cubeNuErr (p : unitInterval) (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) : ℝ :=
  (if PartitionEvent ω ∧ PartitionResolved ω V then cubeNu ω V ((cubeAhom p)⁻¹ *ᵥ q) else 0) -
    1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i

/-- **The random error of Proposition 5.2 on `V`.** -/
noncomputable def cubeSubaddErr (p : unitInterval) (V : TriadicCube d) (ω : Configuration d) :
    ℝ :=
  ∑ i, ∑ j, |slopeMatrix (cubeMuErr p ω V) i j| + ∑ i, ∑ j, |slopeMatrix (cubeNuErr p ω V) i j|

theorem cubeSubaddErr_nonneg (p : unitInterval) (V : TriadicCube d) (ω : Configuration d) :
    0 ≤ cubeSubaddErr p V ω := by
  unfold cubeSubaddErr
  positivity

theorem isSlopeQuadratic_cubeMuErr (hd : 0 < d) (p : unitInterval) (ω : Configuration d)
    (V : TriadicCube d) : IsSlopeQuadratic (cubeMuErr p ω V) := by
  have hdot := (isSlopeQuadratic_dotProduct_mulVec (cubeAhom (d := d) p)⁻¹).const_mul (1 / 2)
  by_cases h : PartitionEvent ω ∧ PartitionResolved ω V
  · have e : cubeMuErr p ω V = fun q => cubeMu ω V q +
        1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [cubeMuErr, if_pos h]
    rw [e]
    exact (isSlopeQuadratic_cubeMu hd h.1 h.2).add hdot
  · have e : cubeMuErr p ω V = fun q => (fun _ => (0 : ℝ)) q +
        1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [cubeMuErr, if_neg h]
    rw [e]
    exact isSlopeQuadratic_zero.add hdot

theorem isSlopeQuadratic_cubeNuErr (p : unitInterval) (ω : Configuration d)
    (V : TriadicCube d) : IsSlopeQuadratic (cubeNuErr p ω V) := by
  have hdot := (isSlopeQuadratic_dotProduct_mulVec (cubeAhom (d := d) p)⁻¹).const_mul (1 / 2)
  by_cases h : PartitionEvent ω ∧ PartitionResolved ω V
  · have e : cubeNuErr p ω V = fun q => cubeNu ω V ((cubeAhom p)⁻¹ *ᵥ q) -
        1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [cubeNuErr, if_pos h]
    rw [e]
    exact ((isSlopeQuadratic_cubeNu ω V).comp_mulVec _).sub hdot
  · have e : cubeNuErr p ω V = fun q => (fun _ => (0 : ℝ)) q -
        1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [cubeNuErr, if_neg h]
    rw [e]
    exact isSlopeQuadratic_zero.sub hdot

theorem abs_cubeMuErr_le (hd : 0 < d) (p : unitInterval) (ω : Configuration d)
    (V : TriadicCube d) (q : Fin d → ℝ) :
    |cubeMuErr p ω V q| ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 := by
  refine ((isSlopeQuadratic_cubeMuErr hd p ω V).abs_le q).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => sq_nonneg (q i)))
  unfold cubeSubaddErr
  have : 0 ≤ ∑ i, ∑ j, |slopeMatrix (cubeNuErr p ω V) i j| := by positivity
  linarith

theorem abs_cubeNuErr_le (p : unitInterval) (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) : |cubeNuErr p ω V q| ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 := by
  refine ((isSlopeQuadratic_cubeNuErr p ω V).abs_le q).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => sq_nonneg (q i)))
  unfold cubeSubaddErr
  have : 0 ≤ ∑ i, ∑ j, |slopeMatrix (cubeMuErr p ω V) i j| := by positivity
  linarith

theorem measurable_cubeMuErr (hd : 0 < d) (p : unitInterval) (V : TriadicCube d)
    (q : Fin d → ℝ) : Measurable fun ω => cubeMuErr p ω V q := by
  have e : (fun ω => cubeMuErr p ω V q) = fun ω =>
      -(if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) +
        1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
    funext ω
    simp only [cubeMuErr]
    split_ifs <;> ring
  rw [e]
  exact (measurable_neg_cubeMu_indicator_real hd V q).neg.add measurable_const

theorem measurable_cubeNuErr (p : unitInterval) (V : TriadicCube d) (q : Fin d → ℝ) :
    Measurable fun ω => cubeNuErr p ω V q :=
  (Measurable.ite (measurableSet_partitionEvent_resolved V) (measurable_cubeNu V _)
    measurable_const).sub measurable_const

theorem measurable_cubeSubaddErr (hd : 0 < d) (p : unitInterval) (V : TriadicCube d) :
    Measurable (cubeSubaddErr p V) := by
  unfold cubeSubaddErr slopeMatrix slopePolar
  refine (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_).add
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  · exact ((((measurable_cubeMuErr hd p V _).sub (measurable_cubeMuErr hd p V _)).sub
      (measurable_cubeMuErr hd p V _)).div_const _).abs
  · exact ((((measurable_cubeNuErr p V _).sub (measurable_cubeNuErr p V _)).sub
      (measurable_cubeNuErr p V _)).div_const _).abs

/-- The test slopes `eᵢ` and `eᵢ + eⱼ` have `ℓ¹` norm at most `2`. -/
theorem sum_abs_single_add_single_le (i j : Fin d) :
    ∑ k, |(Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) k| ≤ 2 := by
  have hi : ∑ k, |(Pi.single i 1 : Fin d → ℝ) k| = 1 := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hj : ∑ k, |(Pi.single j 1 : Fin d → ℝ) k| = 1 := by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  calc ∑ k, |(Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) k|
      ≤ ∑ k, (|(Pi.single i 1 : Fin d → ℝ) k| + |(Pi.single j 1 : Fin d → ℝ) k|) :=
        Finset.sum_le_sum fun k _ => abs_add_le _ _
    _ = 2 := by rw [Finset.sum_add_distrib, hi, hj]; norm_num

theorem sum_abs_single_le (i : Fin d) : ∑ k, |(Pi.single i 1 : Fin d → ℝ) k| ≤ 2 := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- The entries of the matrix of a quadratic function bounded by `B` at the test slopes. -/
theorem sum_abs_slopeMatrix_le {g : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hg : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 → |g v| ≤ B) :
    ∑ i, ∑ j, |slopeMatrix g i j| ≤ d * d * (3 / 2 * B) := by
  have h : ∀ i j, |slopeMatrix g i j| ≤ 3 / 2 * B := fun i j => by
    unfold slopeMatrix slopePolar
    have h1 := hg _ (sum_abs_single_add_single_le i j)
    have h2 := hg _ (sum_abs_single_le i)
    have h3 := hg _ (sum_abs_single_le j)
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num)]
    calc |g (Pi.single i 1 + Pi.single j 1) - g (Pi.single i 1) - g (Pi.single j 1)|
        ≤ |g (Pi.single i 1 + Pi.single j 1)| + |g (Pi.single i 1)| + |g (Pi.single j 1)| :=
          (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ B + B + B := add_le_add (add_le_add h1 h2) h3
      _ = 3 / 2 * B * 2 := by ring
  calc ∑ i, ∑ j, |slopeMatrix g i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, 3 / 2 * B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = d * d * (3 / 2 * B) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The error on the good event** of Proposition 5.2: `X(V) ≤ 12 d² K λ^{scale V}`. -/
theorem cubeSubaddErr_le_of_good {p : unitInterval} {V : TriadicCube d} {K lam : ℝ}
    (h : CubeSubaddGood p ω V K lam) (hK : 0 ≤ K) (hlam : 0 ≤ lam) :
    cubeSubaddErr p V ω ≤ 12 * d * d * (K * lam ^ V.scale) := by
  obtain ⟨hP, hres, hμ, hν⟩ := h
  have hc : PartitionEvent ω ∧ PartitionResolved ω V := ⟨hP, hres⟩
  have hsq : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 → ∑ k, v k ^ 2 ≤ 4 := fun v hv => by
    have h1 := sum_sq_le_sq_sum_abs_vec v
    have h2 : (∑ k, |v k|) ^ 2 ≤ 2 ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => abs_nonneg _) hv 2
    linarith
  have hKl : 0 ≤ K * lam ^ V.scale := by positivity
  have hμb : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 → |cubeMuErr p ω V v| ≤ 4 * (K * lam ^ V.scale) :=
    fun v hv => by
      rw [cubeMuErr, if_pos hc]
      have := hμ v
      have h4 := mul_le_mul_of_nonneg_right (hsq v hv) hKl
      nlinarith
  have hνb : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 → |cubeNuErr p ω V v| ≤ 4 * (K * lam ^ V.scale) :=
    fun v hv => by
      rw [cubeNuErr, if_pos hc]
      have := hν v
      have h4 := mul_le_mul_of_nonneg_right (hsq v hv) hKl
      nlinarith
  have h1 := sum_abs_slopeMatrix_le hμb
  have h2 := sum_abs_slopeMatrix_le hνb
  unfold cubeSubaddErr
  nlinarith

theorem TriadicCube.toIntegerCube_vertices_nonempty (V : TriadicCube d) :
    V.toIntegerCube.vertices.Nonempty := by
  refine ⟨V.toIntegerCube.corner, ?_⟩
  rw [IntegerCube.mem_vertices]
  intro i
  have : (0 : ℤ) < (V.toIntegerCube.size : ℤ) := by
    change (0 : ℤ) < ((3 ^ V.scale : ℕ) : ℤ)
    positivity
  constructor <;> omega

/-- The largest partition size on the vertices of `V`. -/
noncomputable def sizeMax (ω : Configuration d) (V : TriadicCube d) : ℝ :=
  V.toIntegerCube.vertices.sup' V.toIntegerCube_vertices_nonempty
    fun a => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a

theorem stoppingSize_le_sizeMax (ω : Configuration d) {V : TriadicCube d} {a : Vertex d}
    (ha : a ∈ V.toIntegerCube.vertices) :
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a ≤ sizeMax ω V :=
  Finset.le_sup' (fun a => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a) ha

theorem sizeMax_nonneg (ω : Configuration d) (V : TriadicCube d) : 0 ≤ sizeMax ω V := by
  obtain ⟨a, ha⟩ := V.toIntegerCube_vertices_nonempty
  exact (stoppingSize_nonneg _ _).trans (stoppingSize_le_sizeMax ω ha)

/-- The constant of the bound of the error by the largest partition size. -/
noncomputable def sizeErrConst (d : ℕ) (S : ℝ) : ℝ :=
  d * d * (3 / 2) * (4 * d * d * coarseGradConstant d ^ 2 + 4 * S + 3 ^ d * S ^ 2)

/-- **The error everywhere on the partition event**, by the largest partition size:
`X(V) ≤ c (1 + M^{2(d-1)})`. -/
theorem cubeSubaddErr_le_sizeMax (hd : 0 < d) {p : unitInterval} (hP : PartitionEvent ω)
    {S : ℝ} (hS0 : 0 ≤ S)
    (hSb : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|)
    (V : TriadicCube d) :
    cubeSubaddErr p V ω ≤ sizeErrConst d S * (1 + sizeMax ω V ^ (2 * (d - 1))) := by
  set M := sizeMax ω V with hM
  have hM0 : 0 ≤ M := sizeMax_nonneg ω V
  set K2 : ℝ := d * d * coarseGradConstant d ^ 2 with hK2
  have hK20 : 0 ≤ K2 := by positivity
  have hMk : 0 ≤ M ^ (2 * (d - 1)) := by positivity
  have hsq : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 → ∑ k, v k ^ 2 ≤ 4 := fun v hv => by
    have h1 := sum_sq_le_sq_sum_abs_vec v
    have h2 : (∑ k, |v k|) ^ 2 ≤ 2 ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => abs_nonneg _) hv 2
    linarith
  have hdot : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 →
      |1 / 2 * ∑ i, v i * ((cubeAhom (d := d) p)⁻¹ *ᵥ v) i| ≤ 2 * S := fun v hv => by
    have h1 := abs_sum_mul_le_sum_abs_mul v ((cubeAhom (d := d) p)⁻¹ *ᵥ v)
    have h2 := hSb v
    have h3 : (∑ i, |v i|) * ∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ v) i| ≤ 2 * (S * 2) :=
      mul_le_mul hv (h2.trans (mul_le_mul_of_nonneg_left hv hS0))
        (Finset.sum_nonneg fun i _ => abs_nonneg _) (by norm_num)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hMB : cubeMuBound ω V ≤ K2 * M ^ (2 * (d - 1)) := by
    unfold cubeMuBound
    have hvol := V.latticeVolume_pos
    have hsum : ∑ z ∈ V.toIntegerCube.vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) ≤
        V.latticeVolume * M ^ (2 * (d - 1)) := by
      calc ∑ z ∈ V.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))
          ≤ ∑ _z ∈ V.toIntegerCube.vertices, M ^ (2 * (d - 1)) :=
            Finset.sum_le_sum fun z hz =>
              pow_le_pow_left₀ (stoppingSize_nonneg _ _) (stoppingSize_le_sizeMax ω hz) _
        _ = V.latticeVolume * M ^ (2 * (d - 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul, V.card_toIntegerCube_vertices]
    rw [div_le_iff₀ hvol]
    calc (d : ℝ) * d * coarseGradConstant d ^ 2 * ∑ z ∈ V.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))
        ≤ d * d * coarseGradConstant d ^ 2 * (V.latticeVolume * M ^ (2 * (d - 1))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = K2 * M ^ (2 * (d - 1)) * V.latticeVolume := by rw [hK2]; ring
  have hμb : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 →
      |cubeMuErr p ω V v| ≤ 4 * K2 * M ^ (2 * (d - 1)) + 2 * S := fun v hv => by
    rw [cubeMuErr]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hdot v hv))
    split_ifs with hc
    · rw [abs_of_nonpos (cubeMu_nonpos hd hP hc.2 v)]
      have h1 := neg_cubeMu_le_cubeMuBound_mul hd hP hc.2 v
      have h2 := mul_le_mul hMB (hsq v hv) (Finset.sum_nonneg fun k _ => sq_nonneg (v k))
        (by positivity)
      linarith
    · rw [abs_zero]
      positivity
  have hνb : ∀ v : Fin d → ℝ, ∑ k, |v k| ≤ 2 →
      |cubeNuErr p ω V v| ≤ 3 ^ d * S ^ 2 + 2 * S := fun v hv => by
    rw [cubeNuErr, sub_eq_add_neg]
    refine (abs_add_le _ _).trans (add_le_add ?_ (by rw [abs_neg]; exact hdot v hv))
    split_ifs with hc
    · rw [abs_of_nonneg (cubeNu_nonneg _)]
      have h1 := cubeNu_le (ω := ω) (U := V) ((cubeAhom (d := d) p)⁻¹ *ᵥ v)
      have h2 : ∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ v) i| ≤ 2 * S := by
        have := (hSb v).trans (mul_le_mul_of_nonneg_left hv hS0)
        linarith
      have h3 : (∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ v) i|) ^ 2 ≤ (2 * S) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _) h2 2
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 3 ^ d / 4)
      nlinarith
    · rw [abs_zero]
      positivity
  have h1 := sum_abs_slopeMatrix_le hμb
  have h2 := sum_abs_slopeMatrix_le hνb
  unfold cubeSubaddErr
  rw [sizeErrConst]
  have hS2 : 0 ≤ 3 ^ d * S ^ 2 := by positivity
  have hdd : 0 ≤ (d : ℝ) * d * (3 / 2) := by positivity
  have k : 4 * K2 * M ^ (2 * (d - 1)) + 2 * S + (3 ^ d * S ^ 2 + 2 * S) ≤
      (4 * d * d * coarseGradConstant d ^ 2 + 4 * S + 3 ^ d * S ^ 2) *
        (1 + M ^ (2 * (d - 1))) := by
    rw [hK2]
    nlinarith
  have := mul_le_mul_of_nonneg_left k hdd
  nlinarith

/-- A power of the logarithm of the volume is absorbed by `3^{m s/2}`. -/
theorem exists_poly_le_three_rpow_general {θ₀ s : ℝ} (hθ₀ : 0 < θ₀) (hs : 0 < s) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ,
      1 + (4 * θ₀ * (1 + Real.log (((3 : ℝ) ^ m) ^ d))) ^ k ≤
        C * (3 : ℝ) ^ ((m : ℝ) * (s / 2)) := by
  set y : ℝ := 2 * d / s with hy
  have hy0 : 0 ≤ y := by positivity
  set A : ℝ := 4 * θ₀ * (1 + y) with hA
  have hA0 : 0 ≤ A := by positivity
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  refine ⟨1 + A ^ k * (3 * k.factorial), le_add_of_nonneg_right (by positivity), fun m => ?_⟩
  set x : ℝ := Real.log 3 * ((m : ℝ) * (s / 2)) with hx
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := by positivity
  have h3 : (3 : ℝ) ^ ((m : ℝ) * (s / 2)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  have hlog : Real.log (((3 : ℝ) ^ m) ^ d) = y * x := by
    rw [Real.log_pow, Real.log_pow, hx, hy]
    field_simp
  have hlin : 1 + y * x ≤ (1 + y) * (1 + x) := by
    have e : (1 + y) * (1 + x) = 1 + x + y + y * x := by ring
    rw [e]
    linarith
  have hfac := Real.pow_div_factorial_le_exp (1 + x) (by linarith) k
  have he : Real.exp (1 + x) ≤ 3 * Real.exp x := by
    rw [Real.exp_add]
    have := Real.exp_one_lt_d9
    have h0 := Real.exp_pos x
    nlinarith only [this, h0]
  have h4 : (1 + x) ^ k ≤ 3 * k.factorial * Real.exp x := by
    rw [div_le_iff₀ hk] at hfac
    have := mul_le_mul_of_nonneg_right he hk.le
    linarith
  have hex : 1 ≤ Real.exp x := Real.one_le_exp hx0
  rw [h3, hlog]
  have hb : (4 * θ₀ * (1 + y * x)) ^ k ≤ A ^ k * (1 + x) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 4 * θ₀ by positivity)
    calc 4 * θ₀ * (1 + y * x) ≤ 4 * θ₀ * ((1 + y) * (1 + x)) := this
      _ = A * (1 + x) := by rw [hA]; ring
  have hAk : 0 ≤ A ^ k := by positivity
  have h5 : A ^ k * (1 + x) ^ k ≤ A ^ k * (3 * k.factorial * Real.exp x) :=
    mul_le_mul_of_nonneg_left h4 hAk
  have h6 : 0 ≤ A ^ k * (3 * k.factorial) := by positivity
  have h7 : A ^ k * (3 * k.factorial) * 1 ≤ A ^ k * (3 * k.factorial) * Real.exp x :=
    mul_le_mul_of_nonneg_left hex h6
  calc 1 + (4 * θ₀ * (1 + y * x)) ^ k ≤ 1 + A ^ k * (3 * k.factorial) * Real.exp x := by
        have e : A ^ k * (3 * k.factorial * Real.exp x) =
          A ^ k * (3 * k.factorial) * Real.exp x := by ring
        linarith
    _ ≤ (1 + A ^ k * (3 * k.factorial)) * Real.exp x := by linarith

open LatticeProb Rigidity.Proofs.Cluster in
/-- **The `O_{1/(2(d-1))}` bound of the error bound by the largest partition size.** -/
theorem osBound_sizeMax (hd : 2 ≤ d) {p : unitInterval} {θ₀ c₃ : ℝ} (hθ₀ : 0 < θ₀)
    (hc₃ : 0 < c₃)
    (hmom : ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ₀))
        (latticeBondLaw d p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ₀)
        ∂(latticeBondLaw d p)) ≤ 2)
    (V : TriadicCube d) :
    OsBound (latticeBondLaw d p) (1 / ((2 * (d - 1) : ℕ) : ℝ))
      (c₃ * 2 ^ (2 * (d - 1)) *
        (1 + (4 * θ₀ * (1 + Real.log V.latticeVolume)) ^ (2 * (d - 1))))
      (fun ω => c₃ * (1 + sizeMax ω V ^ (2 * (d - 1)))) := by
  set μ := latticeBondLaw d p with hμ
  set n : ℕ := 2 * (d - 1) with hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set T := V.toIntegerCube.vertices with hT
  have hS : ∀ a ∈ T, OsBound μ 1 (2 * θ₀)
      (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a) := fun a _ =>
    osBound_of_exp_moment hθ₀ (by simpa only [Real.rpow_one] using (hmom a).1)
      (by simpa only [Real.rpow_one] using (hmom a).2)
  have hM := osBound_finset_sup' one_pos (by positivity) T V.toIntegerCube_vertices_nonempty
    (fun a ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a) hS
  rw [V.card_toIntegerCube_vertices, div_one, Real.rpow_one] at hM
  set θM : ℝ := 2 * (1 + Real.log V.latticeVolume) * (2 * θ₀) with hθM
  have hM' : OsBound μ 1 θM (fun ω => sizeMax ω V) := hM
  have hlog : 0 ≤ Real.log V.latticeVolume :=
    Real.log_nonneg (one_le_pow₀ (one_le_pow₀ (by norm_num)))
  have hpow := osBound_pow_of_nonneg hM' (fun ω => sizeMax_nonneg ω V) hn0
  have h1 := osBound_const μ (1 / (n : ℝ)) 1 zero_le_one
  have hsum := OsBound.add (by positivity) h1 hpow
  have hmul := OsBound.const_mul hc₃ hsum
  have e2 : (2 : ℝ) ^ (1 / (1 / (n : ℝ))) = 2 ^ n := by
    rw [one_div_one_div, Real.rpow_natCast]
  rw [e2] at hmul
  refine OsBound.mono_ae (le_of_eq ?_) (Filter.Eventually.of_forall fun ω => le_rfl) hmul
  rw [hθM]
  ring

open LatticeProb Rigidity.Proofs.Cluster in
/-- **Armstrong and Dario, Proposition 5.2, displays (5.2) and (5.3)** (every `d ≥ 2`,
`p > p_c(d)`), given the bound of Lemma 5.9: there are `α, C > 0` such that for every triadic
cube `V` the random error `X(V)` of `μ(V, q) + (1/2) q · ā⁻¹ q` and
`ν(V, ā⁻¹ q) - (1/2) q · ā⁻¹ q` (with `μ = ν = 0` off the event that the partition exists and
resolves `V`) is measurable and `X(V) ≤ O_r(C 3^{-α scale V})` with `r = 1/(2d - 1)`, an exponent
that depends only on `d`, as `s(d)` of the source. -/
theorem exists_cubeSubaddErr_isOsBond_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube d,
      Measurable (cubeSubaddErr p V) ∧ (∀ ω, 0 ≤ cubeSubaddErr p V ω) ∧
      IsOsBond d p (cubeSubaddErr p V) (1 / (2 * (d : ℝ) - 1))
        (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
      ∀ (ω : Configuration d) (q : Fin d → ℝ),
        |cubeMuErr p ω V q| ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 ∧
        |cubeNuErr p ω V q| ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨K, lam, s, c, K', hK, hlam0, hlam1, hs0, -, hc, hK', -, hcube⟩ :=
    exists_cubeSubaddGood_tail_cube_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i, ∑ j, |((cubeAhom (d := d) p)⁻¹) i j| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hSb : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i| :=
    fun v => by rw [hSdef]; exact sum_abs_mulVec_le _ v
  obtain ⟨θ₀, hθ₀, hmom⟩ := exists_partition_size_moment hd hpc
  set c₃ : ℝ := sizeErrConst d S with hc₃
  have hc₃0 : 0 < c₃ := by
    have hcg : 0 < coarseGradConstant d := by
      unfold coarseGradConstant
      positivity
    rw [hc₃, sizeErrConst]
    positivity
  set n : ℕ := 2 * (d - 1) with hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨C'', hC''1, hC''⟩ := exists_poly_le_three_rpow_general (d := d) hθ₀ hs0 n
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set β : ℝ := -Real.log lam / Real.log 3 with hβ
  have hβ0 : 0 < β := div_pos (neg_pos.2 (Real.log_neg hlam0 hlam1)) hl3
  set α : ℝ := min β (s / 2) with hα
  have hα0 : 0 < α := lt_min hβ0 (by positivity)
  have hαβ : α ≤ β := min_le_left _ _
  have hαs : α ≤ s / 2 := min_le_right _ _
  set s₀ : ℝ := 1 / (n : ℝ) with hs₀
  have hs₀0 : 0 < s₀ := by positivity
  set r : ℝ := s₀ * 1 / (s₀ + 1) with hr
  have hr0 : 0 < r := by positivity
  have hrs : r ≤ s₀ := by
    rw [hr, div_le_iff₀ (by positivity)]
    nlinarith
  have hr_eq : r = 1 / (2 * (d : ℝ) - 1) := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hnd : (n : ℝ) = 2 * (d : ℝ) - 2 := by
      rw [hn, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast
      ring
    have hD : (2 * (d : ℝ) - 2) ≠ 0 := by linarith
    have hD' : (2 * (d : ℝ) - 1) ≠ 0 := by linarith
    rw [hr, hs₀, hnd]
    field_simp <;> ring
  set B₁ : ℝ := (2 : ℝ) ^ ((s₀ + 1) / (s₀ * 1)) with hB₁
  set B₂ : ℝ := (2 : ℝ) ^ (1 / r) with hB₂
  have hB₁0 : 0 < B₁ := by positivity
  have hB₂0 : 0 < B₂ := by positivity
  set C : ℝ := B₂ * (12 * d * d * K + B₁ * (2 * c₃ * 2 ^ n * C'' / c)) +
      c₃ * 2 ^ n * C'' * (4 * K' / c) + 1 with hC
  have hC0 : 0 < C := by
    have h1 : 0 ≤ B₂ * (12 * d * d * K + B₁ * (2 * c₃ * 2 ^ n * C'' / c)) := by positivity
    have h2 : 0 ≤ c₃ * 2 ^ n * C'' * (4 * K' / c) := by positivity
    linarith
  refine ⟨α, C * 2 ^ (1 / r) * Real.exp 2 ^ (1 / r), hα0, by positivity, fun V =>
    ⟨measurable_cubeSubaddErr hd0 p V, cubeSubaddErr_nonneg p V, ?_,
      fun ω q => ⟨abs_cubeMuErr_le hd0 p ω V q, abs_cubeNuErr_le p ω V q⟩⟩⟩
  rw [← hr_eq]
  set μ := latticeBondLaw d p with hμ
  set m := V.scale with hm
  set u : ℝ := (3 : ℝ) ^ ((m : ℝ) * (s / 2)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by norm_num) (by positivity)
  have hu0 : 0 < u := by linarith
  set v : ℝ := (3 : ℝ) ^ (-(m : ℝ) * α) with hv
  have hv0 : 0 < v := by positivity
  have hvu : 1 / u ≤ v := by
    rw [hv, hu, div_le_iff₀ (by positivity), ← Real.rpow_add (by norm_num)]
    apply Real.one_le_rpow (by norm_num)
    have : (m : ℝ) * α ≤ (m : ℝ) * (s / 2) :=
      mul_le_mul_of_nonneg_left hαs (Nat.cast_nonneg m)
    linarith
  have hlamv : lam ^ m ≤ v := by
    have e : lam ^ m = (3 : ℝ) ^ (-(m : ℝ) * β) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      conv_lhs => rw [← Real.exp_log hlam0]
      rw [← Real.exp_nat_mul, hβ]
      congr 1
      field_simp
    rw [e, hv]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (m : ℝ) * α ≤ (m : ℝ) * β := mul_le_mul_of_nonneg_left hαβ (Nat.cast_nonneg m)
    linarith
  have hX : ((3 : ℝ) ^ m) ^ s = u ^ 2 := by
    have e1 : ((3 : ℝ) ^ m) ^ s = (3 : ℝ) ^ ((m : ℝ) * s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e2 : u ^ 2 = (3 : ℝ) ^ ((m : ℝ) * s) := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e1, e2]
  set a : ℝ := c₃ * 2 ^ n * (1 + (4 * θ₀ * (1 + Real.log V.latticeVolume)) ^ n) with ha
  have hlogV : 0 ≤ Real.log V.latticeVolume :=
    Real.log_nonneg (one_le_pow₀ (one_le_pow₀ (by norm_num)))
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hau : a ≤ c₃ * 2 ^ n * C'' * u := by
    have hvol : V.latticeVolume = ((3 : ℝ) ^ m) ^ d := rfl
    have := hC'' m
    rw [← hu, ← hvol] at this
    have h0 : (0 : ℝ) ≤ c₃ * 2 ^ n := by positivity
    calc a ≤ c₃ * 2 ^ n * (C'' * u) := by rw [ha]; exact mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have hY := osBound_sizeMax (p := p) hd hθ₀ hc₃0 hmom V
  rw [← hn, ← hs₀, ← ha] at hY
  have hH := ae_partitionEvent hd hpc
  have hdomY : ∀ᵐ ω ∂μ, cubeSubaddErr p V ω ≤ c₃ * (1 + sizeMax ω V ^ n) := by
    filter_upwards [hH] with ω hω
    exact cubeSubaddErr_le_sizeMax hd0 hω hS0 hSb V
  have hfinal : OsBound μ r (C * v) (cubeSubaddErr p V) := by
    by_cases hA : 2 * K' ≤ Real.exp (c * u ^ 2 / 2)
    · set E := {ω : Configuration d | ¬ CubeSubaddGood p ω V K lam} with hE
      set θE : ℝ := 2 / (c * u ^ 2) with hθE
      have hθE0 : 0 < θE := by positivity
      have hEμ : μ E ≤ ENNReal.ofReal (Real.exp (-(1 / θE))) := by
        refine (hcube V).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [← hm, hX, hθE, one_div_div]
        calc 2 * K' * Real.exp (-c * u ^ 2) ≤
              Real.exp (c * u ^ 2 / 2) * Real.exp (-c * u ^ 2) :=
              mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
          _ = Real.exp (-(c * u ^ 2 / 2)) := by rw [← Real.exp_add]; ring_nf
      have hEind := osBound_indicator μ hθE0 hEμ
      have hprod := OsBound.mul hs₀0 one_pos ha0
        (fun ω => mul_nonneg hc₃0.le (by have := sizeMax_nonneg ω V; positivity))
        (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) hY hEind
      rw [← hr, ← hB₁] at hprod
      have hconst := osBound_const μ r (12 * d * d * (K * lam ^ m)) (by positivity)
      have hsum := OsBound.add hr0 hconst hprod
      rw [← hB₂] at hsum
      refine OsBound.mono_ae ?_ ?_ hsum
      · have h1 : 12 * d * d * (K * lam ^ m) ≤ 12 * d * d * K * v := by
          have := mul_le_mul_of_nonneg_left hlamv hK
          have h0 : (0 : ℝ) ≤ 12 * d * d := by positivity
          calc 12 * d * d * (K * lam ^ m) ≤ 12 * d * d * (K * v) :=
                mul_le_mul_of_nonneg_left this h0
            _ = _ := by ring
        have h2 : a * θE ≤ 2 * c₃ * 2 ^ n * C'' / c * v := by
          calc a * θE ≤ c₃ * 2 ^ n * C'' * u * θE := mul_le_mul_of_nonneg_right hau hθE0.le
            _ = 2 * c₃ * 2 ^ n * C'' / c * (1 / u) := by rw [hθE]; field_simp
            _ ≤ 2 * c₃ * 2 ^ n * C'' / c * v := mul_le_mul_of_nonneg_left hvu (by positivity)
        have h3 : 0 ≤ c₃ * 2 ^ n * C'' * (4 * K' / c) := by positivity
        calc B₂ * (12 * d * d * (K * lam ^ m) + B₁ * (a * θE))
            ≤ B₂ * (12 * d * d * K * v + B₁ * (2 * c₃ * 2 ^ n * C'' / c * v)) := by gcongr
          _ = B₂ * (12 * d * d * K + B₁ * (2 * c₃ * 2 ^ n * C'' / c)) * v := by ring
          _ ≤ C * v := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hv0.le
      · filter_upwards [hH] with ω hω
        by_cases hg : CubeSubaddGood p ω V K lam
        · have h1 := cubeSubaddErr_le_of_good hg hK hlam0.le
          have h2 : 0 ≤ c₃ * (1 + sizeMax ω V ^ n) * E.indicator (fun _ => (1 : ℝ)) ω := by
            have := sizeMax_nonneg ω V
            exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
          rw [← hm] at h1
          linarith
        · have hωE : ω ∈ E := hg
          rw [Set.indicator_of_mem hωE, mul_one]
          have h1 := cubeSubaddErr_le_sizeMax hd0 hω hS0 hSb V
          rw [← hc₃, ← hn] at h1
          have : 0 ≤ 12 * d * d * (K * lam ^ m) := by positivity
          linarith
    · push Not at hA
      have hK'0 : 0 < K' := by
        by_contra h0
        push Not at h0
        linarith [Real.exp_pos (c * u ^ 2 / 2)]
      have hu2 : u ^ 2 ≤ 4 * K' / c := by
        have h1 := Real.add_one_le_exp (c * u ^ 2 / 2)
        rw [le_div_iff₀ hc]
        nlinarith only [h1, hA, hK'0]
      have haC : a ≤ C * v := by
        have h1 : a ≤ c₃ * 2 ^ n * C'' * (4 * K' / c) * v := by
          calc a ≤ c₃ * 2 ^ n * C'' * u := hau
            _ = c₃ * 2 ^ n * C'' * u ^ 2 * (1 / u) := by field_simp
            _ ≤ c₃ * 2 ^ n * C'' * (4 * K' / c) * v := by
                apply mul_le_mul _ hvu (by positivity) (by positivity)
                exact mul_le_mul_of_nonneg_left hu2 (by positivity)
        have h2 : 0 ≤ B₂ * (12 * d * d * K + B₁ * (2 * c₃ * 2 ^ n * C'' / c)) := by positivity
        calc a ≤ c₃ * 2 ^ n * C'' * (4 * K' / c) * v := h1
          _ ≤ C * v := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hv0.le
      exact OsBound.mono_ae haC hdomY (hY.of_exponent_le hrs)
  have hIs := isOsBond_of_osBound hr0 (by positivity) (measurable_cubeSubaddErr hd0 p V) hfinal
  refine Rigidity.Proofs.S2.IsOsBond.mono_scale hr0 (by positivity) (le_of_eq ?_)
    (measurable_cubeSubaddErr hd0 p V) hIs
  rw [hv]
  ring

end Rigidity.Percolation
