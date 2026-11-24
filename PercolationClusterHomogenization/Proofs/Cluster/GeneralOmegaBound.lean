import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaExpect

/-!
# The pointwise bound of the proof of Lemma 5.9 on the event of small partition cubes

With `V = □_n`, `U = □_{n+1}`, `1 ≤ n`, `ℓ ≤ n` and the event `PartitionSizeLe ω U ℓ`:

`ν(V, p) - μ(V, q) - q · p ≤ c₀ + 3 (M_ν + D^μ_n(U, q)) / |V| + K_n · 4 |U| (F_v + F_u)`

(`cubeOmega_le_of_sizeLe`), where `K_n = 12 d / ((3ⁿ - 1)² |V|)`, the constant `c₀` collects the
deterministic bounds of the quadratic-response error, of the boundary error and of the coarsening
error (`omegaConst`), `M_ν` is the majorant of the energy `D^ν_n(U, p)` of the differences of the
maximizers of `ν` given by the subadditivity of `ν` (`nuDefectMajorant`, a measurable function), and
`F_u`, `F_v` are the flatness errors of the coarsened minimizer and maximizer for the slope `ξ`.
This is the pointwise chain of the proof of Lemma 5.9 of Armstrong and Dario in the form used for
the expectation.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The factor `K_n = 12 d / ((3ⁿ - 1)² |□_n|)` of the Caccioppoli term. -/
noncomputable def caccioppoliFactor (d n : ℕ) : ℝ :=
  12 * d / (((3 : ℝ) ^ n - 1) ^ 2 * (⟨n, 0⟩ : TriadicCube d).latticeVolume)

/-- The deterministic part `c₀` of the pointwise bound. -/
noncomputable def omegaConst (d n ℓ : ℕ) (p q : Fin d → ℝ) : ℝ :=
  |∑ i, q i * p i| / (3 : ℝ) ^ n +
    (∑ i, |q i|) * (∑ i, |p i|) * comparisonCap d ℓ * (1 / √((3 : ℝ) ^ n)) +
    caccioppoliFactor d n * 2 * (coarseningConst d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * d) *
      (3 ^ d * (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume * (∑ i, |p i|) ^ 2 +
        4 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
          ((⟨n + 1, 0⟩ : TriadicCube d).latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * d - 1))))

/-- The majorant of the energy `D^ν_n(□_{n+1}, p)` given by the subadditivity of `ν`. -/
noncomputable def nuDefectMajorant (ω : Configuration d) (n : ℕ) (p : Fin d → ℝ) : ℝ :=
  ∑ x ∈ (⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p -
    cubeNu ω ⟨n + 1, 0⟩ p * (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume +
    3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
      (√3 ^ n * (((⟨n + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices.filter
          (ExceptionalMajorant ω n)).card : ℝ) +
        (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume / √3 ^ n)

theorem caccioppoliFactor_nonneg (d n : ℕ) : 0 ≤ caccioppoliFactor d n := by
  unfold caccioppoliFactor
  have := (⟨n, 0⟩ : TriadicCube d).latticeVolume_pos
  positivity

/-- **The pointwise bound on the event of small partition cubes.** -/
theorem cubeOmega_le_of_sizeLe (hd : 0 < d) {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ ≤ n)
    (hS : PartitionSizeLe ω ⟨n + 1, 0⟩ ℓ) (p q ξ : Fin d → ℝ) :
    cubeNu ω ⟨n, 0⟩ p - cubeMu ω ⟨n, 0⟩ q - ∑ i, q i * p i ≤
      omegaConst d n ℓ p q +
        3 * (nuDefectMajorant ω n p + cubeMuDefect ω ⟨n + 1, 0⟩ n q) /
          (⟨n, 0⟩ : TriadicCube d).latticeVolume +
        caccioppoliFactor d n * (4 * (⟨n + 1, 0⟩ : TriadicCube d).latticeVolume *
          (cubeFlatnessError ⟨n + 1, 0⟩ (fun x => cubeExtend ω ⟨n + 1, 0⟩
              (cubeNuSolution ω ⟨n + 1, 0⟩ p) (partitionAnchor ω x)) ξ +
            cubeFlatnessError ⟨n + 1, 0⟩ (fun x => cubeExtend ω ⟨n + 1, 0⟩
              (cubeMuMinimizer ω ⟨n + 1, 0⟩ q) (partitionAnchor ω x)) ξ)) := by
  set V : TriadicCube d := ⟨n, 0⟩ with hVdef
  set U : TriadicCube d := ⟨n + 1, 0⟩ with hUdef
  have hP := hS.1
  have hVU : V.vertices ⊆ U.vertices := by
    intro x hx
    rw [mem_vertices_originCube_iff] at hx ⊢
    intro i
    have h1 := hx i
    have h2 : (3 : ℤ) ^ n ≤ 3 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    linarith
  have hU : PartitionResolved ω U := hS.resolved subset_rfl (by change ℓ ≤ n + 1; omega)
  have hV : PartitionResolved ω V := hS.resolved hVU hℓ
  have hSV : PartitionSizeLe ω V ℓ := ⟨hP, fun x hx => hS.2 x (hVU hx)⟩
  have hchain := cubeNu_sub_cubeMu_chain hd hP hn hU hV p q ξ
  -- the boundary error
  obtain ⟨hv, hvar⟩ := cubeNuMaximizer_spec (ω := ω) V p
  have hE := cubeBoundaryError_le_comparison hd hP hV p hv hvar
  have hY := cubeComparisonError_le_of_sizeLe hd hSV
  have hvolV := V.latticeVolume_pos
  have hQ0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP0 : 0 ≤ ∑ i, |p i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hEb : (∑ i, |q i|) * cubeBoundaryError ω V p (cubeNuMaximizer ω V p) / V.latticeVolume ≤
      (∑ i, |q i|) * (∑ i, |p i|) * comparisonCap d ℓ * (1 / √((3 : ℝ) ^ n)) := by
    have h1 : cubeBoundaryError ω V p (cubeNuMaximizer ω V p) / V.latticeVolume ≤
        (∑ i, |p i|) * cubeComparisonError ω V := by
      rw [div_le_iff₀ hvolV]
      refine hE.trans ?_
      unfold cubeComparisonError
      have hF0 := faceSizeSum_nonneg ω V
      have : (0 : ℝ) ≤ 1 / (3 : ℝ) ^ V.scale := by positivity
      have e : (∑ i, |p i|) * (faceSizeSum ω V + 2 * 3 ^ d *
          √(d * marginSizeSum ω V / V.latticeVolume) * V.latticeVolume) ≤
          (∑ i, |p i|) * (1 / (3 : ℝ) ^ V.scale + faceSizeSum ω V / V.latticeVolume +
            2 * 3 ^ d * √(d * marginSizeSum ω V / V.latticeVolume)) * V.latticeVolume := by
        have e2 : (∑ i, |p i|) * (1 / (3 : ℝ) ^ V.scale + faceSizeSum ω V / V.latticeVolume +
            2 * 3 ^ d * √(d * marginSizeSum ω V / V.latticeVolume)) * V.latticeVolume =
            (∑ i, |p i|) * (faceSizeSum ω V + 2 * 3 ^ d *
              √(d * marginSizeSum ω V / V.latticeVolume) * V.latticeVolume) +
            (∑ i, |p i|) * (V.latticeVolume / (3 : ℝ) ^ V.scale) := by
          field_simp
          ring
        rw [e2]
        have : 0 ≤ (∑ i, |p i|) * (V.latticeVolume / (3 : ℝ) ^ V.scale) := by positivity
        linarith
      exact e
    have h2 := mul_le_mul_of_nonneg_left hY hP0
    calc (∑ i, |q i|) * cubeBoundaryError ω V p (cubeNuMaximizer ω V p) / V.latticeVolume
        = (∑ i, |q i|) * (cubeBoundaryError ω V p (cubeNuMaximizer ω V p) / V.latticeVolume) := by
          ring
      _ ≤ (∑ i, |q i|) * ((∑ i, |p i|) * (comparisonCap d ℓ * (1 / √((3 : ℝ) ^ V.scale)))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hQ0
      _ = _ := by ring
  -- the energy of the differences of the maximizers of `ν`
  have hsn : (0 : ℝ) < √3 ^ n := by positivity
  have hDν : cubeNuDefect ω U n p ≤ nuDefectMajorant ω n p := by
    have h := cubeNuDefect_add_le hd hP (show n ≤ U.scale by change n ≤ n + 1; omega) p hsn
    have hc := subcubeExceptionalCount_le hP U n
    unfold nuDefectMajorant
    have hK : 0 ≤ 3 ^ d / 4 * (∑ i, |p i|) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hc hsn.le)
      (U.latticeVolume / √3 ^ n)) hK
    linarith
  -- the coarsening error
  set w := cubeNuMaximizer ω U p - cubeMuMinimizer ω U q with hw
  have hCE := cubeCoarseningError_le_of_sizeLe hd hP hU (fun x hx => hS.2 x hx) w
  have hBw : cubeForm ω U w w ≤
      3 ^ d * U.latticeVolume * (∑ i, |p i|) ^ 2 +
        4 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
          (U.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * d - 1)) := by
    have h1 := cubeForm_sub_le (ω := ω) (cubeNuMaximizer ω U p) (cubeMuMinimizer ω U q)
    obtain ⟨hvU, hvarU⟩ := cubeNuMaximizer_spec (ω := ω) U p
    have h2 := cubeForm_le_of_cubeNu_variation p hvU hvarU
    have h3 := cubeNu_le (ω := ω) (U := U) p
    have h4 := cubeForm_cubeMuMinimizer_le hd hP hU q
    have hS2 : partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ≤
        U.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * d - 1) := by
      unfold partitionSizeSum
      calc _ ≤ ∑ _z ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ ℓ) ^ (2 * d - 1) :=
            Finset.sum_le_sum fun z hz =>
              pow_le_pow_left₀ (TriadicCube.stoppingSize_nonneg _ _) (hS.stoppingSize_le hz) _
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, U.card_toIntegerCube_vertices]
    have hvolU := U.latticeVolume_pos
    have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h5 : cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q) ≤
        2 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
          (U.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * d - 1)) :=
      h4.trans (mul_le_mul_of_nonneg_left hS2 (by positivity))
    have h6 : cubeForm ω U (cubeNuMaximizer ω U p) (cubeNuMaximizer ω U p) ≤
        2 * U.latticeVolume * (3 ^ d / 4 * (∑ i, |p i|) ^ 2) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    rw [hw]
    nlinarith
  have hKn := caccioppoliFactor_nonneg d n
  have hCE2 : caccioppoliFactor d n * (2 * cubeCoarseningError ω U w) ≤
      caccioppoliFactor d n * 2 * (coarseningConst d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * d) *
        (3 ^ d * U.latticeVolume * (∑ i, |p i|) ^ 2 +
          4 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
            (U.latticeVolume * ((3 : ℝ) ^ ℓ) ^ (2 * d - 1)))) := by
    have hc0 : 0 ≤ coarseningConst d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * d) := by positivity
    have := hCE.trans (mul_le_mul_of_nonneg_left hBw hc0)
    nlinarith
  -- the flatness error of the maximizer is that of the solution
  have hFv : (fun x => cubeExtend ω U (cubeNuMaximizer ω U p) (partitionAnchor ω x)) =
      fun x => cubeExtend ω U (cubeNuSolution ω U p) (partitionAnchor ω x) := by
    rw [cubeNuSolution_eq hP hU]
  -- assembly
  have hsize : ((V.toIntegerCube.size : ℕ) : ℝ) = (3 : ℝ) ^ n := by
    change ((3 ^ n : ℕ) : ℝ) = _
    push_cast
    rfl
  rw [hsize, hFv] at hchain
  have hKdef : 12 * (d : ℝ) / (((3 : ℝ) ^ n - 1) ^ 2 * V.latticeVolume) = caccioppoliFactor d n :=
    rfl
  rw [hKdef] at hchain
  have hDν' : 3 * (cubeNuDefect ω U n p + cubeMuDefect ω U n q) / V.latticeVolume ≤
      3 * (nuDefectMajorant ω n p + cubeMuDefect ω U n q) / V.latticeVolume := by
    gcongr
  unfold omegaConst
  have e : caccioppoliFactor d n * (2 * cubeCoarseningError ω U w + 4 * U.latticeVolume *
      (cubeFlatnessError U (fun x => cubeExtend ω U (cubeNuSolution ω U p) (partitionAnchor ω x)) ξ +
        cubeFlatnessError U (fun x => cubeExtend ω U (cubeMuMinimizer ω U q)
          (partitionAnchor ω x)) ξ)) =
      caccioppoliFactor d n * (2 * cubeCoarseningError ω U w) +
        caccioppoliFactor d n * (4 * U.latticeVolume *
          (cubeFlatnessError U (fun x => cubeExtend ω U (cubeNuSolution ω U p)
              (partitionAnchor ω x)) ξ +
            cubeFlatnessError U (fun x => cubeExtend ω U (cubeMuMinimizer ω U q)
              (partitionAnchor ω x)) ξ)) := by ring
  rw [e] at hchain
  linarith

end Rigidity.Percolation
