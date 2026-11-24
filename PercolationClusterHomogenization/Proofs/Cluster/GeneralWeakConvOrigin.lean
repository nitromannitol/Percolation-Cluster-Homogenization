import PercolationClusterHomogenization.Proofs.Cluster.GeneralSwitchLocProb
import PercolationClusterHomogenization.Proofs.Cluster.PlanarWeakConvVariance
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFiniteVolumeMatrix

/-!
# Lemma 5.7 of Armstrong and Dario for the cube centred at the origin, in every dimension

For `d ≥ 2`, `p > p_c(d)` and `n ≥ 8d`, the variance of the spatial average
`|□_n|⁻¹ ⟨e_j, ∇[u(·, □_n, q)]_𝒫⟩_{□_n}` (`cubeMuGradAvg`) is at most `C |q|² (τ_n + 3^{-n/4})`
(`exists_variance_cubeMuGradAvg_origin_le`). The proof is the end of the proof of Lemma 5.7 of
Armstrong and Dario: let `g` be the solenoidal field of scale `n` in the direction `e_j`
(`cubeSolenoidalField n j l`, `l ≠ j`), `X_V = |V|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V` for the `3^d`
subcubes `V` of scale `n` of `□_{n+1}`, and `Y_V` their local versions, which are bounded,
measurable for the bonds inside `V` and hence independent. Since `g = e_j` on `□_n`, `X_{□_n}` is
the spatial average; display (5.30) bounds `E[(∑_V X_V)²]`, display (5.31) bounds
`E[(X_V - Y_V)²]`, and the variance step (`variance_le_of_pairwise_indep`) gives the bound.

Since the mean of the spatial average is `(ā_{□_n}⁻¹ q)_j` (display (5.23)), this is display (5.25)
for `□_n` (`exists_lintegral_cubeMuGradAvg_origin_le`). The two-dimensional version is
`Rigidity.Proofs.Cluster.exists_variance_planarMuGradAvg_origin_le`.
-/

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The spatial average `|V|⁻¹ ⟨e_j, ∇[u(·, V, q)]_𝒫⟩_V` of the coarsened gradient of the minimizer
of `μ(V, q)`. -/
noncomputable def cubeMuGradAvg (ω : Configuration d) (V : TriadicCube d) (q : Fin d → ℝ)
    (j : Fin d) : ℝ :=
  cubeCoarsePairing ω V (Pi.single j 1) (cubeMuMinimizer ω V q) / V.latticeVolume

/-- The spatial average as the pairing of the constant field `e_j`. -/
theorem cubeMuGradAvg_eq_latticeEdgePairing (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) (j : Fin d) :
    cubeMuGradAvg ω V q j = latticeEdgePairing V.toIntegerCube.vertices
      (fun _ => (Pi.single j 1 : Fin d → ℝ))
      (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
        V.latticeVolume := by
  rw [cubeMuGradAvg, cubeCoarsePairing_eq_latticeEdgePairing]

/-- The pairing of a fixed field over a subset `D` of `U` with the coarsened gradient of the
minimizer of `μ(U, q)` is measurable. -/
theorem measurable_latticeEdgePairing_cubeMuMinimizer (hd : 0 < d) {U : TriadicCube d}
    {D : Finset (Vertex d)} (hDU : D ⊆ U.toIntegerCube.vertices) (g : Vertex d → Fin d → ℝ)
    (q : Fin d → ℝ) :
    Measurable fun ω : Configuration d => latticeEdgePairing D g
      (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) := by
  unfold latticeEdgePairing
  refine Finset.measurable_sum _ fun x hx => Finset.measurable_sum _ fun i _ => ?_
  by_cases hxi : x + unit i ∈ D
  · simp only [hxi, if_true]
    exact (measurable_cubeMuMinimizer_edge hd U q (hDU hx) (hDU hxi)).const_mul _
  · simp only [hxi, if_false]
    exact measurable_const

theorem measurable_cubeMuGradAvg (hd : 0 < d) (V : TriadicCube d) (q : Fin d → ℝ) (j : Fin d) :
    Measurable fun ω => cubeMuGradAvg ω V q j := by
  simp only [cubeMuGradAvg_eq_latticeEdgePairing]
  exact (measurable_latticeEdgePairing_cubeMuMinimizer hd subset_rfl _ q).div_const _

/-- **A deterministic bound for the spatial average.** -/
theorem abs_cubeMuGradAvg_le (hd : 0 < d) (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) (j : Fin d) :
    |cubeMuGradAvg ω V q j| ≤
      2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ V.scale) ^ (2 * d - 1) * 1 * ∑ i, |q i| := by
  rw [cubeMuGradAvg_eq_latticeEdgePairing]
  exact abs_cubeSubcubePairing_le hd V q (fun _ k => abs_single_apply_le_one j k) ω

/-- **The mean of the spatial average on `□_n`** (display (5.23)). -/
theorem integral_cubeMuGradAvg_origin [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (n : ℕ) (q : Fin d → ℝ) (j : Fin d) :
    ∫ ω, cubeMuGradAvg ω ⟨n, 0⟩ q j ∂(latticeBondLaw d p) = (cubeAhomInvFinite p n *ᵥ q) j := by
  have h := integral_cubeCoarsePairing_cubeMuMinimizer hd hpc n q (Pi.single j 1)
  have hfun : (fun ω => cubeMuGradAvg ω ⟨n, 0⟩ q j) = fun ω =>
      if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
        cubeCoarsePairing ω ⟨n, 0⟩ (Pi.single j 1) (cubeMuMinimizer ω ⟨n, 0⟩ q) /
          (⟨n, 0⟩ : TriadicCube d).latticeVolume else 0 := by
    funext ω
    rw [cubeMuGradAvg]
    split_ifs with hω
    · rfl
    · rw [cubeMuMinimizer, dif_neg fun h => hω ⟨h.2.1, h.2.2⟩, map_zero, zero_div]
  rw [hfun, h]
  simp [Pi.single_apply]

/-- A nonnegative integral bounded through the lower integral. -/
theorem integral_le_of_lintegral_le_ofReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfm : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal B) : ∫ ω, f ω ∂μ ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB h

theorem exists_ne_of_two_le (hd : 2 ≤ d) (j : Fin d) : ∃ l : Fin d, j ≠ l := by
  by_cases hj : j.val = 0
  · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
  · exact ⟨⟨0, by omega⟩, fun h => hj (by simp [Fin.ext_iff] at h; exact h)⟩

theorem sum_abs_sq_le (q : Fin d → ℝ) : (∑ i, |q i|) ^ 2 ≤ d * ∑ i, q i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun i => |q i|)
  simpa [sq_abs] using h

theorem card_subcubesAt_originCube_general (n : ℕ) :
    (((⟨n + 1, 0⟩ : TriadicCube d).subcubesAt n).card : ℝ) = 3 ^ d := by
  have h := card_subcubesAt_mul_general (⟨n + 1, 0⟩ : TriadicCube d) (n := n) (by simp)
  rw [TriadicCube.latticeVolume] at h
  change _ * _ = ((3 : ℝ) ^ (n + 1)) ^ d at h
  rw [pow_succ, mul_pow] at h
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  field_simp at h
  linarith

theorem originCube_mem_subcubesAt (n : ℕ) :
    (⟨n, 0⟩ : TriadicCube d) ∈ (⟨n + 1, 0⟩ : TriadicCube d).subcubesAt n := by
  have h0 : triadicCubeAt n (0 : Vertex d) = ⟨n, 0⟩ := by
    refine TriadicCube.eq_of_mem_of_scale_eq (scale_triadicCubeAt n 0) (mem_triadicCubeAt n 0) ?_
    intro i
    change |2 * ((0 : Vertex d) i - (3 : ℤ) ^ n * (0 : Vertex d) i)| < 3 ^ n
    simp only [Pi.zero_apply, mul_zero, sub_zero, abs_zero]
    positivity
  rw [← h0]
  refine TriadicCube.triadicCubeAt_mem_subcubesAt n ?_
  intro i
  change |2 * ((0 : Vertex d) i - (3 : ℤ) ^ (n + 1) * (0 : Vertex d) i)| < 3 ^ (n + 1)
  simp only [Pi.zero_apply, mul_zero, sub_zero, abs_zero]
  positivity

/-- **The variance of the spatial average on `□_n`** (proof of Lemma 5.7, conclusion, every
dimension `d ≥ 2`), for `n ≥ 8d`. -/
theorem exists_variance_cubeMuGradAvg_origin_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 * d ≤ n → ∀ (q : Fin d → ℝ) (j : Fin d),
      variance (fun ω => cubeMuGradAvg ω ⟨n, 0⟩ q j) (latticeBondLaw d p) ≤
        C * (∑ i, q i ^ 2) * (cubeTau (d := d) p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C₃, hC₃, h530⟩ := exists_lintegral_sum_subcube_cubeSolenoidal_sq_le hd hpc
  obtain ⟨C₄, hC₄, h531⟩ := exists_lintegral_sq_sub_cubeSwitchLoc_le hd hpc
  set N : ℝ := (3 : ℝ) ^ d with hN
  refine ⟨4 * C₃ + (4 * N + 2) * (N * (C₄ * 100 * d)), by positivity, fun n hn q j => ?_⟩
  obtain ⟨l, hjl⟩ := exists_ne_of_two_le hd j
  set μ := latticeBondLaw d p with hμ
  set g := cubeSolenoidalField n j l with hgdef
  have hg : ∀ x i, |g x i| ≤ 10 := abs_cubeSolenoidalField_le n j l
  set Q := ∑ i, |q i| with hQdef
  set P := ∑ i, q i ^ 2 with hPdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQP : Q ^ 2 ≤ d * P := sum_abs_sq_le q
  set τx := cubeTau (d := d) p n + (3 : ℝ) ^ (-(n : ℝ) / 4) with hτx
  have hτ0 := cubeTau_nonneg (d := d) p n
  have hx0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by positivity
  have hτx0 : 0 ≤ τx := add_nonneg hτ0 hx0
  have hxτ : (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ τx := by rw [hτx]; linarith
  set s := (⟨n + 1, 0⟩ : TriadicCube d).subcubesAt n with hs
  have hscale : ∀ V ∈ s, V.scale = n := fun V hV => TriadicCube.scale_of_mem_subcubesAt hV
  have hvolV : ∀ V ∈ s, V.latticeVolume = ((3 : ℝ) ^ n) ^ d := fun V hV => by
    rw [TriadicCube.latticeVolume, hscale V hV]
  have hi₀ : (⟨n, 0⟩ : TriadicCube d) ∈ s := originCube_mem_subcubesAt n
  set M := 2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ n) ^ (2 * d - 1) * 10 * Q with hMdef
  have hM0 : 0 ≤ M := by positivity
  set k := n / (8 * d) with hk
  -- the variables
  set X : TriadicCube d → Configuration d → ℝ := fun V => if V ∈ s then fun ω =>
    latticeEdgePairing V.toIntegerCube.vertices g
      (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) / ((3 : ℝ) ^ n) ^ d
    else fun _ => 0 with hXdef
  set Y : TriadicCube d → Configuration d → ℝ := fun V => if V ∈ s then
    cubeSwitchLoc k V g q M else fun _ => 0 with hYdef
  have hXm : ∀ V, Measurable (X V) := by
    intro V
    simp only [hXdef]
    split_ifs
    · exact (measurable_latticeEdgePairing_cubeMuMinimizer hd0 subset_rfl g q).div_const _
    · exact measurable_const
  have hYm : ∀ V, Measurable (Y V) := by
    intro V
    simp only [hYdef]
    split_ifs
    · exact measurable_cubeSwitchLoc _ _ _ _ _
    · exact measurable_const
  have hXb : ∀ V ω, |X V ω| ≤ M := by
    intro V ω
    simp only [hXdef]
    split_ifs with hV
    · have := abs_cubeSubcubePairing_le hd0 V q hg ω
      rwa [hvolV V hV, hscale V hV] at this
    · simpa using hM0
  have hYb : ∀ V ω, |Y V ω| ≤ M := by
    intro V ω
    simp only [hYdef]
    split_ifs with hV
    · exact abs_cubeSwitchLoc_le g q hM0 ω
    · simpa using hM0
  have hind : Set.Pairwise ↑s fun V W => IndepFun (Y V) (Y W) μ := by
    intro V hV W hW hVW
    have hV := Finset.mem_coe.1 hV
    have hW := Finset.mem_coe.1 hW
    have hV' : Y V = cubeSwitchLoc k V g q M := by simp only [hYdef, if_pos hV]
    have hW' : Y W = cubeSwitchLoc k W g q M := by simp only [hYdef, if_pos hW]
    rw [hV', hW']
    refine indepFun_cubeSwitchLoc p ?_ g g q M
    refine Set.disjoint_left.2 fun x hxV hxW => hVW ?_
    exact TriadicCube.eq_of_mem_of_scale_eq (by rw [hscale V hV, hscale W hW]) hxV hxW
  have hvar := variance_le_of_pairwise_indep (μ := μ) s hi₀ X Y hXm hYm hXb hYb hind
  -- the first term: display (5.30)
  have hsum : ∫ ω, (∑ V ∈ s, X V ω) ^ 2 ∂μ ≤ C₃ * P * τx := by
    have h := h530 n (by omega) q j l hjl
    have hfun : ∀ ω, (∑ V ∈ s, X V ω) = ∑ V ∈ s, latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
          ((3 : ℝ) ^ n) ^ d := fun ω =>
      Finset.sum_congr rfl fun V hV => by simp only [hXdef, if_pos hV]
    simp only [hfun]
    refine integral_le_of_lintegral_le_ofReal (fun ω => sq_nonneg _)
      ((Finset.measurable_sum s fun V _ =>
        (measurable_latticeEdgePairing_cubeMuMinimizer hd0 subset_rfl g q).div_const _).pow_const 2)
      (by positivity) h
  -- the second term: display (5.31)
  have hloc : ∀ V ∈ s, ∫ ω, (X V ω - Y V ω) ^ 2 ∂μ ≤ C₄ * 100 * d * P * τx := by
    intro V hV
    have h := h531 V (by rw [hscale V hV]; exact hn) q g 10 hg
    rw [hscale V hV] at h
    have hfun : ∀ ω, X V ω - Y V ω = latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) /
          V.latticeVolume - cubeSwitchLoc k V g q M ω :=
      fun ω => by simp only [hXdef, hYdef, if_pos hV, hvolV V hV]
    simp only [hfun]
    refine integral_le_of_lintegral_le_ofReal (fun ω => sq_nonneg _)
      (((measurable_latticeEdgePairing_cubeMuMinimizer hd0 subset_rfl g q).div_const _).sub
        (measurable_cubeSwitchLoc _ _ _ _ _) |>.pow_const 2) (by positivity) ?_
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : C₄ * 10 ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤
        C₄ * 10 ^ 2 * (d * P) * (3 : ℝ) ^ (-(n : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQP (by positivity)) hx0
    have h2 : C₄ * 10 ^ 2 * (d * P) * (3 : ℝ) ^ (-(n : ℝ) / 4) ≤ C₄ * 10 ^ 2 * (d * P) * τx :=
      mul_le_mul_of_nonneg_left hxτ (by positivity)
    nlinarith
  have hcard : (s.card : ℝ) = N := card_subcubesAt_originCube_general n
  have hsum2 : ∑ V ∈ s, ∫ ω, (X V ω - Y V ω) ^ 2 ∂μ ≤ N * (C₄ * 100 * d * P * τx) := by
    refine (Finset.sum_le_sum hloc).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hX0 : X ⟨n, 0⟩ = fun ω => cubeMuGradAvg ω ⟨n, 0⟩ q j := by
    funext ω
    simp only [hXdef, if_pos hi₀]
    rw [latticeEdgePairing_cubeSolenoidalField_origin n hjl, cubeMuGradAvg_eq_latticeEdgePairing]
    rfl
  rw [hX0] at hvar
  refine hvar.trans ?_
  rw [hcard]
  have hN0 : 0 ≤ N := by positivity
  have e1 : (4 * C₃ + (4 * N + 2) * (N * (C₄ * 100 * d))) * P * τx =
      4 * (C₃ * P * τx) + (4 * N + 2) * (N * (C₄ * 100 * d * P * τx)) := by ring
  rw [e1]
  have h38 := mul_le_mul_of_nonneg_left hsum2 (by positivity : (0 : ℝ) ≤ 4 * N + 2)
  linarith

/-- **Display (5.25) for `□_n`** (every dimension `d ≥ 2`), `n ≥ 8d`. -/
theorem exists_lintegral_cubeMuGradAvg_origin_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 * d ≤ n → ∀ q : Fin d → ℝ,
      ∫⁻ ω, ENNReal.ofReal (∑ j : Fin d,
          (cubeMuGradAvg ω ⟨n, 0⟩ q j - (cubeAhomInvFinite p n *ᵥ q) j) ^ 2)
          ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, q i ^ 2) * (cubeTau (d := d) p n + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, hC, hvar⟩ := exists_variance_cubeMuGradAvg_origin_le hd hpc
  refine ⟨d * C, by positivity, fun n hn q => ?_⟩
  set μ := latticeBondLaw d p with hμ
  have hm : ∀ j, Measurable (fun ω => cubeMuGradAvg ω ⟨n, 0⟩ q j) :=
    fun j => measurable_cubeMuGradAvg hd0 _ q j
  have hint : ∀ j, Integrable (fun ω =>
      (cubeMuGradAvg ω ⟨n, 0⟩ q j - (cubeAhomInvFinite p n *ᵥ q) j) ^ 2) μ := by
    intro j
    have hb := fun ω => abs_cubeMuGradAvg_le hd0 ω (⟨n, 0⟩ : TriadicCube d) q j
    set B := 2 * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ n) ^ (2 * d - 1) * 1 * ∑ i, |q i|
    refine Integrable.of_bound ((((hm j).sub measurable_const).pow_const 2).aestronglyMeasurable)
      ((B + |(cubeAhomInvFinite p n *ᵥ q) j|) ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_sub (cubeMuGradAvg ω ⟨n, 0⟩ q j) _).trans (add_le_add (hb ω) le_rfl)) 2
  have hvj : ∀ j, ∫ ω, (cubeMuGradAvg ω ⟨n, 0⟩ q j - (cubeAhomInvFinite p n *ᵥ q) j) ^ 2 ∂μ ≤
      C * (∑ i, q i ^ 2) * (cubeTau (d := d) p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) := by
    intro j
    have := hvar n hn q j
    rw [variance_eq_integral (hm j).aemeasurable, integral_cubeMuGradAvg_origin hd hpc] at this
    exact this
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun j _ => hint j)
    (ae_of_all _ fun ω => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_finsetSum _ fun j _ => hint j]
  calc ∑ j : Fin d, ∫ ω, (cubeMuGradAvg ω ⟨n, 0⟩ q j - (cubeAhomInvFinite p n *ᵥ q) j) ^ 2 ∂μ
      ≤ ∑ _j : Fin d, C * (∑ i, q i ^ 2) * (cubeTau (d := d) p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) :=
        Finset.sum_le_sum fun j _ => hvj j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Rigidity.Percolation
