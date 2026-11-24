import PercolationClusterHomogenization.Proofs.Cluster.GeneralRhoSubadditive
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFlatnessInputs
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHProb

/-!
# Lemma 5.11 of Armstrong and Dario in every dimension, given the bound of Lemma 5.9: the tail of
`ρ(□_m)`

Steps 1 and 3 of the proof of Lemma 5.11 (`l.SIupgrade`), assembled with Step 2
(`measureReal_sum_min_cubeRhoStat_gt_le_of_decay`). For the cube `U = □_{n+3+j}` and its subcubes
`V` of scale `n`, off three events

* some partition cube of a vertex of `U` has scale larger than `ℓ` (probability at most
  `|U| · 2 exp(-a 3^{ℓ+3})`, `measure_not_partitionSizeLe_le`), which gives the bound
  `ρ(V) ≤ C₁(ℓ)` of Step 1 (`cubeRho_le_of_sizeLe`) and the subadditivity (5.56) with
  deterministic errors (`cubeRho_le_avg_add_of_sizeLe`);
* some subcube is not in the good event of the stationary local versions (probability at most
  `3^{d(3+j)} · 2 C exp(-c 3ⁿ)`), so that `ρ(V) = ρ_stat(V) ∧ C₁` on every subcube;
* the Chernoff event of Step 2 with the threshold `t = 2 (e - 1) (C + 1) (1 + C₁) rⁿ` (probability
  at most `27ᵈ exp(-3^{dj} rⁿ)`),

`ρ(U) ≤ t + C(ℓ) 3^{-n/2}` (`exists_cubeRho_tail_of_decay`). The subcubes of scale `n` of
`□_{n+3+j}` are the cubes `⟨n, a + 27 b⟩`, `a` an index of `□_3` and `b` an index of `□_j`
(`sum_subcubesAt_eq_sum_sum_add_smul`). Armstrong and Dario take a constant `C₁` and remove the
event `ρ(V) > C₁` through the minimal scales; here `C₁` depends on `ℓ` and the event is that of
the partition sizes. This is the general-dimensional form of
`Rigidity.Proofs.Cluster.exists_planarRho_tail`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **The partition cubes of a cube are small with high probability**: the probability that some
vertex of `U` has a partition cube of scale larger than `ℓ` is at most `|U| · 2 exp(-a 3^{ℓ+3})`. -/
theorem measure_not_partitionSizeLe_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ (U : TriadicCube d) (ℓ : ℕ),
      latticeBondLaw d p {ω | ¬ PartitionSizeLe ω U ℓ} ≤
        ENNReal.ofReal (U.latticeVolume * (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)))) := by
  obtain ⟨a, ha, h⟩ :=
    Rigidity.Proofs.Cluster.GeneralDim.exists_measure_partitionCube_scale_ge_le hd hpc
  refine ⟨a, ha, fun U ℓ => ?_⟩
  set μ := latticeBondLaw d p with hμ
  have hsub : {ω | ¬ PartitionSizeLe ω U ℓ} ⊆ {ω | ¬ PartitionEvent ω} ∪
      ⋃ x ∈ U.toIntegerCube.vertices,
        {ω | PartitionEvent ω ∧ ℓ + 3 ≤ (partitionCube ω x).scale + 2} := by
    intro ω hω
    by_cases hP : PartitionEvent ω
    · have : ¬ ∀ x ∈ U.vertices, (partitionCube ω x).scale ≤ ℓ := fun h' => hω ⟨hP, h'⟩
      push Not at this
      obtain ⟨x, hx, hlt⟩ := this
      exact Or.inr (Set.mem_iUnion₂.2 ⟨x, (U.mem_toIntegerCube_vertices x).2 hx, hP, by omega⟩)
    · exact Or.inl hP
  have hnull : μ {ω | ¬ PartitionEvent ω} = 0 := ae_iff.1 (ae_partitionEvent hd hpc)
  calc μ {ω | ¬ PartitionSizeLe ω U ℓ}
      ≤ μ ({ω | ¬ PartitionEvent ω} ∪ ⋃ x ∈ U.toIntegerCube.vertices,
          {ω | PartitionEvent ω ∧ ℓ + 3 ≤ (partitionCube ω x).scale + 2}) := measure_mono hsub
    _ ≤ μ {ω | ¬ PartitionEvent ω} + μ (⋃ x ∈ U.toIntegerCube.vertices,
          {ω | PartitionEvent ω ∧ ℓ + 3 ≤ (partitionCube ω x).scale + 2}) := measure_union_le _ _
    _ = μ (⋃ x ∈ U.toIntegerCube.vertices,
          {ω | PartitionEvent ω ∧ ℓ + 3 ≤ (partitionCube ω x).scale + 2}) := by
        rw [hnull, zero_add]
    _ ≤ ∑ x ∈ U.toIntegerCube.vertices,
          μ {ω | PartitionEvent ω ∧ ℓ + 3 ≤ (partitionCube ω x).scale + 2} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ U.toIntegerCube.vertices,
          ENNReal.ofReal (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3))) :=
        Finset.sum_le_sum fun x _ => h (ℓ + 3) x
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), U.card_toIntegerCube_vertices]

/-- The lattice points of the cube of scale `3 + j` at the origin are the points `a + 27 b`, `a`
in the cube of scale `3` and `b` in the cube of scale `j`, each exactly once. -/
theorem sum_cube_three_add_eq (j : ℕ) (g : Vertex d → ℝ) :
    ∑ c ∈ (⟨3 + j, 0⟩ : TriadicCube d).toIntegerCube.vertices, g c =
      ∑ a ∈ (⟨3, 0⟩ : TriadicCube d).toIntegerCube.vertices,
        ∑ b ∈ (⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices, g (a + (27 : ℤ) • b) := by
  have h1 := sum_triadicCubeAt_eq (U := (⟨3 + j, 0⟩ : TriadicCube d)) (n := 3)
    (show 3 ≤ 3 + j by omega) (fun _ x => g x)
  rw [h1, sum_subcubesAt_eq_general (show 3 ≤ 3 + j by omega) 0
    (fun V => ∑ x ∈ V.toIntegerCube.vertices, g x), Nat.add_sub_cancel_left, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_nbij' (fun x => x - (27 : ℤ) • b) (fun a => a + (27 : ℤ) • b) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hx' := (Rigidity.Proofs.Multiscale.mem_cube_iff 3 b x).1 hx
    refine (Rigidity.Proofs.Multiscale.mem_cube_iff 3 0 _).2 fun i => ?_
    have := hx' i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, sub_zero]
    norm_num at this ⊢
    exact this
  · intro a ha
    have ha' := (Rigidity.Proofs.Multiscale.mem_cube_iff 3 0 a).1 ha
    refine (Rigidity.Proofs.Multiscale.mem_cube_iff 3 b _).2 fun i => ?_
    have := ha' i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      sub_zero] at this ⊢
    norm_num at this ⊢
    exact this
  · intro x _
    exact sub_add_cancel x _
  · intro a _
    exact add_sub_cancel_right a _
  · intro x _
    rw [sub_add_cancel]

/-- **The subcubes of scale `n` of `□_{n+3+j}`** are the cubes `⟨n, a + 27 b⟩`, `a` an index of
`□_3` and `b` an index of `□_j`, each exactly once. -/
theorem sum_subcubesAt_eq_sum_sum_add_smul (n j : ℕ) (f : TriadicCube d → ℝ) :
    ∑ V ∈ (⟨n + 3 + j, 0⟩ : TriadicCube d).subcubesAt n, f V =
      ∑ a ∈ (⟨3, 0⟩ : TriadicCube d).toIntegerCube.vertices,
        ∑ b ∈ (⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices, f ⟨n, a + (27 : ℤ) • b⟩ := by
  rw [sum_subcubesAt_eq_general (show n ≤ n + 3 + j by omega) 0 f,
    show n + 3 + j - n = 3 + j by omega]
  exact sum_cube_three_add_eq j fun c => f ⟨n, c⟩

/-- The bound `C₁(ℓ)` of `ρ` on the subcubes, on the event of small partition cubes, plus one. -/
noncomputable def cubeRhoCap (d : ℕ) (S : ℝ) (ℓ : ℕ) : ℝ :=
  3 ^ d / 4 * S ^ 2 * d + d * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) + 1

theorem cubeRhoCap_pos (d : ℕ) (S : ℝ) (ℓ : ℕ) : 0 < cubeRhoCap d S ℓ := by
  unfold cubeRhoCap
  positivity

/-- **Lemma 5.11 of Armstrong and Dario** (every dimension `d ≥ 2`, given the bound of Lemma 5.9,
in the form of a tail bound): for `ℓ ≤ n`, off an event of probability at most
`|□_{n+3+j}| 2 exp(-a 3^{ℓ+3}) + 3^{d(3+j)} 2 C₂ exp(-c 3ⁿ) + 27ᵈ exp(-3^{dj} rⁿ)`, the partition
cubes of the vertices of `□_{n+3+j}` have scale at most `ℓ` and
`ρ(□_{n+3+j}) ≤ 2 (e - 1) (C + 1) (1 + C₁(ℓ)) rⁿ + C(ℓ) 3^{-n/2}`. -/
theorem exists_cubeRho_tail_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ C r : ℝ, 0 ≤ C ∧ 1 / 3 ≤ r ∧ r < 1 ∧ ∃ a : ℝ, 0 < a ∧ ∃ C₂ : ℝ≥0∞, C₂ ≠ ∞ ∧ ∃ c : ℝ,
      0 < c ∧
      ∀ {S : ℝ},
      (∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) →
      ∀ n j ℓ : ℕ, ℓ ≤ n →
        latticeBondLaw d p {ω | ¬ (PartitionSizeLe ω ⟨n + 3 + j, 0⟩ ℓ ∧
            cubeRho p ω ⟨n + 3 + j, 0⟩ ≤
              2 * (Real.exp 1 - 1) * (C + 1) * (1 + cubeRhoCap d S ℓ) * r ^ n +
                rhoSubaddConst d S ℓ * (1 / √((3 : ℝ) ^ n)))} ≤
          ENNReal.ofReal (((3 : ℝ) ^ (n + 3 + j)) ^ d * (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)))) +
            ENNReal.ofReal (((3 : ℝ) ^ (3 + j)) ^ d) *
              (2 * C₂ * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) +
            ENNReal.ofReal ((27 : ℝ) ^ d * Real.exp (-(((3 : ℝ) ^ j) ^ d * r ^ n))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, r, hC, hr13, hr1, hstep⟩ :=
    measureReal_sum_min_cubeRhoStat_gt_le_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr13
  obtain ⟨a, ha, hreach⟩ := measure_not_partitionSizeLe_le hd hpc
  obtain ⟨C₂, hC₂, c, hc, hgood⟩ := exists_measure_not_cubeStatGood_le hd hpc
  refine ⟨C, r, hC, hr13, hr1, a, ha, C₂, hC₂, c, hc, fun {S} hSb n j ℓ hℓn => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set U : TriadicCube d := ⟨n + 3 + j, 0⟩ with hU
  have hnU : n ≤ U.scale := show n ≤ n + 3 + j by omega
  set A := (⟨3, 0⟩ : TriadicCube d).toIntegerCube.vertices with hA
  set B := (⟨j, 0⟩ : TriadicCube d).toIntegerCube.vertices with hB
  have hAc : (A.card : ℝ) = 27 ^ d := by
    rw [hA, TriadicCube.card_toIntegerCube_vertices]
    change ((3 : ℝ) ^ 3) ^ d = _
    norm_num
  have hBc : (B.card : ℝ) = ((3 : ℝ) ^ j) ^ d := by
    rw [hB, TriadicCube.card_toIntegerCube_vertices]
    rfl
  have hsubc : ((U.subcubesAt n).card : ℝ) = ((3 : ℝ) ^ (3 + j)) ^ d := by
    rw [hU, card_subcubesAt_eq_general (show n ≤ n + 3 + j by omega),
      Rigidity.Proofs.Multiscale.card_centers (show n ≤ n + 3 + j by omega),
      show n + 3 + j - n = 3 + j by omega]
    push_cast
    rfl
  set C₁ := cubeRhoCap d S ℓ with hC₁
  have hC₁0 : 0 < C₁ := cubeRhoCap_pos d S ℓ
  set t : ℝ := 2 * (Real.exp 1 - 1) * (C + 1) * (1 + C₁) * r ^ n with ht
  set E₁ := {ω : Configuration d | ¬ PartitionSizeLe ω U ℓ} with hE₁
  set E₂ := ⋃ V ∈ U.subcubesAt n, {ω : Configuration d | ¬ CubeStatGood ω V} with hE₂
  set E₃ := {ω : Configuration d | (A.card : ℝ) * ((B.card : ℝ) * t) <
    ∑ a ∈ A, ∑ b ∈ B, min (cubeRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁} with hE₃
  have hsub : {ω | ¬ (PartitionSizeLe ω U ℓ ∧ cubeRho p ω U ≤
      t + rhoSubaddConst d S ℓ * (1 / √((3 : ℝ) ^ n)))} ⊆ E₁ ∪ E₂ ∪ E₃ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    have hSL : PartitionSizeLe ω U ℓ := not_not.1 h1
    have hSG : ∀ V ∈ U.subcubesAt n, CubeStatGood ω V := fun V hV => by
      by_contra hV'
      exact h2 (Set.mem_iUnion₂.2 ⟨V, hV, hV'⟩)
    have hS3 : ∑ a ∈ A, ∑ b ∈ B, min (cubeRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁ ≤
        (A.card : ℝ) * ((B.card : ℝ) * t) := not_lt.1 h3
    apply hω
    refine ⟨hSL, ?_⟩
    have havg := cubeRho_le_avg_add_of_sizeLe hd hSL hℓn hnU hSb
    have hmin : ∀ V ∈ U.subcubesAt n, cubeRho p ω V = min (cubeRhoStat p V ω) C₁ := by
      intro V hV
      rw [cubeRhoStat_eq_of_good p (hSG V hV)]
      have hle := cubeRho_le_of_sizeLe hd hpc hSL (TriadicCube.subset_of_mem_subcubesAt hnU hV)
        (by rw [TriadicCube.scale_of_mem_subcubesAt hV]; exact hℓn) hSb
      refine (min_eq_left (hle.trans ?_)).symm
      rw [hC₁, cubeRhoCap]
      linarith
    have hsum : ∑ V ∈ U.subcubesAt n, cubeRho p ω V ≤ (A.card : ℝ) * ((B.card : ℝ) * t) := by
      rw [Finset.sum_congr rfl hmin, hU,
        sum_subcubesAt_eq_sum_sum_add_smul n j (fun V => min (cubeRhoStat p V ω) C₁)]
      exact hS3
    have hcard : ((U.subcubesAt n).card : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
      rw [hsubc, hAc, hBc, ← mul_pow, pow_add]
      norm_num
    have hcpos : (0 : ℝ) < (U.subcubesAt n).card := by
      rw [hcard, hAc, hBc]
      positivity
    have havg' : ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, cubeRho p ω V ≤ t := by
      rw [inv_mul_le_iff₀ hcpos, hcard]
      linarith
    linarith
  have hP₁ : μ E₁ ≤ ENNReal.ofReal (((3 : ℝ) ^ (n + 3 + j)) ^ d *
      (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)))) :=
    hreach U ℓ
  have hP₂ : μ E₂ ≤ ENNReal.ofReal (((3 : ℝ) ^ (3 + j)) ^ d) *
      (2 * C₂ * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ V ∈ U.subcubesAt n, μ {ω | ¬ CubeStatGood ω V}
        ≤ ∑ _V ∈ U.subcubesAt n, 2 * C₂ * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) :=
          Finset.sum_le_sum fun V hV => (hgood V).trans
            (by rw [TriadicCube.scale_of_mem_subcubesAt hV])
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, hsubc]
  have hP₃ : μ E₃ ≤ ENNReal.ofReal ((27 : ℝ) ^ d * Real.exp (-(((3 : ℝ) ^ j) ^ d * r ^ n))) := by
    have h := hstep n j hC₁0 t
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ E₃)]
    refine ENNReal.ofReal_le_ofReal (h.trans ?_)
    rw [hAc, hBc]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have he : 1 ≤ Real.exp 1 - 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have hrn : 0 < r ^ n := pow_pos hr0 n
    have hkey : C₁ * r ^ n ≤ t - (Real.exp 1 - 1) * (C * (1 + C₁) * r ^ n) := by
      rw [ht]
      have h1 : C₁ * r ^ n ≤ (1 + C₁) * r ^ n := by nlinarith
      have h2 : 1 ≤ (Real.exp 1 - 1) * (C + 2) := by nlinarith
      have h3 : (1 + C₁) * r ^ n ≤ (Real.exp 1 - 1) * (C + 2) * ((1 + C₁) * r ^ n) := by
        have : 0 ≤ (1 + C₁) * r ^ n := by positivity
        nlinarith
      nlinarith
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ hC₁0]
    have h9 : (0 : ℝ) ≤ ((3 : ℝ) ^ j) ^ d := by positivity
    have := mul_le_mul_of_nonneg_left hkey h9
    nlinarith
  calc μ {ω | ¬ (PartitionSizeLe ω U ℓ ∧ cubeRho p ω U ≤
        t + rhoSubaddConst d S ℓ * (1 / √((3 : ℝ) ^ n)))}
      ≤ μ (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub
    _ ≤ μ E₁ + μ E₂ + μ E₃ := (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hP₁ hP₂) hP₃

end Rigidity.Percolation
