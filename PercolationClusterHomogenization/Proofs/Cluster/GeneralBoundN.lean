import PercolationClusterHomogenization.Proofs.Cluster.GeneralSubaddTailMain
import PercolationClusterHomogenization.Percolation.TriadicExceptionalSupremum
import PercolationClusterHomogenization.Proofs.Density.ScaleInputsFaithful

/-!
# Proposition 5.13 of Armstrong and Dario in every dimension, given the bound of Lemma 5.9

The tails of Proposition 5.2 on the cubes `□_m` at the origin
(`exists_cubeSubaddGood_tail_of_decay`) extend to every triadic cube
(`exists_cubeSubaddGood_tail_cube_of_decay`): on the good event of the stationary local versions,
`μ(V, ·)` and `ν(V, ·)` are the values on `□_{scale V}` in the configuration translated by
`-center V` (`cubeSubaddGood_of_statGood`), and the bond law is translation invariant. For a
mesoscopic scale `n(m) ≤ m ≤ L n(m)`, the bad event at scale `m` (some subcube of scale `n(m)` of
`□_m`, or some translate `z + □_{n(m)}`, `z ∈ □_m`, fails the bounds) has probability at most
`C exp(-c (3^m)^{s/L})`, and the random scale `𝒩 = 3 sup {3^m : bad at m}` (Definition 5.12) is
`O_{s/L}(θ)` by the exceptional-scale moment bound (`exceptionalScale_exp_moment`): this is
Proposition 5.13 (`exists_cubeBoundN_of_decay`, with `n(m) = ⌈m/4⌉`), as in the two-dimensional
`Rigidity.Proofs.Cluster.planarBoundN_holds`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **Transport of Proposition 5.2 by a translation** on the good event of the stationary local
versions. -/
theorem cubeSubaddGood_of_statGood {p : unitInterval} {V : TriadicCube d} {K lam : ℝ}
    (hSG : CubeStatGood ω V)
    (hG : CubeSubaddGood p (configurationTranslation (-V.center) ω) V.atOrigin K lam) :
    CubeSubaddGood p ω V K lam := by
  set ω' := configurationTranslation (-V.center) ω with hω'
  have hω : configurationTranslation V.center ω' = ω := by
    rw [hω', configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have hz : ∀ i, V.atOrigin.side ∣ V.center i := V.atOrigin_side_dvd_center
  have hz' : ∀ i, (3 : ℤ) ^ V.atOrigin.scale ∣ V.center i := hz
  have hLG' : CubeLocalGood ω' V.atOrigin := hSG.2
  have hLG : CubeLocalGood (configurationTranslation V.center ω')
      (V.atOrigin.shift V.center) := by
    rw [hω, V.atOrigin_shift_center]
    exact hSG.1
  have hpart : ∀ x ∈ V.atOrigin.vertices,
      partitionCube (configurationTranslation V.center ω') (x + V.center) =
        (partitionCube ω' x).shift V.center := by
    intro x hx
    rw [partitionCube_eq_cappedCube hLG ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      partitionCube_eq_cappedCube hLG' hx]
    exact cappedCube_goodCubes_translation hz' ω' x
  obtain ⟨hP', hres', hμ, hν⟩ := hG
  have hres := (partitionResolved_shift_iff hz hpart).2 hres'
  have hμe : ∀ q, cubeMu (configurationTranslation V.center ω') (V.atOrigin.shift V.center) q =
      cubeMu ω' V.atOrigin q := fun q => cubeMu_shift_translation_of_partition hres' hz hpart q
  have hνe : ∀ ξ, cubeNu (configurationTranslation V.center ω') (V.atOrigin.shift V.center) ξ =
      cubeNu ω' V.atOrigin ξ := fun ξ => cubeNu_shift ω' hz ξ
  rw [hω, V.atOrigin_shift_center] at hres hμe hνe
  have hsc : V.atOrigin.scale = V.scale := rfl
  refine ⟨hSG.1.1, hres, fun q => ?_, fun q => ?_⟩
  · rw [hμe q, ← hsc]
    exact hμ q
  · rw [hνe, ← hsc]
    exact hν q

theorem measure_preimage_configurationTranslation_general (p : unitInterval) (z : Vertex d)
    (s : Set (Configuration d)) :
    latticeBondLaw d p (configurationTranslation z ⁻¹' s) = latticeBondLaw d p s :=
  (measurePreserving_configurationTranslation p z).measure_preimage_emb
    (configurationTranslationMeasurableEquiv z).measurableEmbedding s

/-- **Proposition 5.2 with stretched-exponential tails on every triadic cube** (given the bound
of Lemma 5.9). -/
theorem exists_cubeSubaddGood_tail_cube_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K lam s c K' : ℝ, 0 ≤ K ∧ 0 < lam ∧ lam < 1 ∧ 0 < s ∧ s ≤ 1 ∧ 0 < c ∧ 0 ≤ K' ∧
      (∀ (m : ℕ) (z : Vertex d), latticeBondLaw d p
        {ω | ¬ CubeSubaddGood p (configurationTranslation z ω) ⟨m, 0⟩ K lam} ≤
          ENNReal.ofReal (K' * Real.exp (-c * ((3 : ℝ) ^ m) ^ s))) ∧
      ∀ V : TriadicCube d, latticeBondLaw d p {ω | ¬ CubeSubaddGood p ω V K lam} ≤
        ENNReal.ofReal (2 * K' * Real.exp (-c * ((3 : ℝ) ^ V.scale) ^ s)) := by
  obtain ⟨K, lam, s, c, K', hK, hlam0, hlam1, hs0, hs1, hc, hK', htail⟩ :=
    exists_cubeSubaddGood_tail_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨C₂, hC₂, c₂, hc₂, hgood⟩ := exists_measure_not_cubeStatGood_le hd hpc
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = min c c₂ := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc']; exact lt_min hc hc₂
  have hc'c : c' ≤ c := by rw [hc']; exact min_le_left _ _
  have hc'c₂ : c' ≤ c₂ := by rw [hc']; exact min_le_right _ _
  obtain ⟨K'', hK''⟩ : ∃ K'' : ℝ, K'' = max K' (2 * C₂.toReal) := ⟨_, rfl⟩
  have hK''1 : K' ≤ K'' := by rw [hK'']; exact le_max_left _ _
  have hK''2 : 2 * C₂.toReal ≤ K'' := by rw [hK'']; exact le_max_right _ _
  refine ⟨K, lam, s, c', K'', hK, hlam0, hlam1, hs0, hs1, hc'0, hK'.trans hK''1,
    fun m z => ?_, fun V => ?_⟩
  · have h := htail m
    rw [← measure_preimage_configurationTranslation_general p z] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hX : 0 ≤ ((3 : ℝ) ^ m) ^ s := by positivity
    refine mul_le_mul hK''1 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (hK'.trans hK''1)
    have := mul_le_mul_of_nonneg_right hc'c hX
    linarith
  · have hsub : {ω | ¬ CubeSubaddGood p ω V K lam} ⊆ {ω | ¬ CubeStatGood ω V} ∪
        configurationTranslation (-V.center) ⁻¹'
          {ω | ¬ CubeSubaddGood p ω ⟨V.scale, 0⟩ K lam} := by
      intro ω hω
      by_contra hne
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, not_or, not_not] at hne
      exact hω (cubeSubaddGood_of_statGood hne.1 hne.2)
    have hX0 : 0 ≤ ((3 : ℝ) ^ V.scale) ^ s := by positivity
    have h1 : latticeBondLaw d p {ω | ¬ CubeStatGood ω V} ≤
        ENNReal.ofReal (K'' * Real.exp (-c' * ((3 : ℝ) ^ V.scale) ^ s)) := by
      refine (hgood V).trans ?_
      rw [show (2 : ℝ≥0∞) * C₂ = ENNReal.ofReal (2 * C₂.toReal) by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC₂, ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul hK''2 (Real.exp_le_exp.2 ?_)
        (Real.exp_pos _).le (hK'.trans hK''1))
      have h3 : ((3 : ℝ) ^ V.scale) ^ s ≤ (3 : ℝ) ^ V.scale := by
        calc ((3 : ℝ) ^ V.scale) ^ s ≤ ((3 : ℝ) ^ V.scale) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hs1
          _ = _ := Real.rpow_one _
      have h4 := mul_le_mul_of_nonneg_right hc'c₂ hX0
      have h5 := mul_le_mul_of_nonneg_left h3 hc₂.le
      linarith
    have h2 : latticeBondLaw d p (configurationTranslation (-V.center) ⁻¹'
          {ω | ¬ CubeSubaddGood p ω ⟨V.scale, 0⟩ K lam}) ≤
        ENNReal.ofReal (K'' * Real.exp (-c' * ((3 : ℝ) ^ V.scale) ^ s)) := by
      rw [measure_preimage_configurationTranslation_general]
      refine (htail V.scale).trans (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul hK''1 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (hK'.trans hK''1)
      have := mul_le_mul_of_nonneg_right hc'c hX0
      linarith
    have hK''0 : 0 ≤ K'' * Real.exp (-c' * ((3 : ℝ) ^ V.scale) ^ s) :=
      mul_nonneg (hK'.trans hK''1) (Real.exp_pos _).le
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add h1 h2).trans ?_))
    rw [← ENNReal.ofReal_add hK''0 hK''0]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith

theorem TriadicCube.center_mem_vertices (V : TriadicCube d) : V.center ∈ V.vertices := by
  intro i
  change |2 * (V.side * V.index i - V.side * V.index i)| < V.side
  simp [V.side_pos]

/-- A triadic cube of scale `n` inside `U` is a subcube of `U` of scale `n`. -/
theorem mem_subcubesAt_of_subset_general {U V : TriadicCube d} {n : ℕ} (hV : V.scale = n)
    (hVU : V.vertices ⊆ U.vertices) : V ∈ U.subcubesAt n := by
  refine Finset.mem_image.2 ⟨V.center, (U.mem_toIntegerCube_vertices _).2
    (hVU V.center_mem_vertices), ?_⟩
  exact TriadicCube.eq_of_mem_of_scale_eq (by rw [scale_triadicCubeAt, hV])
    (mem_triadicCubeAt n _) V.center_mem_vertices

/-- `3^{dm} exp(-c (3^m)^s) ≤ K₁ exp(-(c/2) (3^m)^s)` for every `m`. -/
theorem exists_three_pow_mul_exp_rpow_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ m : ℕ, ((3 : ℝ) ^ m) ^ d * Real.exp (-c * ((3 : ℝ) ^ m) ^ s) ≤
      K₁ * Real.exp (-(c / 2) * ((3 : ℝ) ^ m) ^ s) := by
  set k : ℕ := ⌈(d : ℝ) / s⌉₊ with hk
  refine ⟨(k.factorial : ℝ) * (2 / c) ^ k, by positivity, fun m => ?_⟩
  set X : ℝ := ((3 : ℝ) ^ m) ^ s with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hs.le
  have hdk : ((3 : ℝ) ^ m) ^ d ≤ X ^ k := by
    have e : ((3 : ℝ) ^ m) ^ d = X ^ ((d : ℝ) / s) := by
      rw [hX, ← Real.rpow_mul (by positivity), mul_div_cancel₀ _ hs.ne', Real.rpow_natCast]
    rw [e, ← Real.rpow_natCast X k]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (Nat.le_ceil _)
  calc ((3 : ℝ) ^ m) ^ d * Real.exp (-c * X) ≤ X ^ k * Real.exp (-c * X) :=
        mul_le_mul_of_nonneg_right hdk (Real.exp_pos _).le
    _ ≤ _ := pow_mul_exp_neg_mul_le hc (by positivity) k

/-- The exponential moment of a scale with values in `[0, ∞]` is the bound `O_s` of its real
part. -/
theorem isOsBond_toReal_of_exp_moment_general {p : unitInterval}
    {M : Configuration d → ℝ≥0∞} {s θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun ω => Real.exp (((M ω).toReal / θ) ^ s)) (latticeBondLaw d p))
    (hle : (∫ ω, Real.exp (((M ω).toReal / θ) ^ s) ∂(latticeBondLaw d p)) ≤ 2) :
    IsOsBond d p (fun ω => (M ω).toReal) s θ := by
  have e : ∀ ω, Real.exp (Real.rpow (max ((M ω).toReal / θ) 0) s) =
      Real.exp (((M ω).toReal / θ) ^ s) := fun ω => by
    rw [max_eq_left (div_nonneg ENNReal.toReal_nonneg hθ.le)]
    rfl
  unfold IsOsBond
  simp only [e]
  exact ⟨hint, hle⟩

/-- **Definition 5.12 and Proposition 5.13 of Armstrong and Dario for a general mesoscopic
scale** (every dimension `d ≥ 2`, given the bound of Lemma 5.9): for every scale `n(m) ≤ m` with
`m ≤ L n(m)` there is a random scale `𝒩 ≤ O_r(θ)` such that, whenever `𝒩 ≤ 3ᵐ`, Proposition 5.2
holds at level `K λ^{n(m)}` on every triadic subcube of `□_m` of scale `n(m)` and on `□_{n(m)}` in
the configuration translated by `-z`, for every `z ∈ □_m`. -/
theorem exists_cubeBoundN_general_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l)
    {L : ℕ} (hL : 0 < L) (nf : ℕ → ℕ) (hnf : ∀ m, nf m ≤ m ∧ m ≤ L * nf m) :
    ∃ K lam r θ : ℝ, 0 ≤ K ∧ 0 < lam ∧ lam < 1 ∧ 0 < r ∧ 0 < θ ∧
      ∃ N : Configuration d → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond d p N r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, N ω ≤ 3 ^ m →
          (∀ V : TriadicCube d, V.scale = nf m →
            V.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices → CubeSubaddGood p ω V K lam) ∧
          ∀ z ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
            CubeSubaddGood p (configurationTranslation (-z) ω) ⟨nf m, 0⟩ K lam := by
  obtain ⟨K, lam, s, c, K', hK, hlam0, hlam1, hs0, hs1, hc, hK', htr, hcube⟩ :=
    exists_cubeSubaddGood_tail_cube_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  set μ := latticeBondLaw d p with hμ
  obtain ⟨bad, hbad⟩ : ∃ bad : ℕ → Set (Configuration d), ∀ m, bad m = {ω |
      ¬ ((∀ V : TriadicCube d, V.scale = nf m →
          V.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices → CubeSubaddGood p ω V K lam) ∧
        ∀ z ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
          CubeSubaddGood p (configurationTranslation (-z) ω) ⟨nf m, 0⟩ K lam)} :=
    ⟨_, fun _ => rfl⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hs'0 : 0 < s / L := by positivity
  obtain ⟨K₁, hK₁0, h₁⟩ := exists_three_pow_mul_exp_rpow_le (d := d) hc hs'0
  have hsumle : ∀ {ι : Type} (S : Finset ι) (f : ι → ℝ≥0∞) {b : ℝ},
      (∀ i ∈ S, f i ≤ ENNReal.ofReal b) → ∑ i ∈ S, f i ≤ ENNReal.ofReal (S.card * b) := by
    intro ι S f b h
    by_cases hb : 0 ≤ b
    · refine (Finset.sum_le_card_nsmul S f _ h).trans (le_of_eq ?_)
      rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    · have h0 : ∀ i ∈ S, f i = 0 := fun i hi => by
        have := h i hi
        rwa [ENNReal.ofReal_of_nonpos (not_le.1 hb).le, nonpos_iff_eq_zero] at this
      rw [Finset.sum_eq_zero h0]
      exact zero_le
  have hbadm : ∀ m, μ (bad m) ≤ ENNReal.ofReal (3 * K' * K₁) *
      ENNReal.ofReal (Real.exp (-(c / 2) * ((3 : ℝ) ^ m) ^ (s / L))) := by
    intro m
    rw [hbad]
    have hnm : nf m ≤ (⟨m, 0⟩ : TriadicCube d).scale := (hnf m).1
    have hLn : (m : ℝ) ≤ L * (nf m : ℝ) := by exact_mod_cast (hnf m).2
    generalize nf m = n at hnm hLn ⊢
    have hsub : {ω | ¬ ((∀ V : TriadicCube d, V.scale = n →
          V.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices → CubeSubaddGood p ω V K lam) ∧
        ∀ z ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
          CubeSubaddGood p (configurationTranslation (-z) ω) ⟨n, 0⟩ K lam)} ⊆
        (⋃ V ∈ (⟨m, 0⟩ : TriadicCube d).subcubesAt n,
          {ω | ¬ CubeSubaddGood p ω V K lam}) ∪
        ⋃ z ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
          {ω | ¬ CubeSubaddGood p (configurationTranslation (-z) ω) ⟨n, 0⟩ K lam} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      by_contra hne
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
        not_not] at hne
      apply hω
      refine ⟨fun V hV hVU => hne.1 V (mem_subcubesAt_of_subset_general hV hVU), fun z hz => ?_⟩
      exact hne.2 z ((TriadicCube.mem_toIntegerCube_vertices _ z).2 hz)
    have hX : ((3 : ℝ) ^ m) ^ (s / L) ≤ ((3 : ℝ) ^ n) ^ s := by
      rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [mul_div_assoc', div_le_iff₀ hL0]
      nlinarith
    have hvol : (⟨m, 0⟩ : TriadicCube d).latticeVolume = ((3 : ℝ) ^ m) ^ d := rfl
    have hcard : (((⟨m, 0⟩ : TriadicCube d).subcubesAt n).card : ℝ) ≤ ((3 : ℝ) ^ m) ^ d := by
      have h := card_subcubesAt_mul_general (⟨m, 0⟩ : TriadicCube d) hnm
      rw [hvol] at h
      have h9 : (1 : ℝ) ≤ ((3 : ℝ) ^ n) ^ d := one_le_pow₀ (one_le_pow₀ (by norm_num))
      have h0 : (0 : ℝ) ≤ ((⟨m, 0⟩ : TriadicCube d).subcubesAt n).card := Nat.cast_nonneg _
      nlinarith
    have hcardU : (((⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices.card : ℕ) : ℝ) =
        ((3 : ℝ) ^ m) ^ d := by
      rw [TriadicCube.card_toIntegerCube_vertices]
      rfl
    have he0 : 0 ≤ Real.exp (-c * ((3 : ℝ) ^ n) ^ s) := (Real.exp_pos _).le
    have hA : μ (⋃ V ∈ (⟨m, 0⟩ : TriadicCube d).subcubesAt n,
        {ω | ¬ CubeSubaddGood p ω V K lam}) ≤
        ENNReal.ofReal (((3 : ℝ) ^ m) ^ d * (2 * K' * Real.exp (-c * ((3 : ℝ) ^ n) ^ s))) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (hsumle _ _ fun V hV => ?_).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity)))
      have := hcube V
      rwa [TriadicCube.scale_of_mem_subcubesAt hV] at this
    have hB : μ (⋃ z ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
        {ω | ¬ CubeSubaddGood p (configurationTranslation (-z) ω) ⟨n, 0⟩ K lam}) ≤
        ENNReal.ofReal (((3 : ℝ) ^ m) ^ d * (K' * Real.exp (-c * ((3 : ℝ) ^ n) ^ s))) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (hsumle _ _ fun z _ => htr n (-z)).trans (le_of_eq (by rw [hcardU]))
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hA hB).trans ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := h₁ m
    have he' : Real.exp (-c * ((3 : ℝ) ^ n) ^ s) ≤ Real.exp (-c * ((3 : ℝ) ^ m) ^ (s / L)) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hX hc.le
      linarith
    have h9 : (0 : ℝ) ≤ ((3 : ℝ) ^ m) ^ d := by positivity
    have h2 : ((3 : ℝ) ^ m) ^ d * Real.exp (-c * ((3 : ℝ) ^ n) ^ s) ≤
        K₁ * Real.exp (-(c / 2) * ((3 : ℝ) ^ m) ^ (s / L)) :=
      (mul_le_mul_of_nonneg_left he' h9).trans h1
    have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 3 * K' by positivity)
    have e : ((3 : ℝ) ^ m) ^ d * (2 * K' * Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) +
        ((3 : ℝ) ^ m) ^ d * (K' * Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) =
        3 * K' * (((3 : ℝ) ^ m) ^ d * Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) := by ring
    rw [e]
    linarith
  set E : ℕ → Set (Configuration d) := fun m => toMeasurable μ (bad m) with hE
  have hEm : ∀ m, MeasurableSet (E m) := fun m => measurableSet_toMeasurable _ _
  have hEμ : ∀ m, μ (E m) ≤ ENNReal.ofReal (3 * K' * K₁) *
      ENNReal.ofReal (Real.exp (-(c / 2) * ((3 : ℝ) ^ m) ^ (s / L))) := fun m => by
    rw [hE, measure_toMeasurable]
    exact hbadm m
  obtain ⟨θ, hθ, hint, hle⟩ := exceptionalScale_exp_moment μ E hEm _ ENNReal.ofReal_ne_top
    (s / L) (c / 2) hs'0 (by positivity) hEμ
  have hfin : ∀ᵐ ω ∂μ, exceptionalScale E ω ≠ ∞ :=
    ae_exceptionalScale_ne_top μ E _ ENNReal.ofReal_ne_top ((3 : ℝ) ^ (s / L)) (c / 2)
      (Real.one_lt_rpow (by norm_num) hs'0) (by positivity) (fun m => by
        rw [Real.rpow_pow_comm (show (0 : ℝ) ≤ 3 by norm_num) (s / L) m]
        exact hEμ m)
  have hos := isOsBond_toReal_of_exp_moment_general (p := p) hθ hint hle
  refine ⟨K, lam, s / L, 3 * θ, hK, hlam0, hlam1, hs'0, by positivity,
    fun ω => 3 * (exceptionalScale E ω).toReal,
    ((measurable_exceptionalScale E hEm).ennreal_toReal).const_mul 3,
    fun ω => by positivity, Rigidity.Proofs.S2.IsOsBond.const_mul (by norm_num) hos, ?_⟩
  filter_upwards [hfin] with ω hω m hm
  have hlt : exceptionalScale E ω < 3 ^ m := by
    have h1 : (exceptionalScale E ω).toReal < (3 : ℝ) ^ m := by
      have := ENNReal.toReal_nonneg (a := exceptionalScale E ω)
      have h3 : (0 : ℝ) < 3 ^ m := by positivity
      linarith
    rw [← ENNReal.ofReal_toReal hω, show (3 : ℝ≥0∞) ^ m = ENNReal.ofReal ((3 : ℝ) ^ m) by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 h1
  have hnot : ω ∉ bad m := by
    intro hb
    have hωE : ω ∈ E m := subset_toMeasurable μ (bad m) hb
    have h3 : (3 : ℝ≥0∞) ^ m ≤ exceptionalScale E ω := by
      unfold exceptionalScale
      exact le_iSup_of_le m (by rw [if_pos hωE])
    exact absurd hlt (not_lt.2 h3)
  by_contra h
  exact hnot (by rw [hbad]; exact h)

/-- **Definition 5.12 and Proposition 5.13 of Armstrong and Dario** (every dimension `d ≥ 2`,
given the bound of Lemma 5.9): a random scale `𝒩 ≤ O_r(θ)` above which, with `n = ⌈m/4⌉`,
`μ(·, q)` and `ν(·, ā⁻¹ q)` are within `K |q|² λⁿ` of `-(1/2) q · ā⁻¹ q` and `(1/2) q · ā⁻¹ q` on
every triadic cube of scale `n` contained in `□_m`, and on `□_n` in the configuration translated by
`-z` for every `z ∈ □_m`. -/
theorem exists_cubeBoundN_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K lam r θ : ℝ, 0 ≤ K ∧ 0 < lam ∧ lam < 1 ∧ 0 < r ∧ 0 < θ ∧
      ∃ N : Configuration d → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond d p N r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, N ω ≤ 3 ^ m →
          (∀ V : TriadicCube d, V.scale = (m + 3) / 4 →
            V.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices → CubeSubaddGood p ω V K lam) ∧
          ∀ z ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
            CubeSubaddGood p (configurationTranslation (-z) ω) ⟨(m + 3) / 4, 0⟩ K lam :=
  exists_cubeBoundN_general_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59 (L := 4) (by norm_num)
    (fun m => (m + 3) / 4) (fun m => ⟨by omega, by omega⟩)

end Rigidity.Percolation
