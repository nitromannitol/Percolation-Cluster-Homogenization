import PercolationClusterHomogenization.Proofs.Cluster.PlanarMinimalScales
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHProb
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHPartition
import PercolationClusterHomogenization.Proofs.Cluster.GeneralReachDomination
import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralScaleForms

/-!
# The minimal scales of the reverse Hölder cells and of the reach, in every dimension

Armstrong and Dario (arXiv:1609.09431v2), Definition 3.7 with Propositions 2.1 and 2.4: the
partition `𝓡` into cells whose predecessors are reverse Hölder cubes (`rhGood`), and the minimal
scales above which the moments and the sizes of the cells, and of the reach of the partition into
good cubes, are controlled on `□_m`. `CubeRegularityScales d p` records them in the form used in
the proof of Lemma 7.1, and `cubeRegularityScales_holds` proves it for `p > p_c(d)`, `d ≥ 2`. The
planar form is `PlanarMinimalScales` (`planarMinimalScales_holds`), which also bounds the
partition cubes; in every dimension those bounds are `CubeMinimalScales` (`cubeMinimalScales_holds`).

The reach of the partition is dominated by the stopping size of the coarsely good cubes
(`partitionReach_le_stoppingSize_coarseGood`), and both stopping sizes satisfy Proposition 2.4
(`exists_cube_minimalScaleLocal`, from `exists_minimalScale_general`).
-/

namespace Rigidity.Proofs.Cluster.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {d : ℕ}

/-- **Proposition 2.4 of Armstrong and Dario for a local family, with a real minimal scale**
(every dimension): for every `τ ∈ ℕ` and `α > 0` there are `K`, `r, θ > 0` and `M ≤ O_r(θ)` such
that almost surely, whenever `M ≤ 3ᵐ`, `∑_{x ∈ □_m} size(x)^τ ≤ K |□_m|` and `size(x) ≤ 3^{α m}`
on `□_m`. -/
theorem exists_cube_minimalScaleLocal (hd : 0 < d) (p : unitInterval)
    (G : Configuration d → Set (TriadicCube d))
    (hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω})
    (hloc : ∀ T : TriadicCube d,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c) (hs0 : 0 < s0) (hs1 : s0 ≤ 1)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)))
    (τ : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ K r θ : ℝ, 0 ≤ K ∧ 0 < r ∧ 0 < θ ∧
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω ≤ 3 ^ m →
          ∑ x ∈ cube m (0 : Vertex d), TriadicCube.stoppingSize (G ω) x ^ τ ≤
              K * (cube m (0 : Vertex d)).card ∧
            ∀ x ∈ cube m (0 : Vertex d), TriadicCube.stoppingSize (G ω) x ≤ ((3 : ℝ) ^ m) ^ α := by
  obtain ⟨C, r, hr, M₀, hM₀m, hfin, ⟨θ, hθ, hint, hle⟩, hprop⟩ :=
    exists_minimalScale_general (d := d) hd p G hGm hloc hC1 hc hs0 hs1 hq τ hα
  have hos := Rigidity.Dirichlet.isOsBond_toReal_of_exp_moment (p := p) hθ hint hle
  refine ⟨max C 0, r, 3 * θ, le_max_right _ _, hr, by positivity,
    fun ω => 3 * (M₀ ω).toReal, (hM₀m.ennreal_toReal).const_mul 3,
    fun ω => by positivity, Rigidity.Proofs.S2.IsOsBond.const_mul (by norm_num) hos, ?_⟩
  filter_upwards [hfin, hprop] with ω hω hpr m hm
  have hlt : M₀ ω < 3 ^ m := by
    have h1 : (M₀ ω).toReal < (3 : ℝ) ^ m := by
      have := ENNReal.toReal_nonneg (a := M₀ ω)
      have h3 : (0 : ℝ) < 3 ^ m := by positivity
      linarith
    rw [← ENNReal.ofReal_toReal hω, show (3 : ℝ≥0∞) ^ m = ENNReal.ofReal ((3 : ℝ) ^ m) by
      rw [ENNReal.ofReal_pow (by norm_num)]; norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 h1
  obtain ⟨hsum, hsize⟩ := hpr m hlt
  refine ⟨?_, fun x hx => hsize x (mem_cube_zero_iff.1 hx)⟩
  rw [cube_zero_eq_vertices]
  refine hsum.trans ?_
  have hcard : (((originCube d m).toIntegerCube.vertices.card : ℕ) : ℝ) = (3 : ℝ) ^ (d * m) := by
    rw [← cube_zero_eq_vertices, card_cube, ← pow_mul, mul_comm]
  rw [hcard]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **The minimal scales of the reverse Hölder cells and of the reach** (Armstrong and Dario,
Definition 3.7 with Propositions 2.1 and 2.4, every dimension, form `O_s`): a constant `A₀` and a
cell scale `s` whose cells `cube (s x) x` form a partition with comparable neighbours and whose
predecessors are in `rhGood A₀`, and for all `t, α > 0` a minimal scale `M ≤ O_r(θ)` above which
`∑_{□_m} (3^{s(x)})^t ≤ K |□_m|`, `3^{s(x)} ≤ 3^{α m}`, `∑_{□_m} reach(x)^{⌈t⌉} ≤ K |□_m|` and
`reach(x) ≤ 3^{α m}` on `□_m`. -/
def CubeRegularityScales (d : ℕ) (p : unitInterval) : Prop :=
  ∃ A₀ : ℝ, ∃ s : Configuration d → Vertex d → ℕ,
    (∀ᵐ ω ∂(latticeBondLaw d p),
      (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) ∧
    ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α → ∃ K r θ : ℝ, 0 ≤ K ∧ 0 < r ∧ 0 < θ ∧
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω ≤ 3 ^ m →
          ∑ x ∈ cube m (0 : Vertex d), ((3 : ℝ) ^ s ω x) ^ t ≤
              K * (cube m (0 : Vertex d)).card ∧
          (∀ x ∈ cube m (0 : Vertex d), (3 : ℝ) ^ s ω x ≤ ((3 : ℝ) ^ m) ^ α) ∧
          ∑ x ∈ cube m (0 : Vertex d), partitionReach ω x ^ ⌈t⌉₊ ≤
            ENNReal.ofReal (K * (cube m (0 : Vertex d)).card) ∧
          ∀ x ∈ cube m (0 : Vertex d), partitionReach ω x ≤ ENNReal.ofReal (((3 : ℝ) ^ m) ^ α)

/-- **The minimal scales of the reverse Hölder cells and of the reach**, for `p > p_c(d)`,
`d ≥ 2`. -/
theorem cubeRegularityScales_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : CubeRegularityScales d p := by
  have hd0 : 0 < d := by omega
  obtain ⟨A₀, C1, c, s0, hC1, hc, hs0, hs1, hfail⟩ := rhFailureBound_holds hd hpc
  set μ := latticeBondLaw d p with hμ
  set G : Configuration d → Set (TriadicCube d) := rhGood A₀ with hG
  have hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω} := measurableSet_mem_rhGood A₀
  have hloc := measurableSet_not_mem_rhGood_local (d := d) A₀
  obtain ⟨hae, -, -⟩ := partition_estimates_general hd0 μ G hGm hC1 hc hs0 hfail
  obtain ⟨C₀, hC₀, c₀, hc₀, hq₀⟩ := exists_measure_not_mem_coarseGood_le hd hpc
  have hH : ∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (coarseGood ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched μ
      coarseGood (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top 1 c₀ one_pos hc₀ fun R => by
        rw [← ENNReal.ofReal_mul hC₀]
        exact hq₀ R
  refine ⟨A₀, fun ω => stoppingScale (G ω), ?_, fun t ht α hα => ?_⟩
  · filter_upwards [hae] with ω hu
    exact ⟨fun x z hz => stoppingScale_eq_of_mem_cube hu hz,
      fun x y hxy => stoppingScale_le_of_supDist hu hxy,
      fun k y hk => mem_of_stoppingScale_le hu hk⟩
  set τ : ℕ := ⌈t⌉₊ with hτ
  have htτ : t ≤ τ := Nat.le_ceil t
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁⟩ :=
    exists_cube_minimalScaleLocal hd0 p G hGm hloc hC1 hc hs0 hs1 hfail τ hα
  obtain ⟨K₂, r₂, θ₂, hK₂, hr₂, hθ₂, M₂, hM₂m, hM₂0, hM₂os, hM₂⟩ :=
    exists_cube_minimalScaleLocal hd0 p coarseGood measurableSet_mem_coarseGood
      measurableSet_not_mem_coarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq₀ τ hα
  set r : ℝ := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min hr₁ hr₂
  have h1 := Rigidity.Proofs.S2.IsOsBond.mono_exponent hr0 (min_le_left _ _) hM₁m hM₁os
  have h2 := Rigidity.Proofs.S2.IsOsBond.mono_exponent hr0 (min_le_right _ _) hM₂m hM₂os
  have h12 := Rigidity.Proofs.S2.IsOsBond.max hr0 (by positivity) (by positivity) hM₁m hM₂m h1 h2
  refine ⟨max K₁ K₂, r, _, le_max_of_le_left hK₁, hr0, by positivity,
    fun ω => max (M₁ ω) (M₂ ω), hM₁m.max hM₂m, fun ω => le_max_of_le_left (hM₁0 ω), h12, ?_⟩
  filter_upwards [hae, hH, hM₁, hM₂] with ω hu hH' hb₁ hb₂ m hm
  obtain ⟨hs₁, hz₁⟩ := hb₁ m ((le_max_left _ _).trans hm)
  obtain ⟨hs₂, hz₂⟩ := hb₂ m ((le_max_right _ _).trans hm)
  have hK : ∀ S : ℝ, S ≤ K₁ * (cube m (0 : Vertex d)).card ∨
      S ≤ K₂ * (cube m (0 : Vertex d)).card → S ≤ max K₁ K₂ * (cube m (0 : Vertex d)).card := by
    rintro S (h | h)
    · exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
    · exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
  set S₂ : Vertex d → ℝ := fun x => TriadicCube.stoppingSize (coarseGood ω) x with hS₂
  have hS₂0 : ∀ x, 0 ≤ S₂ x := fun x => TriadicCube.stoppingSize_nonneg _ x
  have hreach : ∀ x, partitionReach ω x ≤ ENNReal.ofReal (S₂ x) :=
    partitionReach_le_stoppingSize_coarseGood hH'
  have hpow : ∀ {a : ℕ} {b : ℝ}, (3 : ℝ) ^ a ≤ b → ((3 : ℝ) ^ a) ^ t ≤ b ^ τ := by
    intro a b hab
    calc ((3 : ℝ) ^ a) ^ t ≤ ((3 : ℝ) ^ a) ^ (τ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) htτ
      _ = ((3 : ℝ) ^ a) ^ τ := Real.rpow_natCast _ τ
      _ ≤ b ^ τ := pow_le_pow_left₀ (by positivity) hab τ
  refine ⟨hK _ (Or.inl ((Finset.sum_le_sum fun x _ => hpow
      (stoppingSize_eq_stoppingScale hu x).ge).trans hs₁)),
    fun x hx => (stoppingSize_eq_stoppingScale hu x).symm.le.trans (hz₁ x hx), ?_,
    fun x hx => (hreach x).trans (ENNReal.ofReal_le_ofReal (hz₂ x hx))⟩
  calc ∑ x ∈ cube m (0 : Vertex d), partitionReach ω x ^ ⌈t⌉₊
      ≤ ∑ x ∈ cube m (0 : Vertex d), ENNReal.ofReal (S₂ x ^ τ) :=
        Finset.sum_le_sum fun x _ => by
          rw [ENNReal.ofReal_pow (hS₂0 x)]
          exact pow_le_pow_left₀ zero_le (hreach x) τ
    _ = ENNReal.ofReal (∑ x ∈ cube m (0 : Vertex d), S₂ x ^ τ) :=
        (ENNReal.ofReal_sum_of_nonneg fun x _ => pow_nonneg (hS₂0 x) τ).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hK _ (Or.inr hs₂))

end Rigidity.Proofs.Cluster.GeneralDim
