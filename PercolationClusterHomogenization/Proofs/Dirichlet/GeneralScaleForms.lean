import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralTheoremOne
import PercolationClusterHomogenization.Proofs.Partition.MinimalScaleCombined
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSectionFive

/-!
# The minimal scales and Proposition 5.13 in the forms used in Section 6, in every dimension

Two consequences of `exists_minimalScale` and `exists_cubeBoundN_general_of_decay`, stated in the
form of the inputs of the proof of Theorem 1 of Armstrong and Dario in every dimension `d ≥ 2`:

* `cubeMinimalScales_holds`: for every `t ≥ 1` a minimal scale `𝓜_t ≤ O_s(C)` of the partition
  into good cubes with `|□_m|⁻¹ Σ_{x ∈ □_m} size(□_𝒫(x))^t ≤ C` and
  `size(□_𝒫(x)) ≤ 3^{dm/(d+t)}` on `□_m` whenever `𝓜_t ≤ 3ᵐ` (both bounds of (2.13));
* `cubeMesoscopicConvergence_holds`: Proposition 5.13 on the triadic subcubes of `□_m` of scale
  `⌈m/8⌉`, with the rate `λ^{⌈m/8⌉}` of `CubeSubaddGood` written as `3^{-αm}`.

The planar forms are `planarMinimalScales_partition_holds` and `planarMesoscopicConvergence_holds`.
-/

open MeasureTheory LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External
open scoped Matrix ENNReal

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The exponential moment of a scale with values in `[0, ∞]` is the bound `O_s` of its real
part. -/
theorem isOsBond_toReal_of_exp_moment {p : unitInterval} {M : Configuration d → ℝ≥0∞}
    {s θ : ℝ} (hθ : 0 < θ)
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

/-- **Both bounds of (2.13) for the partition into good cubes** (Armstrong and Dario,
Proposition 2.4, every dimension `d ≥ 2`, `p > p_c(d)`), for real exponents `t ≥ 1`. -/
theorem cubeMinimalScales_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : CubeMinimalScales d p := by
  intro t ht
  set τ := ⌈t⌉₊ with hτ
  have htτ : t ≤ τ := Nat.le_ceil t
  obtain ⟨C, s, hs, M, hMm, hMfin, ⟨θ, hθ, hint, hle⟩, hM⟩ := exists_minimalScale hd hpc τ
  have hos0 := isOsBond_toReal_of_exp_moment (p := p) hθ hint hle
  have hmT : Measurable fun ω => (M ω).toReal := hMm.ennreal_toReal
  have hos1 := Rigidity.Proofs.S2.IsOsBond.max hs hθ (by positivity) hmT measurable_const hos0
    (Rigidity.Proofs.S2.isOsBond_const (d := d) (p := p) one_pos hs)
  have hos2 := Rigidity.Proofs.S2.IsOsBond.const_mul (c := 2) two_pos hos1
  set θ' := 2 * (max θ (1 * 3 ^ (1 / s)) * 4 ^ (1 / s)) with hθ'
  have hθ'0 : 0 < θ' := by positivity
  set Cf := max (max C 1) θ' with hCf
  have hCf0 : 0 < Cf := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
  have hmeas : Measurable fun ω => 2 * max (M ω).toReal 1 :=
    (hmT.max measurable_const).const_mul 2
  refine ⟨s, Cf, hs, hCf0, fun ω => 2 * max (M ω).toReal 1, hmeas,
    fun ω => by positivity,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs hθ'0 (le_max_right _ _) hmeas hos2, ?_⟩
  filter_upwards [hM, hMfin, (partition_estimates hd hpc).1] with ω hω hfin hP m hm
  have hX : (M ω).toReal < 3 ^ m := by
    have h1 : (M ω).toReal + 1 ≤ 2 * max (M ω).toReal 1 := by
      have := le_max_left (M ω).toReal 1
      have := le_max_right (M ω).toReal 1
      linarith
    linarith
  have hlt : M ω < 3 ^ m := by
    have h3 : ((3 : ℝ≥0∞) ^ m).toReal = (3 : ℝ) ^ m := by
      rw [ENNReal.toReal_pow]
      norm_num
    exact (ENNReal.toReal_lt_toReal hfin (ENNReal.pow_ne_top (by norm_num))).1 (by rw [h3]; exact hX)
  obtain ⟨hsum, hsize⟩ := hω m hlt
  constructor
  · have hsub : (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices ⊆
        partitionClosure ω (originCube d m).toIntegerCube.vertices := by
      intro x hx
      refine Finset.mem_biUnion.2 ⟨x, hx, ?_⟩
      rw [TriadicCube.mem_toIntegerCube_vertices]
      exact mem_partitionCube hP x
    have hpt : ∀ x, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ t ≤
        (3 : ℝ) ^ (τ * (partitionCube ω x).scale) := by
      intro x
      rw [show τ * (partitionCube ω x).scale = (partitionCube ω x).scale * τ from mul_comm _ _,
        pow_mul, ← Real.rpow_natCast ((3 : ℝ) ^ (partitionCube ω x).scale) τ]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) htτ
    have hV : ((3 : ℝ) ^ m) ^ d = 3 ^ (d * m) := by rw [← pow_mul, mul_comm]
    rw [hV]
    refine le_trans (div_le_div_of_nonneg_right ?_ (by positivity)) (hsum.trans
      ((le_max_left _ _).trans (le_max_left _ _)))
    calc ∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
          ((3 : ℝ) ^ (partitionCube ω x).scale) ^ t
        ≤ ∑ x ∈ (⟨m, 0⟩ : TriadicCube d).toIntegerCube.vertices,
          (3 : ℝ) ^ (τ * (partitionCube ω x).scale) := Finset.sum_le_sum fun x _ => hpt x
      _ ≤ ∑ x ∈ partitionClosure ω (originCube d m).toIntegerCube.vertices,
          (3 : ℝ) ^ (τ * (partitionCube ω x).scale) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  · intro x hx
    refine (hsize x hx).trans ?_
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [mul_div_assoc', mul_comm (m : ℝ) d]
    have ht0 : (0 : ℝ) < d + t := by linarith
    have hτ0 : (0 : ℝ) < d + τ := by linarith
    exact div_le_div_of_nonneg_left (by positivity) ht0 (by linarith)

/-- **Proposition 5.13 on the triadic cubes of scale `⌈m/8⌉`** (Armstrong and Dario,
Definition 5.12, Proposition 5.13 and (6.10)-(6.11), every dimension `d ≥ 2`, `p > p_c(d)`). -/
theorem cubeMesoscopicConvergence_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : CubeMesoscopicConvergence d p := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ₉, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  obtain ⟨K, lam, r, θ, hK, hlam0, hlam1, hr, hθ, N, hNm, hN0, hNos, hN⟩ :=
    exists_cubeBoundN_general_of_decay hd hpc hC hσ₉ hσ1 hρ hρ1 h59 (L := 8) (by norm_num)
      (fun m => (m + 7) / 8) (fun m => ⟨by omega, by omega⟩)
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  set β := -Real.logb 3 lam with hβ
  have hβ0 : 0 < β := by
    rw [hβ, neg_pos]
    exact Real.logb_neg (by norm_num) hlam0 hlam1
  set Cm := max (max K (K * σ ^ 2)) θ with hCm
  have hCm0 : 0 < Cm := lt_of_lt_of_le hθ (le_max_right _ _)
  refine ⟨r, β / 8, Cm, hr, by positivity, hCm0, N, hNm, hN0,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hr hθ (le_max_right _ _) hNm hNos, ?_⟩
  filter_upwards [hN] with ω hω m hm T hT hTU q ξ
  obtain ⟨-, -, hμb, hνb⟩ := (hω m hm).1 T hT hTU
  have hrate : lam ^ T.scale ≤ (3 : ℝ) ^ (-(β / 8 * m)) := by
    have hlam : lam = (3 : ℝ) ^ (Real.logb 3 lam) := (Real.rpow_logb (by norm_num) (by norm_num)
      hlam0).symm
    rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [hT]
    have hm8 : (m : ℝ) ≤ 8 * ((m + 7) / 8 : ℕ) := by exact_mod_cast (show m ≤ 8 * ((m + 7) / 8) by
      omega)
    have : -β = Real.logb 3 lam := by rw [hβ, neg_neg]
    rw [← this]
    nlinarith
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hξ0 : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlamS : 0 ≤ lam ^ T.scale := by positivity
  constructor
  · refine (hμb q).trans ?_
    calc K * (∑ i, q i ^ 2) * lam ^ T.scale ≤ K * (∑ i, q i ^ 2) * (3 : ℝ) ^ (-(β / 8 * m)) :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
      _ ≤ Cm * (∑ i, q i ^ 2) * (3 : ℝ) ^ (-(β / 8 * m)) := by
          gcongr
          exact (le_max_left _ _).trans (le_max_left _ _)
  · have hinv : (cubeAhom p)⁻¹ *ᵥ (σ • ξ) = ξ := by
      rw [hA, inv_smul_one_eq hσ.ne', Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
        inv_mul_cancel₀ hσ.ne', one_smul]
    have h := hνb (σ • ξ)
    rw [hinv] at h
    have e1 : 1 / 2 * ∑ i, (σ • ξ) i * ξ i = 1 / 2 * ∑ i, ξ i * (cubeAhom p *ᵥ ξ) i := by
      rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ∑ i, (σ • ξ) i ^ 2 = σ ^ 2 * ∑ i, ξ i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2] at h
    refine h.trans ?_
    calc K * (σ ^ 2 * ∑ i, ξ i ^ 2) * lam ^ T.scale
        ≤ K * (σ ^ 2 * ∑ i, ξ i ^ 2) * (3 : ℝ) ^ (-(β / 8 * m)) :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = K * σ ^ 2 * (∑ i, ξ i ^ 2) * (3 : ℝ) ^ (-(β / 8 * m)) := by ring
      _ ≤ Cm * (∑ i, ξ i ^ 2) * (3 : ℝ) ^ (-(β / 8 * m)) := by
          gcongr
          exact (le_max_right _ _).trans (le_max_left _ _)

/-- **Armstrong and Dario, Theorem 1, in every dimension `d ≥ 2`, with the discrete homogenized
solution**, for every `𝔭_c(d) < p` and every exponent `p' > 2`, with no further hypothesis. -/
theorem cubeHomogenizationError_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {p' : ℝ} (hp' : 2 < p') :
    CubeHomogenizationError d p p' :=
  cubeHomogenizationError_of_inputs hd hpc (cubeMesoscopicConvergence_holds hd hpc)
    (cubeMinimalScales_holds hd hpc) hp'

end Rigidity.Dirichlet
