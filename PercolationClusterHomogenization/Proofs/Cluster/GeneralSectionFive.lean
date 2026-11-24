import PercolationClusterHomogenization.Proofs.Cluster.GeneralOmegaRate
import PercolationClusterHomogenization.Proofs.Cluster.GeneralConvergenceRate
import PercolationClusterHomogenization.Proofs.Cluster.GeneralIdentification
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSIUpgrade
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSIUpgradeOs

/-!
# Section 5 of Armstrong and Dario in every dimension, without hypothesis

Lemma 5.9 (`exists_cubeOmegaD_le_decay`, with `σ = 3^{-1/4}` and `ρ = 1/3`) discharges the
hypothesis `h59` of the results of Section 5 stated with it. This file states them without it:

* Lemma 5.10, Steps 2 and 3 (`exists_cubeOmegaD_le_pow`, `exists_cubeTau_le_pow`) and Step 4
  (`exists_abs_cubeAhomInvLimit_sub_le_pow`, `cubeAhomInvLimit_eq`);
* Proposition 5.2, qualitative part (`cubeMuLimit_eq`), and display (5.4) in expectation
  (`exists_abs_cubeMuMean_sub_le_pow`, `exists_abs_cubeNuMean_sub_le_pow`);
* display (5.42) (`exists_cubeRho_majorant`) and Lemma 5.11 (`exists_cubeRho_tail`,
  `exists_cubeOmega_isOsBond`, `exists_neg_cubeMu_le_isOsBond`);
* Proposition 5.2, displays (5.2) and (5.3) (`exists_cubeSubaddGood_tail`,
  `exists_cubeSubaddErr_isOsBond`);
* Definition 5.12 and Proposition 5.13 (`exists_cubeBoundN`).

The statements are those of the conditional versions (`*_of_decay`), whose docstrings record how
they differ from the printed ones.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {p : unitInterval}

/-- **Lemma 5.9 of Armstrong and Dario in the form `h59`**: constants `C₉ ≥ 0`, `σ₉ = 3^{-1/4}`,
`ρ₉ = 1/3` and `N₉` with `D_n ≤ C₉ σ₉ⁿ + C₉ ∑_{l ≤ n} ρ₉^{n-l} τ_l` for `n ≥ N₉`. -/
theorem exists_h59 [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C₉ σ₉ ρ₉ : ℝ, ∃ N₉ : ℕ, 0 ≤ C₉ ∧ 0 ≤ σ₉ ∧ σ₉ < 1 ∧ 0 ≤ ρ₉ ∧ ρ₉ < 1 ∧
      ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
        C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l := by
  obtain ⟨C, hC, N, h⟩ := exists_cubeOmegaD_le_decay hd hpc
  exact ⟨C, 1 / √(√(3 : ℝ)), 1 / 3, N, hC, by positivity, one_div_sqrt_sqrt_three_lt_one,
    by norm_num, by norm_num, h⟩

/-- **Lemma 5.10 of Armstrong and Dario, Steps 2 and 3** (every dimension `d ≥ 2`): `D_n` decays
geometrically. Unconditional form of `exists_cubeOmegaD_le_pow_of_decay`. -/
theorem exists_cubeOmegaD_le_pow [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → cubeOmegaD (d := d) p n ≤ K * l ^ n := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeOmegaD_le_pow_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Lemma 5.10 of Armstrong and Dario, Step 3** (every dimension `d ≥ 2`): `τ_n` decays
geometrically. Unconditional form of `exists_cubeTau_le_pow_of_decay`. -/
theorem exists_cubeTau_le_pow [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → cubeTau (d := d) p n ≤ K * l ^ n := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeTau_le_pow_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Lemma 5.10 of Armstrong and Dario** (every dimension `d ≥ 2`): the matrices `ā_{□_n}⁻¹`
converge to their limit at a geometric rate. The printed rate is `C 3^{-n α}`; here `K lⁿ` with
`l < 1`, for the inverse matrices. Unconditional form of
`exists_abs_cubeAhomInvLimit_sub_le_of_decay`. -/
theorem exists_abs_cubeAhomInvLimit_sub_le_pow [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ i j : Fin d,
      |cubeAhomInvLimit p i j - cubeAhomInvFinite p n i j| ≤ K * l ^ n := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_abs_cubeAhomInvLimit_sub_le_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Lemma 5.10 of Armstrong and Dario, identification of the limit** (every dimension
`d ≥ 2`): the limit of `ā_{□_n}⁻¹` is `ā⁻¹`. Unconditional form of
`cubeAhomInvLimit_eq_of_decay`. -/
theorem cubeAhomInvLimit_eq [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    cubeAhomInvLimit (d := d) p = (cubeAhom (d := d) p)⁻¹ := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact cubeAhomInvLimit_eq_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Proposition 5.2 of Armstrong and Dario, qualitative part** (every dimension `d ≥ 2`):
`lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q`. Unconditional form of `cubeMuLimit_eq_of_decay`. -/
theorem cubeMuLimit_eq [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (q : Fin d → ℝ) :
    cubeMuLimit p q = 1 / 2 * ∑ i, q i * ((cubeAhom (d := d) p)⁻¹ *ᵥ q) i := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact cubeMuLimit_eq_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59 q

/-- **Display (5.4) of Armstrong and Dario for `μ`, in expectation** (every dimension `d ≥ 2`).
Unconditional form of `exists_abs_cubeMuMean_sub_le_of_decay`. -/
theorem exists_abs_cubeMuMean_sub_le_pow [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ q : Fin d → ℝ,
      |cubeMuMean p n q - 1 / 2 * ∑ i, q i * ((cubeAhom (d := d) p)⁻¹ *ᵥ q) i| ≤
        K * (∑ i, q i ^ 2) * l ^ n := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_abs_cubeMuMean_sub_le_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Display (5.4) of Armstrong and Dario for `ν`, in expectation** (every dimension `d ≥ 2`).
Unconditional form of `exists_abs_cubeNuMean_sub_le_of_decay`. -/
theorem exists_abs_cubeNuMean_sub_le_pow [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ ξ : Fin d → ℝ,
      |cubeNuMean p n ξ - 1 / 2 * ∑ i, ξ i * (cubeAhom (d := d) p *ᵥ ξ) i| ≤
        K * (∑ i, ξ i ^ 2) * l ^ n := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_abs_cubeNuMean_sub_le_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Display (5.42) of Armstrong and Dario** (every dimension `d ≥ 2`), with an integrable
majorant of `ρ(□_n)`. Unconditional form of `exists_cubeRho_majorant_of_decay`. -/
theorem exists_cubeRho_majorant [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ∃ Φ : Configuration d → ℝ,
      Integrable Φ (latticeBondLaw d p) ∧
      (∀ᵐ ω ∂(latticeBondLaw d p), cubeRho p ω ⟨n, 0⟩ ≤ Φ ω) ∧
      ∫ ω, Φ ω ∂(latticeBondLaw d p) ≤ C * r ^ n := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeRho_majorant_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Lemma 5.11 of Armstrong and Dario, tail form** (every dimension `d ≥ 2`). Unconditional
form of `exists_cubeRho_tail_of_decay`. -/
theorem exists_cubeRho_tail [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
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
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeRho_tail_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Lemma 5.11 of Armstrong and Dario, `O_s` form** (every dimension `d ≥ 2`). Unconditional
form of `exists_cubeOmega_isOsBond_of_decay`. -/
theorem exists_cubeOmega_isOsBond [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube d,
      ∃ Z : Configuration d → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond d p Z (1 / (2 * (d : ℝ) - 1)) (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
        (∀ ω, cubeRho p ω V ≤ Z ω) ∧
        ∀ (ω : Configuration d) (q : Fin d → ℝ),
          |cubeOmega p ω V q| ≤ Z ω * ∑ i, q i ^ 2 := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeOmega_isOsBond_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **The `O_s` bound of `-μ` from Lemma 5.11** (every dimension `d ≥ 2`). Unconditional form of
`exists_neg_cubeMu_le_isOsBond_of_decay`. -/
theorem exists_neg_cubeMu_le_isOsBond [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ α C K : ℝ, 0 < α ∧ 0 < C ∧ 0 ≤ K ∧ ∀ V : TriadicCube d,
      ∃ Z : Configuration d → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond d p Z (1 / (2 * (d : ℝ) - 1)) (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
        ∀ (ω : Configuration d) (q : Fin d → ℝ),
          (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) ≤
            (K + Z ω) * ∑ i, q i ^ 2 := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_neg_cubeMu_le_isOsBond_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Proposition 5.2 of Armstrong and Dario, tail form** (every dimension `d ≥ 2`).
Unconditional form of `exists_cubeSubaddGood_tail_of_decay`. -/
theorem exists_cubeSubaddGood_tail [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K lam s c K' : ℝ, 0 ≤ K ∧ 0 < lam ∧ lam < 1 ∧ 0 < s ∧ s ≤ 1 ∧ 0 < c ∧ 0 ≤ K' ∧
      ∀ m : ℕ, latticeBondLaw d p {ω | ¬ CubeSubaddGood p ω ⟨m, 0⟩ K lam} ≤
        ENNReal.ofReal (K' * Real.exp (-c * ((3 : ℝ) ^ m) ^ s)) := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeSubaddGood_tail_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Proposition 5.2 of Armstrong and Dario, displays (5.2) and (5.3)** (every dimension
`d ≥ 2`). Unconditional form of `exists_cubeSubaddErr_isOsBond_of_decay`. -/
theorem exists_cubeSubaddErr_isOsBond [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube d,
      Measurable (cubeSubaddErr p V) ∧ (∀ ω, 0 ≤ cubeSubaddErr p V ω) ∧
      IsOsBond d p (cubeSubaddErr p V) (1 / (2 * (d : ℝ) - 1))
        (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
      ∀ (ω : Configuration d) (q : Fin d → ℝ),
        |cubeMuErr p ω V q| ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 ∧
        |cubeNuErr p ω V q| ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeSubaddErr_isOsBond_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

/-- **Definition 5.12 and Proposition 5.13 of Armstrong and Dario** (every dimension `d ≥ 2`).
Unconditional form of `exists_cubeBoundN_of_decay`. -/
theorem exists_cubeBoundN [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ K lam r θ : ℝ, 0 ≤ K ∧ 0 < lam ∧ lam < 1 ∧ 0 < r ∧ 0 < θ ∧
      ∃ N : Configuration d → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond d p N r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, N ω ≤ 3 ^ m →
          (∀ V : TriadicCube d, V.scale = (m + 3) / 4 →
            V.vertices ⊆ (⟨m, 0⟩ : TriadicCube d).vertices → CubeSubaddGood p ω V K lam) ∧
          ∀ z ∈ (⟨m, 0⟩ : TriadicCube d).vertices,
            CubeSubaddGood p (configurationTranslation (-z) ω) ⟨(m + 3) / 4, 0⟩ K lam := by
  obtain ⟨C₉, σ₉, ρ₉, N₉, hC, hσ, hσ1, hρ, hρ1, h59⟩ := exists_h59 hd hpc
  exact exists_cubeBoundN_of_decay hd hpc hC hσ hσ1 hρ hρ1 h59

end Rigidity.Percolation
