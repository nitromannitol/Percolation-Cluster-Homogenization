import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth
import PercolationClusterHomogenization.Proofs.Density.GreenGradientCore

/-!
# The density of the infinite cluster in balls, and stretched exponential moments

The statement `ClusterDensityInputFaithful` of the density of the infinite cluster in the balls of
the lattice above a minimal scale, the bound `X ≤ O_s(θ A^{1/s})` from `E[exp((X/θ ∨ 0)^s)] ≤ A`
(`isOsBond_of_integral_le`), the monotonicity and scaling rules of `IsOsBond`, and the restriction of
the normalized `L̲²` norm to a smaller ball.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation
open Rigidity.External (IsOsBond)

/-- **Density of the infinite cluster**, as printed at paper L508-511: there are `s, C, 𝔠 > 0`
and, for every vertex `x`, a minimal scale `M_dense(x) ≤ O_s(C)` such that for all
`r ≥ M_dense(x)` any (open Euclidean) ball of radius `r/100` containing the vertex `x` contains at
least `𝔠 r^d` vertices of `𝒞_∞`. The draft cites Penrose–Pisztora, Adv. Appl. Probab. 28 (1996),
Theorem 1, which concerns continuum percolation (their lattice theorems are for site percolation;
correction C35). For bond percolation in every `d ≥ 2` it follows from Dario–Gu,
arXiv:1909.10439v4, Proposition A.1 (`Rigidity.External.ClusterDensityConcentrationInput`), by a
union bound over triadic cubes: `clusterDensityInputFaithful_of_concentration`
(`ClusterDensityFromDarioGu.lean`). -/
def ClusterDensityInputFaithful : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C c : ℝ, 0 < s ∧ 0 < C ∧ 0 < c ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ r : ℝ, M ω ≤ r → ∀ y : EuclideanSpace ℝ (Fin d),
          dist (latticeEuclideanEmbedding x) y < r / 100 →
            c * r ^ d ≤
              ({z : uniqueInfiniteComponent h |
                dist (latticeEuclideanEmbedding z.val) y < r / 100}.ncard : ℝ)

/-- The density lower bound at a fixed dimension and bond parameter. -/
def ClusterDensityInputFaithfulAt (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s C c : ℝ, 0 < s ∧ 0 < C ∧ 0 < c ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ r : ℝ, M ω ≤ r → ∀ y : EuclideanSpace ℝ (Fin d),
          dist (latticeEuclideanEmbedding x) y < r / 100 →
            c * r ^ d ≤
              ({z : uniqueInfiniteComponent h |
                dist (latticeEuclideanEmbedding z.val) y < r / 100}.ncard : ℝ)

/-! ### The `O_s` calculus and the density input -/

section Density

variable {d : ℕ} {p : unitInterval}

/-- `E[exp((X/θ ∨ 0)^s)] ≤ A` with `A ≥ 1` gives `X ≤ O_s(θ A^{1/s})` (Bernoulli:
`y^{1/A} ≤ 1 + (y - 1)/A` for `y ≥ 0`). -/
theorem isOsBond_of_integral_le {X : Configuration d → ℝ} {s θ A : ℝ} (hs : 0 < s) (hA : 1 ≤ A)
    (hint : Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) (latticeBondLaw d p))
    (hle : (∫ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) ∂latticeBondLaw d p) ≤ A) :
    IsOsBond d p X s (θ * A ^ (1 / s)) := by
  have hAp : 0 < A := lt_of_lt_of_le one_pos hA
  have hB : 0 < A ^ (1 / s) := Real.rpow_pos_of_pos hAp _
  have hBs : (A ^ (1 / s)) ^ s = A := by
    rw [← Real.rpow_mul hAp.le, one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
  have hexp : ∀ ω, Real.exp (Real.rpow (max (X ω / (θ * A ^ (1 / s))) 0) s)
      = (Real.exp (Real.rpow (max (X ω / θ) 0) s)) ^ (1 / A) := by
    intro ω
    rw [← Real.exp_mul]
    congr 1
    have hm : max (X ω / θ / A ^ (1 / s)) 0 = max (X ω / θ) 0 / A ^ (1 / s) := by
      rw [← max_div_div_right hB.le, zero_div]
    rw [← div_div, hm]
    change (max (X ω / θ) 0 / A ^ (1 / s)) ^ s = Real.rpow (max (X ω / θ) 0) s * (1 / A)
    rw [Real.div_rpow (le_max_right _ _) hB.le, hBs]
    exact (mul_one_div _ _).symm
  have hA0 : (0 : ℝ) ≤ 1 / A := by positivity
  have hA1 : 1 / A ≤ 1 := by rw [div_le_one hAp]; exact hA
  have hbern : ∀ ω, Real.exp (Real.rpow (max (X ω / (θ * A ^ (1 / s))) 0) s) ≤
      1 + (1 / A) * (Real.exp (Real.rpow (max (X ω / θ) 0) s) - 1) := by
    intro ω
    rw [hexp]
    have h := rpow_one_add_le_one_add_mul_self
      (s := Real.exp (Real.rpow (max (X ω / θ) 0) s) - 1) (by
        have := Real.exp_pos (Real.rpow (max (X ω / θ) 0) s); linarith) hA0 hA1
    rwa [add_sub_cancel] at h
  have hpos : ∀ ω, 0 < Real.exp (Real.rpow (max (X ω / (θ * A ^ (1 / s))) 0) s) :=
    fun ω => Real.exp_pos _
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun ω => Real.exp (Real.rpow (max (X ω / (θ * A ^ (1 / s))) 0) s))
      (latticeBondLaw d p) := by
    have h := (Real.continuous_rpow_const hA0).comp_aestronglyMeasurable hint.aestronglyMeasurable
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (hexp ω).symm
  have hint2 : Integrable (fun ω => Real.exp (Real.rpow (max (X ω / (θ * A ^ (1 / s))) 0) s))
      (latticeBondLaw d p) := by
    refine Integrable.mono' hint hmeas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hpos ω).le]
    rw [hexp ω]
    calc (Real.exp (Real.rpow (max (X ω / θ) 0) s)) ^ (1 / A)
        ≤ (Real.exp (Real.rpow (max (X ω / θ) 0) s)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (Real.rpow_nonneg (le_max_right _ _) _))
            hA1
      _ = _ := Real.rpow_one _
  refine ⟨hint2, ?_⟩
  have hrhs : Integrable (fun ω => 1 + (1 / A) * (Real.exp (Real.rpow (max (X ω / θ) 0) s) - 1))
      (latticeBondLaw d p) :=
    (integrable_const (1 : ℝ)).add ((hint.sub (integrable_const (1 : ℝ))).const_mul _)
  calc (∫ ω, Real.exp (Real.rpow (max (X ω / (θ * A ^ (1 / s))) 0) s) ∂latticeBondLaw d p)
      ≤ ∫ ω, (1 + (1 / A) * (Real.exp (Real.rpow (max (X ω / θ) 0) s) - 1)) ∂latticeBondLaw d p :=
        integral_mono hint2 hrhs hbern
    _ = 1 + (1 / A) * ((∫ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) ∂latticeBondLaw d p) - 1) := by
        have h1 : Integrable (fun ω => (1 / A) * (Real.exp (Real.rpow (max (X ω / θ) 0) s) - 1))
            (latticeBondLaw d p) := (hint.sub (integrable_const (1 : ℝ))).const_mul _
        rw [integral_add (integrable_const _) h1, integral_const_mul,
          integral_sub hint (integrable_const _)]
        simp
    _ ≤ 1 + (1 / A) * (A - 1) := by gcongr
    _ ≤ 2 := by
        have : (1 / A) * (A - 1) = 1 - 1 / A := by field_simp
        rw [this]; linarith

theorem max_div_div_le_of_le {x θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    max (x / θ') 0 ≤ max (x / θ) 0 := by
  have hθ' : 0 < θ' := lt_of_lt_of_le hθ hθθ'
  refine max_le ?_ (le_max_right _ _)
  rcases le_or_gt 0 x with hx | hx
  · exact (div_le_div_of_nonneg_left hx hθ hθθ').trans (le_max_left _ _)
  · exact (div_nonpos_of_nonpos_of_nonneg hx.le hθ'.le).trans (le_max_right _ _)

theorem exp_rpow_max_div_mono {x θ θ' s : ℝ} (hs : 0 < s) (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    Real.exp (Real.rpow (max (x / θ') 0) s) ≤ Real.exp (Real.rpow (max (x / θ) 0) s) :=
  Real.exp_le_exp.mpr (Real.rpow_le_rpow (le_max_right _ _) (max_div_div_le_of_le hθ hθθ') hs.le)

theorem measurable_exp_rpow_max_div {X : Configuration d → ℝ} {θ : ℝ} (s : ℝ)
    (hX : Measurable X) :
    Measurable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) := by
  have h : Measurable (fun ω => max (X ω / θ) 0) := (hX.div_const θ).max measurable_const
  exact (h.pow_const s).exp

theorem IsOsBond.mono_scale {X : Configuration d → ℝ} {s θ θ' : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hθθ' : θ ≤ θ') (hX : Measurable X) (h : IsOsBond d p X s θ) : IsOsBond d p X s θ' := by
  obtain ⟨hi, hb⟩ := h
  have hmono : ∀ ω, Real.exp (Real.rpow (max (X ω / θ') 0) s) ≤
      Real.exp (Real.rpow (max (X ω / θ) 0) s) := fun ω => exp_rpow_max_div_mono hs hθ hθθ'
  have hi' : Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ') 0) s))
      (latticeBondLaw d p) := by
    refine Integrable.mono' hi (measurable_exp_rpow_max_div s hX).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hmono ω
  exact ⟨hi', (integral_mono hi' hi hmono).trans hb⟩

theorem IsOsBond.const_mul {X : Configuration d → ℝ} {s θ c : ℝ} (hc : 0 < c)
    (h : IsOsBond d p X s θ) : IsOsBond d p (fun ω => c * X ω) s (c * θ) := by
  have e : ∀ ω, (c * X ω) / (c * θ) = X ω / θ := fun ω => mul_div_mul_left _ _ hc.ne'
  unfold IsOsBond
  simp only [e]
  exact h

theorem IsOsBond.max {X Y : Configuration d → ℝ} {s θ θ' : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hθ' : 0 < θ') (hX : Measurable X) (hY : Measurable Y) (h : IsOsBond d p X s θ)
    (h' : IsOsBond d p Y s θ') :
    IsOsBond d p (fun ω => max (X ω) (Y ω)) s (max θ θ' * 4 ^ (1 / s)) := by
  obtain ⟨hi, hb⟩ := h
  obtain ⟨hi', hb'⟩ := h'
  have hpt : ∀ ω, Real.exp (Real.rpow (Max.max (Max.max (X ω) (Y ω) / Max.max θ θ') 0) s) ≤
      Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) + Real.exp (Real.rpow (Max.max (Y ω / θ') 0) s) := by
    intro ω
    rcases max_choice (X ω) (Y ω) with hm | hm
    · rw [hm]
      exact (exp_rpow_max_div_mono hs hθ (le_max_left θ θ')).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [hm]
      exact (exp_rpow_max_div_mono hs hθ' (le_max_right θ θ')).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hmeas : Measurable (fun ω => Real.exp (Real.rpow (Max.max (Max.max (X ω) (Y ω) / Max.max θ θ') 0) s)) :=
    measurable_exp_rpow_max_div (X := fun ω => Max.max (X ω) (Y ω)) s (hX.max hY)
  have hsum : Integrable (fun ω => Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) +
      Real.exp (Real.rpow (Max.max (Y ω / θ') 0) s)) (latticeBondLaw d p) := hi.add hi'
  have hi2 : Integrable (fun ω => Real.exp (Real.rpow (Max.max (Max.max (X ω) (Y ω) / Max.max θ θ') 0) s))
      (latticeBondLaw d p) := by
    refine Integrable.mono' hsum hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hpt ω
  refine isOsBond_of_integral_le hs (by norm_num) hi2 ?_
  calc (∫ ω, Real.exp (Real.rpow (Max.max (Max.max (X ω) (Y ω) / Max.max θ θ') 0) s) ∂latticeBondLaw d p)
      ≤ ∫ ω, (Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) +
          Real.exp (Real.rpow (Max.max (Y ω / θ') 0) s)) ∂latticeBondLaw d p :=
        integral_mono hi2 hsum hpt
    _ = (∫ ω, Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) ∂latticeBondLaw d p) +
          ∫ ω, Real.exp (Real.rpow (Max.max (Y ω / θ') 0) s) ∂latticeBondLaw d p :=
        integral_add hi hi'
    _ ≤ 4 := by linarith

theorem IsOsBond.mono_exponent {X : Configuration d → ℝ} {s s' θ : ℝ} (hs' : 0 < s')
    (hss' : s' ≤ s) (hX : Measurable X) (h : IsOsBond d p X s θ) :
    IsOsBond d p X s' (θ * 6 ^ (1 / s')) := by
  obtain ⟨hi, hb⟩ := h
  have hpt : ∀ ω, Real.exp (Real.rpow (Max.max (X ω / θ) 0) s') ≤
      3 * Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) := by
    intro ω
    set t := Max.max (X ω / θ) 0 with ht
    have ht0 : 0 ≤ t := le_max_right _ _
    have hts : 0 ≤ t ^ s := Real.rpow_nonneg ht0 s
    have h1 : Real.rpow t s' ≤ 1 + Real.rpow t s := by
      rcases le_or_gt t 1 with h1 | h1
      · have := Real.rpow_le_one ht0 h1 hs'.le
        change t ^ s' ≤ 1 + t ^ s
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le h1.le hss'
        change t ^ s' ≤ 1 + t ^ s
        linarith
    calc Real.exp (Real.rpow t s') ≤ Real.exp (1 + Real.rpow t s) := Real.exp_le_exp.mpr h1
      _ = Real.exp 1 * Real.exp (Real.rpow t s) := Real.exp_add _ _
      _ ≤ 3 * Real.exp (Real.rpow t s) :=
          mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
  have hmeas := measurable_exp_rpow_max_div (X := X) (θ := θ) s' hX
  have hi3 : Integrable (fun ω => 3 * Real.exp (Real.rpow (Max.max (X ω / θ) 0) s))
      (latticeBondLaw d p) := hi.const_mul 3
  have hi2 : Integrable (fun ω => Real.exp (Real.rpow (Max.max (X ω / θ) 0) s'))
      (latticeBondLaw d p) := by
    refine Integrable.mono' hi3 hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hpt ω
  refine isOsBond_of_integral_le hs' (by norm_num) hi2 ?_
  calc (∫ ω, Real.exp (Real.rpow (Max.max (X ω / θ) 0) s') ∂latticeBondLaw d p)
      ≤ ∫ ω, 3 * Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) ∂latticeBondLaw d p :=
        integral_mono hi2 hi3 hpt
    _ = 3 * ∫ ω, Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) ∂latticeBondLaw d p :=
        integral_const_mul _ _
    _ ≤ 6 := by linarith

theorem isOsBond_const {κ s : ℝ} (hκ : 0 < κ) (hs : 0 < s) :
    IsOsBond d p (fun _ => κ) s (κ * 3 ^ (1 / s)) := by
  have h1 : κ / κ = 1 := div_self hκ.ne'
  refine isOsBond_of_integral_le hs (by norm_num) ?_ ?_
  · simp only [h1]
    simp
  · simp only [h1]
    simp
    exact Real.exp_one_lt_three.le

end Density

/-! ### Large-scale regularity: from the printed form to the proposed form -/

section Regularity

variable {d : ℕ}

/-- Restriction from a larger ball. -/
theorem componentBallL2_le_sqrt_card_div_mul {ω : Configuration d} (C : OpenComponent ω)
    (x : Vertex d) {ρ σ : ℝ} (hρσ : ρ ≤ σ) (hpos : 0 < (componentEuclideanBall C x ρ).card)
    (f : C → ℝ) :
    componentBallL2 C x ρ f ≤
      Real.sqrt (((componentEuclideanBall C x σ).card : ℝ) /
        ((componentEuclideanBall C x ρ).card : ℝ)) * componentBallL2 C x σ f := by
  unfold componentBallL2
  have hsub := componentEuclideanBall_mono C x hρσ
  have hNρ : (0 : ℝ) < (componentEuclideanBall C x ρ).card := by exact_mod_cast hpos
  have hNσ : (0 : ℝ) < (componentEuclideanBall C x σ).card := by
    exact_mod_cast hpos.trans_le (Finset.card_le_card hsub)
  rw [← Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hNρ.le)]
  apply Real.sqrt_le_sqrt
  rw [div_mul_div_comm, mul_comm ((componentEuclideanBall C x σ).card : ℝ),
    mul_div_mul_right _ _ hNσ.ne']
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => sq_nonneg _)) hNρ.le

end Regularity

end Rigidity.Proofs.S2
