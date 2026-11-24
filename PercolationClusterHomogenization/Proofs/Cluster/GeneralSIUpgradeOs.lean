import PercolationClusterHomogenization.Proofs.Cluster.GeneralSubaddOs

/-!
# Lemma 5.11 of Armstrong and Dario in every dimension, in the form `O_s`

`ω(V, q) = ν(V, ā⁻¹ q) - μ(V, q) - q · ā⁻¹ q` is the difference of the two error forms of
Proposition 5.2, `ω(V, q) = f_ν(q) - f_μ(q)` (`cubeOmega_eq_sub`), so
`sup_q |q|⁻² |ω(V, q)| ≤ 2 X(V) ≤ O_r(C 3^{-α scale V})`
(`exists_cubeOmega_isOsBond_of_decay`, Lemma 5.11 of the source, given the bound of Lemma 5.9,
with `r = 1/(2d - 1)`). The source proves Lemma 5.11 first and derives Proposition 5.2 from it; here, as in
dimension two, the order is reversed, both coming from the tail bounds of
`GeneralSubaddTailMain.lean`. The upper bound (4.17) of `-μ` in the form `O_s` follows
(`exists_neg_cubeMu_le_isOsBond_of_decay`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- `ω(V, q) = f_ν(q) - f_μ(q)`. -/
theorem cubeOmega_eq_sub (p : unitInterval) (ω : Configuration d) (V : TriadicCube d)
    (q : Fin d → ℝ) : cubeOmega p ω V q = cubeNuErr p ω V q - cubeMuErr p ω V q := by
  unfold cubeOmega cubeNuErr cubeMuErr
  split_ifs <;> ring

/-- **Armstrong and Dario, Lemma 5.11** (every `d ≥ 2`, `p > p_c(d)`), given the bound of
Lemma 5.9: `sup_q |q|⁻² |ω(V, q)| ≤ O_r(C 3^{-α scale V})` for every triadic cube `V`, with
`r = 1/(2d - 1)` and a measurable majorant `Z(V)`, which also bounds `ρ(V)`. -/
theorem exists_cubeOmega_isOsBond_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube d,
      ∃ Z : Configuration d → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond d p Z (1 / (2 * (d : ℝ) - 1)) (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
        (∀ ω, cubeRho p ω V ≤ Z ω) ∧
        ∀ (ω : Configuration d) (q : Fin d → ℝ),
          |cubeOmega p ω V q| ≤ Z ω * ∑ i, q i ^ 2 := by
  obtain ⟨α, C, hα, hC, hV⟩ :=
    exists_cubeSubaddErr_isOsBond_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  refine ⟨α, 2 * C, hα, by positivity, fun V => ?_⟩
  obtain ⟨hm, h0, hos, hb⟩ := hV V
  have hω : ∀ (ω : Configuration d) (q : Fin d → ℝ),
      |cubeOmega p ω V q| ≤ 2 * cubeSubaddErr p V ω * ∑ i, q i ^ 2 := fun ω q => by
    obtain ⟨hμ, hν⟩ := hb ω q
    rw [cubeOmega_eq_sub]
    have h1 := abs_sub (cubeNuErr p ω V q) (cubeMuErr p ω V q)
    linarith
  refine ⟨fun ω => 2 * cubeSubaddErr p V ω, hm.const_mul _,
    fun ω => mul_nonneg zero_le_two (h0 ω), ?_, fun ω => ?_, hω⟩
  · have := Rigidity.Proofs.S2.IsOsBond.const_mul (by norm_num : (0 : ℝ) < 2) hos
    simpa only [mul_assoc] using this
  · exact cubeRho_le_of_forall (mul_nonneg zero_le_two (h0 ω)) fun q =>
      (max_le (le_abs_self _) (abs_nonneg _)).trans (hω ω q)

/-- **The upper bound (4.17) of `-μ`, in the form `O_s`** (Armstrong and Dario,
`e.muupboundwhip`, every `d ≥ 2`, given the bound of Lemma 5.9, with the rate `size^{-α}` of
Proposition 5.2 in place of `size^{-1}`): `-μ(V, q) ≤ (K + Z(V)) |q|²` with
`Z(V) ≤ O_r(C 3^{-α scale V})`, `r = 1/(2d - 1)` (at least the exponent `1/(2d + 1)` of the
source), `μ` set to `0` off the event. -/
theorem exists_neg_cubeMu_le_isOsBond_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ α C K : ℝ, 0 < α ∧ 0 < C ∧ 0 ≤ K ∧ ∀ V : TriadicCube d,
      ∃ Z : Configuration d → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond d p Z (1 / (2 * (d : ℝ) - 1)) (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
        ∀ (ω : Configuration d) (q : Fin d → ℝ),
          (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) ≤
            (K + Z ω) * ∑ i, q i ^ 2 := by
  obtain ⟨α, C, hα, hC, hV⟩ :=
    exists_cubeSubaddErr_isOsBond_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  set g : (Fin d → ℝ) → ℝ := fun x => 1 / 2 * ∑ i, x i * ((cubeAhom (d := d) p)⁻¹ *ᵥ x) i
    with hg
  have hgq : IsSlopeQuadratic g :=
    (isSlopeQuadratic_dotProduct_mulVec (cubeAhom (d := d) p)⁻¹).const_mul (1 / 2)
  refine ⟨α, C, ∑ i, ∑ j, |slopeMatrix g i j|, hα, hC, by positivity, fun V => ?_⟩
  obtain ⟨hm, h0, hos, hb⟩ := hV V
  refine ⟨cubeSubaddErr p V, hm, h0, hos, fun ω q => ?_⟩
  have hμ := (hb ω q).1
  have hdot := hgq.abs_le q
  have e : (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0) =
      -(if PartitionEvent ω ∧ PartitionResolved ω V then cubeMu ω V q else 0) := by
    split_ifs <;> simp
  rw [e]
  unfold cubeMuErr at hμ
  set I := if PartitionEvent ω ∧ PartitionResolved ω V then cubeMu ω V q else 0 with hI
  have h1 : -(I + g q) ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 := (neg_le_abs _).trans hμ
  have h2 := le_abs_self (g q)
  calc -I ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 + g q := by linarith
    _ ≤ cubeSubaddErr p V ω * ∑ i, q i ^ 2 +
        (∑ i, ∑ j, |slopeMatrix g i j|) * ∑ i, q i ^ 2 := by linarith
    _ = _ := by ring

end Rigidity.Percolation
