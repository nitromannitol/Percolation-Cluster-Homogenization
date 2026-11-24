import LatticeProb.External.GreenQuantitative
import LatticeProb.Prob.Percolation.ContinuumGreen
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeClusterL2
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import PercolationClusterHomogenization.External.CorrectorQuantitative

/-!
# The normalized `L²` norm on the balls of a component

The triangle inequality and the symmetry of the normalized `L̲²` norm on the balls of a component,
the bound by a bound of the absolute value, and the count `5^d r^d` of the vertices of a component
in a Euclidean ball of radius `r ≥ 1`.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-! ### The normalized `L̲²` norm on a component ball -/

/-- The triangle inequality for the normalized `L̲²` norm on a component ball. -/
theorem componentBallL2_add_le (C : OpenComponent ω) (x : Vertex d) (r : ℝ) (f h : C → ℝ) :
    componentBallL2 C x r (fun z => f z + h z) ≤
      componentBallL2 C x r f + componentBallL2 C x r h := by
  unfold componentBallL2
  set s := componentEuclideanBall C x r
  have hN : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_div' _ hN, Real.sqrt_div' _ hN, Real.sqrt_div' _ hN, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hB : 0 ≤ ∑ z ∈ s, f z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  have hH : 0 ≤ ∑ z ∈ s, h z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s f h
  have hexp : ∑ z ∈ s, (f z + h z) ^ 2 =
      ∑ z ∈ s, f z ^ 2 + 2 * ∑ z ∈ s, f z * h z + ∑ z ∈ s, h z ^ 2 := by
    have : ∀ z, (f z + h z) ^ 2 = f z ^ 2 + 2 * (f z * h z) + h z ^ 2 := fun z => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg (∑ z ∈ s, f z ^ 2))
    (Real.sqrt_nonneg (∑ z ∈ s, h z ^ 2)))]
  apply Real.sqrt_le_sqrt
  rw [hexp, add_sq, Real.sq_sqrt hB, Real.sq_sqrt hH]
  nlinarith

/-- The normalized `L̲²` norm on a component ball is at most a bound of `|h|` on the ball. -/
theorem componentBallL2_le_of_abs_le (C : OpenComponent ω) (x : Vertex d) (r : ℝ) (h : C → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hh : ∀ z ∈ componentEuclideanBall C x r, |h z| ≤ M) :
    componentBallL2 C x r h ≤ M := by
  unfold componentBallL2
  rw [← Real.sqrt_sq hM]
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos (componentEuclideanBall C x r).card with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]
    positivity
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    calc ∑ z ∈ componentEuclideanBall C x r, h z ^ 2
        ≤ ∑ _z ∈ componentEuclideanBall C x r, M ^ 2 :=
          Finset.sum_le_sum fun z hz => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hh z hz) 2
      _ = M ^ 2 * (componentEuclideanBall C x r).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The normalized `L̲²` norm is even. -/
theorem componentBallL2_neg (C : OpenComponent ω) (x : Vertex d) (r : ℝ) (f : C → ℝ) :
    componentBallL2 C x r (fun z => -f z) = componentBallL2 C x r f := by
  simp only [componentBallL2, neg_sq]

/-- The number of vertices of a component in the Euclidean ball `B_r(x)`, `r ≥ 1`, is at most
`5^d r^d`. -/
theorem card_componentEuclideanBall_le (C : OpenComponent ω) (x : Vertex d) {r : ℝ}
    (hr : 1 ≤ r) : ((componentEuclideanBall C x r).card : ℝ) ≤ 5 ^ d * r ^ d := by
  classical
  set box : Finset (Vertex d) :=
    Fintype.piFinset fun i => Finset.Icc (x i - ⌈r⌉) (x i + ⌈r⌉) with hbox
  have hsub : (componentEuclideanBall C x r).map (Function.Embedding.subtype _) ⊆ box := by
    intro w hw
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [mem_componentEuclideanBall] at ha
    rw [hbox, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi := PiLp.norm_apply_le
      (latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x) i
    change |(a.val i : ℝ) - (x i : ℝ)| ≤
      ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ at hi
    rw [← dist_eq_norm] at hi
    have hb : |(a.val i : ℝ) - (x i : ℝ)| ≤ (⌈r⌉ : ℝ) :=
      (hi.trans ha.le).trans (Int.le_ceil r)
    obtain ⟨hl, hu⟩ := abs_le.mp hb
    constructor
    · exact_mod_cast (by linarith : (x i : ℝ) - (⌈r⌉ : ℝ) ≤ (a.val i : ℝ))
    · exact_mod_cast (by linarith : (a.val i : ℝ) ≤ (x i : ℝ) + (⌈r⌉ : ℝ))
  have hcard : (componentEuclideanBall C x r).card ≤ box.card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    exact Finset.card_le_card hsub
  have hceil0 : (0 : ℤ) ≤ 2 * ⌈r⌉ + 1 := by
    have : (0 : ℤ) ≤ ⌈r⌉ := Int.ceil_nonneg (by linarith)
    omega
  have hboxcard : box.card = (2 * ⌈r⌉ + 1).toNat ^ d := by
    rw [hbox, Fintype.card_piFinset]
    rw [Finset.prod_congr rfl (g := fun _ => (2 * ⌈r⌉ + 1).toNat) (fun i _ => by
      rw [Int.card_Icc]; congr 1; ring)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcast : (((2 * ⌈r⌉ + 1).toNat : ℕ) : ℝ) = 2 * (⌈r⌉ : ℝ) + 1 := by
    have : (((2 * ⌈r⌉ + 1).toNat : ℕ) : ℤ) = 2 * ⌈r⌉ + 1 := Int.toNat_of_nonneg hceil0
    exact_mod_cast this
  have hle : 2 * (⌈r⌉ : ℝ) + 1 ≤ 5 * r := by
    have := Int.ceil_lt_add_one r
    linarith
  calc ((componentEuclideanBall C x r).card : ℝ) ≤ (box.card : ℝ) := by exact_mod_cast hcard
    _ = (2 * (⌈r⌉ : ℝ) + 1) ^ d := by rw [hboxcard, Nat.cast_pow, hcast]
    _ ≤ (5 * r) ^ d := pow_le_pow_left₀ (by positivity) hle d
    _ = 5 ^ d * r ^ d := mul_pow _ _ _

/-! ### Affine majorization -/

end Rigidity.Proofs.S2
