import PercolationClusterHomogenization.Proofs.Regularity.GeneralLatticeCubic
import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicExcessThree

/-!
# Excess decay of order three of lattice harmonic functions on `ℤᵈ`

For `F` harmonic on `B_r(z)` and a lattice harmonic cubic polynomial `w`
(`latticeHarmonicCubicPoly d`), `f = F - w` is harmonic and its fourth forward differences are
bounded on `Q_m(z)` by `m^{-d/2 - 4}` times its `ℓ²` norm on `B_r(z)` (`sq_fwd4_le`). The
harmonic third-order expansion of `f` at a corner `c` (`latticeHarmonicTaylorThree f c`) is the
cubic part `tensorCubicPart` of the third differences `t` of `f` at `c`, with the trace removed by
`corrTensor`, plus the harmonic second-order expansion (`abs_sub_harmonicTaylor_two_le`) of the
remainder `f - tensorCubicPart t c`, whose third differences move by fourth differences of `f`
from their value `0` at `c`. The trace of `t` is a sum of fourth differences (`sum_hessAt_eq`
applied to the first differences of `f`), so the expansion is a lattice harmonic cubic polynomial
within `taylorThreeConst d · S⁴ M₄` of `f` on the box `[c, c + S 𝟙]`
(`abs_sub_latticeHarmonicTaylorThree_le`). This gives the excess decay of order three,
`HarmonicRegularity` with `j = 3` for the class `latticeHarmonicClass z` and `Ā_3`
(`harmonicRegularity_cubicPoly_latticeHarmonicClass`). This is the planar argument of
`harmonicRegularity_three_latticeHarmonicClass` in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-! ### The harmonic third-order expansion -/

/-- The third forward differences `D_a D_b D_e f(c)`. -/
def latticeTaylorTensor (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) : Fin d → Fin d → Fin d → ℝ :=
  fun a b e => fwd a (fwd b (fwd e f)) c

theorem isSymmTensor_latticeTaylorTensor (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) :
    IsSymmTensor (latticeTaylorTensor f c) := by
  intro i j k
  simp only [latticeTaylorTensor]
  exact ⟨by rw [fwd_comm i j], by rw [fwd_comm j k]⟩

/-- The remainder `f - tensorCubicPart (latticeTaylorTensor f c) c`. -/
noncomputable def latticeTaylorRest (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) (y : Fin d → ℤ) : ℝ :=
  f y - tensorCubicPart (latticeTaylorTensor f c) c y

/-- The third differences of the remainder move from `0` at `c` as those of `f`. -/
theorem fwd_fwd_fwd_latticeTaylorRest (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) (a b e : Fin d)
    (y : Fin d → ℤ) :
    fwd e (fwd a (fwd b (latticeTaylorRest f c))) y =
      fwd e (fwd a (fwd b f)) y - fwd e (fwd a (fwd b f)) c := by
  have hs := isSymmTensor_latticeTaylorTensor f c
  show fwd e (fwd a (fwd b (fun y => f y - tensorCubicPart (latticeTaylorTensor f c) c y))) y = _
  rw [fwd_sub, fwd_sub, fwd_sub]
  show fwd e (fwd a (fwd b f)) y -
    fwd e (fwd a (fwd b (tensorCubicPart (latticeTaylorTensor f c) c))) y = _
  rw [fwd_fwd_fwd_tensorCubicPart hs, (hs b a e).1, (hs a b e).2, (hs a e b).1]
  rfl

/-- The harmonic second-order expansion at `c` of `abs_sub_harmonicTaylor_two_le`. -/
noncomputable def latticeHarmonicTaylorTwo (g : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) (y : Fin d → ℤ) :
    ℝ :=
  halfQuad (harmHess g c) c y + (g c - halfQuad (hessAt g c) c c) +
    ∑ i, ((y i - c i : ℤ) : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c

/-- The harmonic second-order expansion is a lattice harmonic quadratic function. -/
theorem mem_latticeHarmonicQuadratic_latticeHarmonicTaylorTwo [NeZero d]
    (g : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) :
    (fun x : latticeComponent d => latticeHarmonicTaylorTwo g c x.val) ∈
      latticeHarmonicQuadratic d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hQ : (fun x : latticeComponent d => halfQuad (harmHess g c) c x.val) ∈
      latticeHarmonicQuadratic d :=
    ⟨halfQuad_mem_clusterQuadratic (harmHess g c) c,
      fun y => latticeLaplacian_halfQuad_harmHess hd g c y⟩
  set q : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 fun i => fwd i (fun y => g y - halfQuad (hessAt g c) c y) c with hq
  set α := (g c - halfQuad (hessAt g c) c c) -
    ∑ i, (c i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c with hα
  have hA : (fun x : latticeComponent d => α + inner ℝ q (latticeEuclideanEmbedding x.val)) ∈
      latticeHarmonicQuadratic d :=
    clusterAffine_le_latticeHarmonicQuadratic ⟨α, q, fun _ => rfl⟩
  convert (latticeHarmonicQuadratic d).add_mem hQ hA using 1
  funext x
  have hinner : inner ℝ q (latticeEuclideanEmbedding x.val) =
      ∑ i, (x.val i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c := by
    rw [inner_eq_sum]
    exact sum_congr rfl fun i _ => mul_comm _ _
  have hsplit : ∑ i, ((x.val i - c i : ℤ) : ℝ) *
      fwd i (fun y => g y - halfQuad (hessAt g c) c y) c =
      ∑ i, (x.val i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c -
        ∑ i, (c i : ℝ) * fwd i (fun y => g y - halfQuad (hessAt g c) c y) c := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by push_cast; ring
  show latticeHarmonicTaylorTwo g c x.val = halfQuad (harmHess g c) c x.val +
    (α + inner ℝ q (latticeEuclideanEmbedding x.val))
  rw [latticeHarmonicTaylorTwo, hinner, hα, hsplit]
  ring

/-- The tensor of the harmonic third-order expansion: the third differences with the trace
removed. -/
noncomputable def latticeHarmonicTensor (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) :
    Fin d → Fin d → Fin d → ℝ :=
  latticeTaylorTensor f c - corrTensor (tensorTrace (latticeTaylorTensor f c))

theorem isSymmTensor_latticeHarmonicTensor (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) :
    IsSymmTensor (latticeHarmonicTensor f c) :=
  isSymmTensor_sub (isSymmTensor_latticeTaylorTensor f c) (isSymmTensor_corrTensor _)

theorem tensorTrace_latticeHarmonicTensor (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) (k : Fin d) :
    tensorTrace (latticeHarmonicTensor f c) k = 0 := by
  rw [latticeHarmonicTensor, tensorTrace_sub, tensorTrace_corrTensor, sub_self]

/-- **The harmonic third-order expansion** of `f` at `c`. -/
noncomputable def latticeHarmonicTaylorThree (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ)
    (y : Fin d → ℤ) : ℝ :=
  tensorCubicPart (latticeHarmonicTensor f c) c y +
    latticeHarmonicTaylorTwo (latticeTaylorRest f c) c y

/-- **The harmonic third-order expansion is a lattice harmonic cubic polynomial.** -/
theorem mem_latticeHarmonicCubicPoly_latticeHarmonicTaylorThree [NeZero d]
    (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) :
    (fun x : latticeComponent d => latticeHarmonicTaylorThree f c x.val) ∈
      latticeHarmonicCubicPoly d :=
  (latticeHarmonicCubicPoly d).add_mem
    (tensorCubicPart_mem_latticeHarmonicCubicPoly (isSymmTensor_latticeHarmonicTensor f c)
      (tensorTrace_latticeHarmonicTensor f c) c)
    (latticeHarmonicQuadratic_le_latticeHarmonicCubicPoly
      (mem_latticeHarmonicQuadratic_latticeHarmonicTaylorTwo _ c))

/-- The constant of the harmonic third-order expansion. -/
noncomputable def taylorThreeConst (d : ℕ) : ℝ :=
  d * (d + 1) * d * d + d * d + d ^ 4

theorem taylorThreeConst_nonneg (d : ℕ) : 0 ≤ taylorThreeConst d := by
  unfold taylorThreeConst; positivity

/-- **Harmonic third-order expansion on `ℤᵈ`**: if `f` is harmonic at `c` and at the `c + eₖ` and
its fourth forward differences are bounded by `M₄` on the box `[c - 𝟙, x]`, `x - c ≤ S 𝟙`, then
`|f(x) - latticeHarmonicTaylorThree f c x| ≤ taylorThreeConst d · S⁴ M₄`. -/
theorem abs_sub_latticeHarmonicTaylorThree_le (hd : 0 < d) (f : (Fin d → ℤ) → ℝ)
    {c x : Fin d → ℤ} (hcx : ∀ i, c i ≤ x i) {S : ℕ} (hS : 1 ≤ S) (hs : ∀ i, x i - c i ≤ S)
    {M₄ : ℝ} (hM₀ : 0 ≤ M₄)
    (hM : ∀ y : Fin d → ℤ, (∀ i, c i - 1 ≤ y i ∧ y i ≤ x i) →
      ∀ a b e g, |fwd g (fwd e (fwd a (fwd b f))) y| ≤ M₄)
    (hΔ : latticeLaplacian f c = 0) (hΔk : ∀ k, latticeLaplacian f (c + unit k) = 0) :
    |f x - latticeHarmonicTaylorThree f c x| ≤ taylorThreeConst d * S ^ 4 * M₄ := by
  set g : (Fin d → ℤ) → ℝ := latticeTaylorRest f c with hg
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by linarith
  set M₃ := (d : ℝ) * S * M₄ with hM₃
  have hM₃0 : 0 ≤ M₃ := by positivity
  have hM₄M₃ : M₄ ≤ M₃ := by
    rw [hM₃]
    have : (1 : ℝ) ≤ d * S := by nlinarith
    nlinarith
  -- third differences of the remainder on the box `[c, x]`
  have hMg : ∀ y : Fin d → ℤ, (∀ i, c i ≤ y i ∧ y i ≤ x i) →
      ∀ a b e, |fwd e (fwd a (fwd b g)) y| ≤ M₃ := by
    intro y hy a b e
    rw [hg, fwd_fwd_fwd_latticeTaylorRest]
    have hcy : ∀ i, c i ≤ y i := fun i => (hy i).1
    have hsy : ∀ i, y i - c i ≤ S := fun i => by have := hs i; have := (hy i).2; omega
    have h := abs_cornerPoint_sub_le (fwd e (fwd a (fwd b f))) hcy hsy hM₀
      (fun y' hy' i => hM y' (fun j => ⟨by have := (hy' j).1; omega,
        by have := (hy' j).2; have := (hy j).2; omega⟩) a b e i) univ
    rw [cornerPoint_univ, card_univ, Fintype.card_fin] at h
    exact h
  -- the points `c - eₐ`
  have hbox0 : ∀ a : Fin d, ∀ i, c i - 1 ≤ (c - unit a) i ∧ (c - unit a) i ≤ x i := by
    intro a i
    have hci := hcx i
    by_cases hia : i = a
    · subst hia
      simp only [unit, Pi.sub_apply, Pi.single_eq_same]
      omega
    · simp only [unit, Pi.sub_apply, Pi.single_eq_of_ne hia]
      omega
  -- the third differences of the remainder at `c - eₐ`
  have hMc : ∀ a, |fwd a (fwd a (fwd a g)) (c - unit a)| ≤ M₃ := by
    intro a
    rw [hg, fwd_fwd_fwd_latticeTaylorRest]
    have e1 : fwd a (fwd a (fwd a f)) (c - unit a) - fwd a (fwd a (fwd a f)) c =
        -fwd a (fwd a (fwd a (fwd a f))) (c - unit a) := by
      simp only [fwd, sub_add_cancel]; ring
    rw [e1, abs_neg]
    exact (hM (c - unit a) (hbox0 a) a a a a).trans hM₄M₃
  -- the remainder is harmonic at `c`
  have hΔg : latticeLaplacian g c = 0 := by
    show latticeLaplacian (fun y => f y - tensorCubicPart (latticeTaylorTensor f c) c y) c = 0
    rw [latticeLaplacian_sub, hΔ,
      latticeLaplacian_tensorCubicPart (isSymmTensor_latticeTaylorTensor f c)]
    simp
  have h2 := abs_sub_harmonicTaylor_two_le hd g hcx hs hM₃0 hMg hMc hΔg
  -- the trace of the third differences is a sum of fourth differences
  have hσ : ∀ k, |tensorTrace (latticeTaylorTensor f c) k| ≤ d * M₄ := by
    intro k
    have hΔ' : latticeLaplacian (fwd k f) c = 0 := by
      rw [latticeLaplacian_fwd, hΔk k, hΔ, sub_zero]
    have h := sum_hessAt_eq (fwd k f) c hΔ'
    have e : tensorTrace (latticeTaylorTensor f c) k = ∑ a, hessAt (fwd k f) c a a := rfl
    rw [e, h]
    calc |∑ a, fwd a (fwd a (fwd a (fwd k f))) (c - unit a)|
        ≤ ∑ a, |fwd a (fwd a (fwd a (fwd k f))) (c - unit a)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin d, M₄ := sum_le_sum fun a _ => hM (c - unit a) (hbox0 a) a k a a
      _ = d * M₄ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the correction is small
  have hcorr : |tensorCubicPart (corrTensor (tensorTrace (latticeTaylorTensor f c))) c x| ≤
      d ^ 4 * S ^ 3 * M₄ := by
    have hcoord : ∀ i, |(latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i| ≤ S := by
      intro i
      rw [← latticeEuclideanEmbedding_sub]
      change |(((x - c) i : ℤ) : ℝ)| ≤ S
      rw [Pi.sub_apply, abs_le]
      have h1 := hcx i
      have h2 := hs i
      have h3 : (0 : ℤ) ≤ x i - c i := by omega
      have h4 : (0 : ℝ) ≤ ((x i - c i : ℤ) : ℝ) := by exact_mod_cast h3
      constructor
      · linarith
      · exact_mod_cast h2
    have hb := abs_cubicForm_le (corrTensor (tensorTrace (latticeTaylorTensor f c))) hcoord
    have hsum : ∑ i, ∑ j, ∑ k, |corrTensor (tensorTrace (latticeTaylorTensor f c)) i j k| ≤
        d ^ 3 * (d * M₄) := by
      calc _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, ∑ _k : Fin d, (d : ℝ) * M₄ :=
            sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ =>
              abs_corrTensor_le hσ i j k
        _ = d ^ 3 * (d * M₄) := by
            simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    rw [tensorCubicPart, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have hS3 : (0 : ℝ) ≤ (S : ℝ) ^ 3 := by positivity
    calc |cubicForm (corrTensor (tensorTrace (latticeTaylorTensor f c)))
          (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c)| / 6
        ≤ (d ^ 3 * (d * M₄)) * (S : ℝ) ^ 3 / 6 :=
          div_le_div_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_right hsum hS3))
            (by norm_num)
      _ ≤ d ^ 4 * S ^ 3 * M₄ := by
          have : 0 ≤ (d : ℝ) ^ 4 * S ^ 3 * M₄ := by positivity
          have e : (d : ℝ) ^ 3 * (d * M₄) * S ^ 3 / 6 = (d ^ 4 * S ^ 3 * M₄) / 6 := by ring
          rw [e]; linarith
  -- assemble
  have e : f x - latticeHarmonicTaylorThree f c x =
      (g x - latticeHarmonicTaylorTwo g c x) +
        tensorCubicPart (corrTensor (tensorTrace (latticeTaylorTensor f c))) c x := by
    rw [hg]
    simp only [latticeHarmonicTaylorThree, latticeTaylorRest, latticeHarmonicTensor,
      tensorCubicPart_sub]
    ring
  rw [e]
  have h2' : |g x - latticeHarmonicTaylorTwo g c x| ≤
      d * (d + 1) * S ^ 2 * (d * S * M₃) + d * S ^ 2 * M₃ := h2
  have hS3 : (S : ℝ) ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS1 (by norm_num)
  calc |(g x - latticeHarmonicTaylorTwo g c x) +
        tensorCubicPart (corrTensor (tensorTrace (latticeTaylorTensor f c))) c x|
      ≤ |g x - latticeHarmonicTaylorTwo g c x| +
          |tensorCubicPart (corrTensor (tensorTrace (latticeTaylorTensor f c))) c x| :=
        abs_add_le _ _
    _ ≤ d * (d + 1) * S ^ 2 * (d * S * M₃) + d * S ^ 2 * M₃ + d ^ 4 * S ^ 3 * M₄ :=
        add_le_add h2' hcorr
    _ = (d * (d + 1) * d * d) * S ^ 4 * M₄ + (d * d) * S ^ 3 * M₄ + d ^ 4 * S ^ 3 * M₄ := by
        rw [hM₃]; ring
    _ ≤ (d * (d + 1) * d * d) * S ^ 4 * M₄ + (d * d) * S ^ 4 * M₄ + d ^ 4 * S ^ 4 * M₄ := by
        have h1 : (d * d : ℝ) * S ^ 3 * M₄ ≤ (d * d) * S ^ 4 * M₄ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS3 (by positivity)) hM₀
        have h3 : (d : ℝ) ^ 4 * S ^ 3 * M₄ ≤ d ^ 4 * S ^ 4 * M₄ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS3 (by positivity)) hM₀
        linarith
    _ = taylorThreeConst d * S ^ 4 * M₄ := by rw [taylorThreeConst]; ring

end Rigidity.Proofs.Regularity
