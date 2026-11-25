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

/-! ### The excess decay of order three -/

/-- **Excess decay of order three below the interior scale.** -/
theorem ballExcess_cubicPoly_le_of_latticeHarmonic [NeZero d] (z : Vertex d) {r s : ℝ} {m : ℕ}
    (hm : 0 < m)
    (hbox : Real.sqrt d * ((2 * (2 * (4 * (4 ^ d * (2 * m)) + 6) + 2) + 2 : ℕ) : ℝ) < r)
    (hsm : s + 1 ≤ m) (hs1 : 1 ≤ s) {v : latticeComponent d → ℝ}
    (hv : v ∈ latticeHarmonicClass z r) {w : latticeComponent d → ℝ}
    (hw : w ∈ latticeHarmonicCubicPoly d) :
    ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicCubicPoly d) s v ≤
      taylorThreeConst d * (2 * s) ^ 4 * Real.sqrt (fourthDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) *
          componentBallL2 (latticeComponent d) z r (v - w) ^ 2)) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨F, hvF, hF⟩ := hv
  have hW := latticeLaplacian_latticeExt_eq_zero hw
  set ρ := 4 ^ d * (2 * m) with hρ
  have hρm : m ≤ ρ := by
    have := Nat.one_le_pow d 4 (by norm_num); rw [hρ]; nlinarith
  set f : (Fin d → ℤ) → ℝ := fun y => F y - latticeExt w y with hfdef
  have hf : ∀ x ∈ supBox z (2 * (2 * (4 * ρ + 6) + 2) + 2), latticeLaplacian f x = 0 := by
    intro x hx
    rw [hfdef, latticeLaplacian_sub, hW x, sub_zero]
    exact hF x ((dist_le_of_mem_supBox hx).trans_lt hbox)
  have hs0 : 0 ≤ s := by linarith
  set n := ⌊s⌋₊ with hn
  have hns : (n : ℝ) ≤ s := Nat.floor_le hs0
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hs1)
  have hnm : n + 1 ≤ m := by
    have : ((n + 1 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  set M := Real.sqrt (fourthDiffCoeff d m *
    ∑ y ∈ supBox z (2 * (2 * (4 * ρ + 6) + 2) + 2), f y ^ 2) with hMdef
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM : ∀ y ∈ supBox z m, ∀ a b e g, |fwd g (fwd e (fwd a (fwd b f))) y| ≤ M := by
    intro y hy a b e g
    apply Real.abs_le_sqrt
    exact sq_fwd4_le f z hm (fun x hx => hf x (by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)) a b e g hy
  set c : Fin d → ℤ := fun i => z i - n with hc
  have hcn : c ∈ supBox z n := corner_mem_supBox z n
  have hΔc : latticeLaplacian f c = 0 := hf c (by
    rw [mem_supBox_iff_supDist_le] at hcn ⊢; omega)
  have hΔk : ∀ k, latticeLaplacian f (c + unit k) = 0 := fun k => hf _ (by
    rw [mem_supBox_iff_supDist_le] at hcn ⊢
    have := supDist_add_unit_le' c z k; omega)
  have hP := mem_latticeHarmonicCubicPoly_latticeHarmonicTaylorThree f c
  have hsum := (latticeHarmonicCubicPoly d).add_mem hw hP
  refine (ballExcess_le _ _ hsum).trans ?_
  rw [componentBallSeminorm_apply]
  have hK := taylorThreeConst_nonneg d
  have hbound : 0 ≤ taylorThreeConst d * ((2 * n : ℕ) : ℝ) ^ 4 * M := by positivity
  refine (componentBallL2_le_of_abs_le (latticeComponent d) z s hbound ?_).trans ?_
  · intro x hx
    have hxz := abs_sub_le_floor_of_mem_ball hx
    have hcx : ∀ i, c i ≤ x.val i := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; omega
    have hs2 : ∀ i, x.val i - c i ≤ (2 * n : ℕ) := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; push_cast; omega
    have htay := abs_sub_latticeHarmonicTaylorThree_le hd f hcx (S := 2 * n) (by omega) hs2 hM0
      (fun y hy a b e g => hM y (by
        rw [mem_supBox_iff_supDist_le]
        simp only [supDist, Finset.sup_le_iff, mem_univ, true_implies]
        intro i
        have h1 := hy i
        have h2 := abs_le.1 (hxz i)
        simp only [hc] at h1
        rw [← hn] at h2
        omega) a b e g) hΔc hΔk
    have hval : (v - (w + fun x : latticeComponent d => latticeHarmonicTaylorThree f c x.val)) x =
        f x.val - latticeHarmonicTaylorThree f c x.val := by
      show v x - (w x + latticeHarmonicTaylorThree f c x.val) =
        F x.val - w x - latticeHarmonicTaylorThree f c x.val
      rw [hvF]
      ring
    rw [hval]
    exact htay
  · have ht : ((2 * n : ℕ) : ℝ) ≤ 2 * s := by push_cast; linarith
    have ht0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : ((2 * n : ℕ) : ℝ) ^ 4 ≤ (2 * s) ^ 4 := pow_le_pow_left₀ ht0 ht 4
    have hMle : M ≤ Real.sqrt (fourthDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) *
          componentBallL2 (latticeComponent d) z r (v - w) ^ 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (fourthDiffCoeff_nonneg d m)
      rw [← sum_sq_eq_card_mul_componentBallL2_sq]
      have hball := sum_sq_supBox_le_ball z hbox f
      refine hball.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
      rw [Pi.sub_apply, hvF]
      rfl
    calc taylorThreeConst d * ((2 * n : ℕ) : ℝ) ^ 4 * M ≤ taylorThreeConst d * (2 * s) ^ 4 * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hK) hM0
      _ ≤ _ := mul_le_mul_of_nonneg_left hMle (by positivity)

/-- The lower radius `X₃ = 2 √d (32 · 4^d + 30)` of the excess decay of order three. -/
noncomputable def latticeHRScaleCubic (d : ℕ) : ℝ := 2 * Real.sqrt d * (32 * 4 ^ d + 30)

/-- The constant of the excess decay of order three of lattice harmonic functions. -/
noncomputable def latticeHRConstCubic (d : ℕ) : ℝ :=
  16 * taylorThreeConst d * Real.sqrt (fourthDiffConst d * 5 ^ d *
      (2 * latticeHRScaleCubic d) ^ (d + 8)) +
    Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (2 * (2 * latticeHRScaleCubic d)) ^ ((d : ℝ) / 2) *
      (2 * (2 * latticeHRScaleCubic d)) ^ 4

theorem latticeHRScaleCubic_nonneg (d : ℕ) : 0 ≤ latticeHRScaleCubic d := by
  unfold latticeHRScaleCubic; positivity

theorem latticeHRConstCubic_nonneg (d : ℕ) : 0 ≤ latticeHRConstCubic d := by
  have := latticeHRScaleCubic_nonneg d
  have := taylorThreeConst_nonneg d
  rw [latticeHRConstCubic]; positivity

/-- **Excess decay of order three, against one lattice harmonic cubic polynomial.** -/
theorem ballExcess_le_latticeHRConstCubic_mul [NeZero d] (z : Vertex d) {R r s : ℝ} (hrR : r ≤ R)
    {v : latticeComponent d → ℝ} (hv : v ∈ latticeHarmonicClass z r)
    (hXs : latticeHRScaleCubic d ≤ s) (hsr : s ≤ r / 2) {w : latticeComponent d → ℝ}
    (hw : w ∈ latticeHarmonicCubicPoly d) :
    ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicCubicPoly d) s v ≤
      latticeHRConstCubic d * (s / r) ^ 4 * componentBallL2 (latticeComponent d) z r (v - w) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  set X₀ := latticeHRScaleCubic d with hX₀
  set Λ : ℝ := 32 * 4 ^ d + 30 with hΛ
  have hΛ1 : 62 ≤ Λ := by
    rw [hΛ]; have : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num); linarith
  have hX₀def : X₀ = 2 * Real.sqrt d * Λ := rfl
  have hX₀pos : 0 < X₀ := by rw [hX₀def]; positivity
  set B := 2 * X₀ with hB
  have hBpos : 0 < B := by positivity
  have hs0 : 0 < s := hX₀pos.trans_le hXs
  have hX₀1 : 1 ≤ X₀ := by rw [hX₀def]; nlinarith
  have hs1 : 1 ≤ s := hX₀1.trans hXs
  have hr2 : 2 * X₀ ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  set N := componentBallL2 (latticeComponent d) z r (v - w) with hN
  have hN0 : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  set m := ⌊r / X₀⌋₊ with hmdef
  have hrX : 2 ≤ r / X₀ := by rw [le_div_iff₀ hX₀pos]; linarith
  have hm2 : 2 ≤ m := Nat.le_floor (by exact_mod_cast hrX)
  have hm0 : 0 < m := by omega
  have hmle : (m : ℝ) ≤ r / X₀ := Nat.floor_le (by positivity)
  have hmge : r / B ≤ m := by
    have h1 := Nat.lt_floor_add_one (r / X₀)
    rw [← hmdef] at h1
    have : r / B = r / X₀ / 2 := by rw [hB]; field_simp
    rw [this]; linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hbox : Real.sqrt d * ((2 * (2 * (4 * (4 ^ d * (2 * m)) + 6) + 2) + 2 : ℕ) : ℝ) < r := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have h1 : ((2 * (2 * (4 * (4 ^ d * (2 * m)) + 6) + 2) + 2 : ℕ) : ℝ) ≤ Λ * m := by
      push_cast; rw [hΛ]; nlinarith
    have h2 : Λ * m ≤ Λ * (r / X₀) := mul_le_mul_of_nonneg_left hmle (by linarith)
    have h3 : Real.sqrt d * (Λ * (r / X₀)) = r / 2 := by
      rw [hX₀def]; field_simp
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : 0 ≤ Real.sqrt d)
    linarith
  have hT := taylorThreeConst_nonneg d
  have hCH1 : 0 ≤ 16 * taylorThreeConst d * Real.sqrt (fourthDiffConst d * 5 ^ d *
      (2 * latticeHRScaleCubic d) ^ (d + 8)) := by positivity
  have hCH2 : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) *
      (2 * (2 * latticeHRScaleCubic d)) ^ ((d : ℝ) / 2) * (2 * (2 * latticeHRScaleCubic d)) ^ 4 := by
    positivity
  have hsr4 : 0 ≤ (s / r) ^ 4 := by positivity
  by_cases hsm : s + 1 ≤ m
  · have h := ballExcess_cubicPoly_le_of_latticeHarmonic z hm0 hbox hsm hs1 hv hw
    refine h.trans ?_
    set K₀ : ℝ := fourthDiffConst d with hK₀
    have hK₀0 : 0 ≤ K₀ := fourthDiffConst_nonneg d
    have hcoef := fourthDiffCoeff_le d hm0
    have hcard : ((componentEuclideanBall (latticeComponent d) z r).card : ℝ) ≤ (5 * r) ^ d :=
      (card_componentEuclideanBall_le _ z hr0.le).trans
        (pow_le_pow_left₀ (by linarith) (by linarith) d)
    have hinv : 1 / (m : ℝ) ^ (d + 8) ≤ (B / r) ^ (d + 8) := by
      rw [one_div, ← inv_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_comm₀ hmpos (by positivity), inv_div]
      exact hmge
    have hin : fourthDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2) ≤
        (K₀ * 5 ^ d * B ^ (d + 8)) * (N / r ^ 4) ^ 2 := by
      calc fourthDiffCoeff d m *
            (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2)
          ≤ K₀ / (m : ℝ) ^ (d + 8) * ((5 * r) ^ d * N ^ 2) :=
            mul_le_mul hcoef (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)) (by positivity)
              (by positivity)
        _ ≤ K₀ * (B / r) ^ (d + 8) * ((5 * r) ^ d * N ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left hinv hK₀0
        _ = (K₀ * 5 ^ d * B ^ (d + 8)) * (N / r ^ 4) ^ 2 := by
            rw [div_pow, div_pow, mul_pow]
            field_simp
            ring
    have hsq : Real.sqrt (fourthDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2)) ≤
        Real.sqrt (K₀ * 5 ^ d * B ^ (d + 8)) * (N / r ^ 4) := by
      calc _ ≤ Real.sqrt ((K₀ * 5 ^ d * B ^ (d + 8)) * (N / r ^ 4) ^ 2) := Real.sqrt_le_sqrt hin
        _ = _ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc taylorThreeConst d * (2 * s) ^ 4 * Real.sqrt (fourthDiffCoeff d m *
          (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2))
        ≤ taylorThreeConst d * (2 * s) ^ 4 *
            (Real.sqrt (K₀ * 5 ^ d * B ^ (d + 8)) * (N / r ^ 4)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 16 * taylorThreeConst d * Real.sqrt (K₀ * 5 ^ d * B ^ (d + 8)) * (s / r) ^ 4 * N := by
          field_simp
          ring
      _ ≤ latticeHRConstCubic d * (s / r) ^ 4 * N := by
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul_of_nonneg_right _ hsr4
          rw [latticeHRConstCubic, ← hX₀, ← hB, ← hK₀]
          linarith
  · push Not at hsm
    have hm2s : (m : ℝ) < 2 * s := by linarith
    have hsm' : r / B < 2 * s := lt_of_le_of_lt hmge hm2s
    have hvol := clusterBallVolumeComparison_of_clusterCubeDensity (latticeComponent d) z R hd
      one_pos (clusterCubeDensity_latticeComponent z (24 * Real.sqrt d) 1)
    have h6 : 6 * Real.sqrt d * max 1 1 ≤ s := by
      rw [max_self, mul_one]
      have : 6 * Real.sqrt d ≤ X₀ := by rw [hX₀def]; nlinarith
      linarith
    have hmono := radiusMonotone_componentBallSeminorm (latticeComponent d) z
      (by positivity : (0 : ℝ) < 6 * Real.sqrt d * max 1 1) (by positivity) hvol
    have h1 := ballExcess_le (componentBallSeminorm (latticeComponent d) z)
      (latticeHarmonicCubicPoly d) (s := s) (u := v) hw
    have h2 := hmono (v - w) s r h6 (by linarith) hrR
    rw [componentBallSeminorm_apply, componentBallSeminorm_apply] at h2
    rw [componentBallSeminorm_apply] at h1
    have h2B : 0 < 2 * B := by positivity
    have hrs : r / s ≤ 2 * B := by
      rw [div_le_iff₀ hs0]; rw [div_lt_iff₀ hBpos] at hsm'; linarith
    have hrs0 : 0 ≤ r / s := by positivity
    have h3 : (r / s) ^ ((d : ℝ) / 2) ≤ (2 * B) ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow hrs0 hrs (by positivity)
    have h4 : 1 ≤ (2 * B) ^ 4 * (s / r) ^ 4 := by
      rw [← mul_pow]
      have : 1 ≤ 2 * B * (s / r) := by
        rw [div_lt_iff₀ hBpos] at hsm'
        rw [mul_div_assoc', le_div_iff₀ hr0]; linarith
      exact one_le_pow₀ this
    have hK : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) := Real.sqrt_nonneg _
    calc ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicCubicPoly d) s v
        ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (r / s) ^ ((d : ℝ) / 2) * N :=
          h1.trans h2
      _ ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (2 * B) ^ ((d : ℝ) / 2) * N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hK) hN0
      _ ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (2 * B) ^ ((d : ℝ) / 2) *
            ((2 * B) ^ 4 * (s / r) ^ 4) * N := by
          have h5 : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (2 * B) ^ ((d : ℝ) / 2) *
              N := by positivity
          nlinarith
      _ ≤ latticeHRConstCubic d * (s / r) ^ 4 * N := by
          have e : Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (2 * B) ^ ((d : ℝ) / 2) *
              ((2 * B) ^ 4 * (s / r) ^ 4) * N = (Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) *
                (2 * B) ^ ((d : ℝ) / 2) * (2 * B) ^ 4) * (s / r) ^ 4 * N := by ring
          rw [e]
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul_of_nonneg_right _ hsr4
          rw [latticeHRConstCubic, ← hX₀, ← hB]
          linarith

/-- **Excess decay of order three of lattice harmonic functions on the balls of `ℤᵈ`**:
`HarmonicRegularity` with `j = 3` for the class `latticeHarmonicClass z` and the lattice harmonic
cubic polynomials, above the radius `latticeHRScaleCubic d`. -/
theorem harmonicRegularity_cubicPoly_latticeHarmonicClass [NeZero d] (z : Vertex d) (R : ℝ) :
    HarmonicRegularity (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicClass z)
      (latticeHarmonicCubicPoly d) 3 (latticeHRScaleCubic d) R (latticeHRConstCubic d) := by
  intro r hrR v hv s hXs hsr
  have hK : 0 ≤ latticeHRConstCubic d * (s / r) ^ (3 + 1) := by
    have hr : 0 ≤ r := by have := latticeHRScaleCubic_nonneg d; linarith
    have hs : 0 ≤ s := (latticeHRScaleCubic_nonneg d).trans hXs
    exact mul_nonneg (latticeHRConstCubic_nonneg d) (pow_nonneg (div_nonneg hs hr) _)
  have e : latticeHRConstCubic d * (s / r) ^ (3 + 1) *
      ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicCubicPoly d) r v =
      ⨅ w : latticeHarmonicCubicPoly d, latticeHRConstCubic d * (s / r) ^ (3 + 1) *
        componentBallSeminorm (latticeComponent d) z r (v - w) :=
    Real.mul_iInf_of_nonneg hK _
  rw [e]
  refine le_ciInf fun w => ?_
  rw [componentBallSeminorm_apply]
  exact ballExcess_le_latticeHRConstCubic_mul z hrR hv hXs hsr w.2

end Rigidity.Proofs.Regularity
