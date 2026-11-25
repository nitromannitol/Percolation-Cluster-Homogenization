import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# Cubic forms on `ℤᵈ` and the lattice harmonic cubic polynomials

For a tensor `t` of order three, `cubicMixed t u v w = ∑ tᵢⱼₖ uᵢ vⱼ wₖ` is trilinear and
`cubicForm t v = cubicMixed t v v v`. When `t` is invariant under the permutations of its indices
(`IsSymmTensor`), `cubicForm t (u + w) = cubicForm t u + 3 t(w, u, u) + 3 t(w, w, u) + cubicForm t w`
(`cubicForm_add`), so that the cubic part `tensorCubicPart t c y = cubicForm t (y - c) / 6` on `ℤᵈ`
has the constant third forward differences `D_a D_b D_e = t_{abe}`
(`fwd_fwd_fwd_tensorCubicPart`) and the lattice Laplacian `y ↦ ∑ₖ (∑ₐ tₐₐₖ) (y - c)ₖ`
(`latticeLaplacian_tensorCubicPart`), the lattice Laplacian being exact on polynomials of degree
three. The tensor `corrTensor σ`, `(σᵢ δⱼₖ + σⱼ δᵢₖ + σₖ δᵢⱼ) / (d + 2)`, is symmetric with trace
`σ` (`tensorTrace_corrTensor`); it removes the trace of the third differences in the harmonic
third-order expansion.

`latticeHarmonicCubicPoly d` is the space `Ā_3` of the lattice harmonic cubic polynomials: the
functions `q + cubicForm t (·) / 6` with `t` symmetric and trace-free and `q` a lattice harmonic
quadratic function. Its elements are lattice harmonic (`latticeLaplacian_latticeExt_eq_zero`), they
are the cubic part `tensorCubicPart t z` centred at any `z` plus a lattice harmonic quadratic
function (`sub_tensorCubicPart_mem_latticeHarmonicQuadratic`), and their third forward differences
are the entries of `t` (`fwd_fwd_fwd_latticeExt`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The trilinear form `(u, v, w) ↦ ∑ᵢ ∑ⱼ ∑ₖ tᵢⱼₖ uᵢ vⱼ wₖ` of a tensor of order three. -/
def cubicMixed (t : Fin d → Fin d → Fin d → ℝ) (u v w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, ∑ k, t i j k * u i * v j * w k

/-- The cubic form `v ↦ ∑ᵢ ∑ⱼ ∑ₖ tᵢⱼₖ vᵢ vⱼ vₖ`. -/
def cubicForm (t : Fin d → Fin d → Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  cubicMixed t v v v

/-- A tensor of order three invariant under the permutations of its indices. -/
def IsSymmTensor (t : Fin d → Fin d → Fin d → ℝ) : Prop :=
  ∀ i j k, t i j k = t j i k ∧ t i j k = t i k j

/-- The trace `k ↦ ∑ₐ tₐₐₖ` of a tensor of order three. -/
def tensorTrace (t : Fin d → Fin d → Fin d → ℝ) (k : Fin d) : ℝ :=
  ∑ a, t a a k

section Trilinear

variable (t : Fin d → Fin d → Fin d → ℝ)

theorem cubicMixed_add_left (u u' v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t (u + u') v w = cubicMixed t u v w + cubicMixed t u' v w := by
  simp only [cubicMixed, PiLp.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_add_mid (u v v' w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u (v + v') w = cubicMixed t u v w + cubicMixed t u v' w := by
  simp only [cubicMixed, PiLp.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_add_right (u v w w' : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u v (w + w') = cubicMixed t u v w + cubicMixed t u v w' := by
  simp only [cubicMixed, PiLp.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_neg_left (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t (-u) v w = -cubicMixed t u v w := by
  simp only [cubicMixed, PiLp.neg_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_neg_mid (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u (-v) w = -cubicMixed t u v w := by
  simp only [cubicMixed, PiLp.neg_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_neg_right (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u v (-w) = -cubicMixed t u v w := by
  simp only [cubicMixed, PiLp.neg_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_add_tensor (t' : Fin d → Fin d → Fin d → ℝ) (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed (t + t') u v w = cubicMixed t u v w + cubicMixed t' u v w := by
  simp only [cubicMixed, Pi.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_neg_tensor (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed (-t) u v w = -cubicMixed t u v w := by
  simp only [cubicMixed, Pi.neg_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_sub_tensor (t' : Fin d → Fin d → Fin d → ℝ) (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed (t - t') u v w = cubicMixed t u v w - cubicMixed t' u v w := by
  simp only [cubicMixed, Pi.sub_apply, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem cubicMixed_zero_tensor (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed (0 : Fin d → Fin d → Fin d → ℝ) u v w = 0 := by
  simp [cubicMixed]

theorem cubicMixed_single_single_single (a b e : Fin d) :
    cubicMixed t (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
      (EuclideanSpace.single e 1) = t a b e := by
  simp [cubicMixed]

theorem cubicMixed_single_single (a b : Fin d) (w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) w =
      ∑ k, t a b k * w k := by
  simp [cubicMixed]

/-- `t(u, v, v)` is the quadratic form of the matrix `(∑ᵢ tᵢⱼₖ uᵢ)ⱼₖ` at `v`. -/
theorem cubicMixed_eq_quadForm (u v : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u v v = quadForm (fun j k => ∑ i, t i j k * u i) v := by
  simp only [cubicMixed, quadForm, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]

/-- `t(u, u', v)` is the inner product of `v` with the vector `(∑ᵢ ∑ⱼ tᵢⱼₖ uᵢ u'ⱼ)ₖ`. -/
theorem cubicMixed_eq_inner (u u' v : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u u' v =
      inner ℝ (WithLp.toLp 2 fun k => ∑ i, ∑ j, t i j k * u i * u' j : EuclideanSpace ℝ (Fin d))
        v := by
  rw [inner_eq_sum]
  simp only [cubicMixed, sum_mul]
  exact (sum_congr rfl fun i _ => sum_comm).trans sum_comm

theorem mul_cubicMixed_eq_quadForm (r : ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    r * cubicMixed t u v v = quadForm (fun j k => r * ∑ i, t i j k * u i) v := by
  rw [cubicMixed_eq_quadForm, quadForm, quadForm, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  ring

theorem mul_cubicMixed_eq_inner (r : ℝ) (u u' v : EuclideanSpace ℝ (Fin d)) :
    r * cubicMixed t u u' v =
      inner ℝ (WithLp.toLp 2 fun k => r * ∑ i, ∑ j, t i j k * u i * u' j :
        EuclideanSpace ℝ (Fin d)) v := by
  rw [cubicMixed_eq_inner, inner_eq_sum, inner_eq_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  show r * ((∑ i, ∑ j, t i j k * u i * u' j) * v k) = (r * ∑ i, ∑ j, t i j k * u i * u' j) * v k
  ring

end Trilinear

section Symmetric

variable {t : Fin d → Fin d → Fin d → ℝ}

theorem cubicMixed_comm12 (ht : IsSymmTensor t) (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u v w = cubicMixed t v u w := by
  rw [cubicMixed, cubicMixed, sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [(ht j i k).1]
  ring

theorem cubicMixed_comm23 (ht : IsSymmTensor t) (u v w : EuclideanSpace ℝ (Fin d)) :
    cubicMixed t u v w = cubicMixed t u w v := by
  rw [cubicMixed, cubicMixed]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [(ht i k j).2]
  ring

/-- **The expansion of a symmetric cubic form at a sum.** -/
theorem cubicForm_add (ht : IsSymmTensor t) (u w : EuclideanSpace ℝ (Fin d)) :
    cubicForm t (u + w) = cubicForm t u + 3 * cubicMixed t w u u + 3 * cubicMixed t w w u +
      cubicForm t w := by
  have h1 : cubicMixed t u u w = cubicMixed t w u u := by
    rw [cubicMixed_comm23 ht, cubicMixed_comm12 ht]
  have h2 : cubicMixed t u w u = cubicMixed t w u u := cubicMixed_comm12 ht _ _ _
  have h3 : cubicMixed t u w w = cubicMixed t w w u := by
    rw [cubicMixed_comm12 ht, cubicMixed_comm23 ht]
  have h4 : cubicMixed t w u w = cubicMixed t w w u := cubicMixed_comm23 ht _ _ _
  simp only [cubicForm, cubicMixed_add_left, cubicMixed_add_mid, cubicMixed_add_right]
  rw [h1, h2, h3, h4]
  ring

theorem cubicForm_neg (u : EuclideanSpace ℝ (Fin d)) :
    cubicForm t (-u) = -cubicForm t u := by
  simp only [cubicForm, cubicMixed_neg_left, cubicMixed_neg_mid, cubicMixed_neg_right, neg_neg]

end Symmetric

theorem isSymmTensor_add {t t' : Fin d → Fin d → Fin d → ℝ} (ht : IsSymmTensor t)
    (ht' : IsSymmTensor t') : IsSymmTensor (t + t') := fun i j k => by
  simp only [Pi.add_apply]
  exact ⟨by rw [(ht i j k).1, (ht' i j k).1], by rw [(ht i j k).2, (ht' i j k).2]⟩

theorem isSymmTensor_neg {t : Fin d → Fin d → Fin d → ℝ} (ht : IsSymmTensor t) :
    IsSymmTensor (-t) := fun i j k => by
  simp only [Pi.neg_apply]
  exact ⟨by rw [(ht i j k).1], by rw [(ht i j k).2]⟩

theorem isSymmTensor_sub {t t' : Fin d → Fin d → Fin d → ℝ} (ht : IsSymmTensor t)
    (ht' : IsSymmTensor t') : IsSymmTensor (t - t') := fun i j k => by
  simp only [Pi.sub_apply]
  exact ⟨by rw [(ht i j k).1, (ht' i j k).1], by rw [(ht i j k).2, (ht' i j k).2]⟩

theorem isSymmTensor_zero : IsSymmTensor (0 : Fin d → Fin d → Fin d → ℝ) := fun _ _ _ => by
  simp

/-- **A bound for a cubic form** on the vectors with coordinates at most `B`. -/
theorem abs_cubicForm_le (t : Fin d → Fin d → Fin d → ℝ) {v : EuclideanSpace ℝ (Fin d)} {B : ℝ}
    (hv : ∀ i, |v i| ≤ B) : |cubicForm t v| ≤ (∑ i, ∑ j, ∑ k, |t i j k|) * B ^ 3 := by
  rw [cubicForm, cubicMixed, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_mul]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv i)
  have hi := hv i
  have hj := hv j
  have hk := hv k
  calc |t i j k| * |v i| * |v j| * |v k| ≤ |t i j k| * B * B * B := by gcongr
    _ = |t i j k| * B ^ 3 := by ring

/-! ### The cubic part on the lattice -/

/-- The cubic part `y ↦ cubicForm t (y - c) / 6` at the point `c` of `ℤᵈ`. -/
noncomputable def tensorCubicPart (t : Fin d → Fin d → Fin d → ℝ) (c y : Fin d → ℤ) : ℝ :=
  cubicForm t (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) / 6

theorem latticeEuclideanEmbedding_add_unit_sub (y c : Fin d → ℤ) (a : Fin d) :
    latticeEuclideanEmbedding (y + unit a) - latticeEuclideanEmbedding c =
      (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) + EuclideanSpace.single a 1 := by
  rw [latticeEuclideanEmbedding_add, latticeEuclideanEmbedding_unit]; abel

theorem latticeEuclideanEmbedding_sub_unit_sub (y c : Fin d → ℤ) (a : Fin d) :
    latticeEuclideanEmbedding (y - unit a) - latticeEuclideanEmbedding c =
      (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) + -EuclideanSpace.single a 1 := by
  rw [latticeEuclideanEmbedding_sub_unit]; abel

theorem latticeEuclideanEmbedding_zero_vertex :
    latticeEuclideanEmbedding (0 : Fin d → ℤ) = 0 := by
  ext i
  change (((0 : Fin d → ℤ) i : ℤ) : ℝ) = (0 : EuclideanSpace ℝ (Fin d)) i
  simp

theorem fwd_add (i : Fin d) (f g : (Fin d → ℤ) → ℝ) :
    fwd i (fun y => f y + g y) = fun y => fwd i f y + fwd i g y := by
  funext y; simp only [fwd]; ring

section CubicPart

variable {t : Fin d → Fin d → Fin d → ℝ}

/-- The first forward differences of the cubic part. -/
theorem fwd_tensorCubicPart (ht : IsSymmTensor t) (c : Fin d → ℤ) (a : Fin d) :
    fwd a (tensorCubicPart t c) = fun y =>
      (3 * cubicMixed t (EuclideanSpace.single a 1)
          (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c)
          (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) +
        3 * cubicMixed t (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)
          (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) +
        cubicForm t (EuclideanSpace.single a 1)) / 6 := by
  funext y
  simp only [fwd, tensorCubicPart, latticeEuclideanEmbedding_add_unit_sub]
  rw [cubicForm_add ht]
  ring

/-- The second forward differences of the cubic part. -/
theorem fwd_fwd_tensorCubicPart (ht : IsSymmTensor t) (c : Fin d → ℤ) (a b : Fin d) :
    fwd b (fwd a (tensorCubicPart t c)) = fun y =>
      cubicMixed t (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
          (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) +
        (cubicMixed t (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
            (EuclideanSpace.single b 1) +
          cubicMixed t (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)
            (EuclideanSpace.single b 1)) / 2 := by
  rw [fwd_tensorCubicPart ht]
  funext y
  simp only [fwd, latticeEuclideanEmbedding_add_unit_sub, cubicMixed_add_mid,
    cubicMixed_add_right]
  rw [cubicMixed_comm23 ht (EuclideanSpace.single a 1)
    (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) (EuclideanSpace.single b 1)]
  ring

/-- **The third forward differences of the cubic part** are the entries of the tensor. -/
theorem fwd_fwd_fwd_tensorCubicPart (ht : IsSymmTensor t) (c : Fin d → ℤ) (a b e : Fin d)
    (y : Fin d → ℤ) : fwd e (fwd b (fwd a (tensorCubicPart t c))) y = t a b e := by
  rw [fwd_fwd_tensorCubicPart ht]
  simp only [fwd, latticeEuclideanEmbedding_add_unit_sub, cubicMixed_add_right]
  rw [cubicMixed_single_single_single]
  ring

/-- **The lattice Laplacian of the cubic part** is the linear function with the trace of the
tensor as coefficients. -/
theorem latticeLaplacian_tensorCubicPart (ht : IsSymmTensor t) (c y : Fin d → ℤ) :
    latticeLaplacian (tensorCubicPart t c) y =
      ∑ k, tensorTrace t k * (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) k := by
  simp only [latticeLaplacian, tensorCubicPart, latticeEuclideanEmbedding_add_unit_sub,
    latticeEuclideanEmbedding_sub_unit_sub]
  have h : ∀ a : Fin d,
      cubicForm t ((latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) +
          EuclideanSpace.single a 1) / 6 +
        cubicForm t ((latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) +
          -EuclideanSpace.single a 1) / 6 -
        2 * (cubicForm t (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) / 6) =
      cubicMixed t (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)
        (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) := by
    intro a
    rw [cubicForm_add ht, cubicForm_add ht, cubicMixed_neg_left, cubicMixed_neg_left,
      cubicMixed_neg_mid, cubicForm_neg]
    ring
  rw [sum_congr rfl fun a _ => h a]
  simp only [cubicMixed_single_single, tensorTrace, sum_mul]
  rw [sum_comm]

end CubicPart

/-! ### The correction of the trace -/

/-- The tensor `(σᵢ δⱼₖ + σⱼ δᵢₖ + σₖ δᵢⱼ) / (d + 2)`, symmetric with trace `σ`. -/
noncomputable def corrTensor (σ : Fin d → ℝ) : Fin d → Fin d → Fin d → ℝ :=
  fun i j k => (σ i * (if j = k then 1 else 0) + σ j * (if i = k then 1 else 0) +
    σ k * (if i = j then 1 else 0)) / (d + 2)

theorem ite_eq_comm_one (i j : Fin d) :
    (if j = i then (1 : ℝ) else 0) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem isSymmTensor_corrTensor (σ : Fin d → ℝ) : IsSymmTensor (corrTensor σ) := by
  intro i j k
  simp only [corrTensor]
  constructor
  · rw [ite_eq_comm_one i j]
    ring
  · rw [ite_eq_comm_one j k]
    ring

theorem tensorTrace_corrTensor (σ : Fin d → ℝ) : tensorTrace (corrTensor σ) = σ := by
  funext k
  simp only [tensorTrace, corrTensor, ← sum_div, sum_add_distrib, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (d : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem abs_corrTensor_le {σ : Fin d → ℝ} {L : ℝ} (hσ : ∀ i, |σ i| ≤ L) (i j k : Fin d) :
    |corrTensor σ i j k| ≤ L := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast i.pos
  have hite : ∀ (x : ℝ) (p : Prop) [Decidable p], |x * (if p then (1 : ℝ) else 0)| ≤ |x| := by
    intro x p _
    split_ifs <;> simp
  have h1 := hite (σ i) (j = k)
  have h2 := hite (σ j) (i = k)
  have h3 := hite (σ k) (i = j)
  have h4 := abs_add_three (σ i * (if j = k then (1 : ℝ) else 0))
    (σ j * (if i = k then (1 : ℝ) else 0)) (σ k * (if i = j then (1 : ℝ) else 0))
  have hL : 0 ≤ L := (abs_nonneg _).trans (hσ i)
  rw [corrTensor, abs_div, abs_of_pos (by positivity : (0 : ℝ) < d + 2), div_le_iff₀ (by positivity)]
  have := hσ i
  have := hσ j
  have := hσ k
  nlinarith

theorem tensorTrace_add (t t' : Fin d → Fin d → Fin d → ℝ) (k : Fin d) :
    tensorTrace (t + t') k = tensorTrace t k + tensorTrace t' k := by
  simp only [tensorTrace, Pi.add_apply, sum_add_distrib]

theorem tensorTrace_neg (t : Fin d → Fin d → Fin d → ℝ) (k : Fin d) :
    tensorTrace (-t) k = -tensorTrace t k := by
  simp only [tensorTrace, Pi.neg_apply, sum_neg_distrib]

theorem tensorTrace_sub (t t' : Fin d → Fin d → Fin d → ℝ) (k : Fin d) :
    tensorTrace (t - t') k = tensorTrace t k - tensorTrace t' k := by
  simp only [tensorTrace, Pi.sub_apply, sum_sub_distrib]

/-! ### The lattice harmonic cubic polynomials -/

/-- The cubic part centred at `c` differs from the cubic part centred at `0` by a quadratic
function. -/
theorem tensorCubicPart_sub_mem_clusterQuadratic [NeZero d] {t : Fin d → Fin d → Fin d → ℝ}
    (ht : IsSymmTensor t) (c : Fin d → ℤ) :
    (fun x : latticeComponent d => tensorCubicPart t c x.val -
      cubicForm t (latticeEuclideanEmbedding x.val) / 6) ∈ clusterQuadratic (latticeComponent d) := by
  refine ⟨cubicForm t (-latticeEuclideanEmbedding c) / 6,
    WithLp.toLp 2 fun k => 1 / 2 * ∑ i, ∑ j, t i j k * (-latticeEuclideanEmbedding c) i *
      (-latticeEuclideanEmbedding c) j,
    fun j k => 1 / 2 * ∑ i, t i j k * (-latticeEuclideanEmbedding c) i, fun x => ?_⟩
  simp only [tensorCubicPart]
  rw [sub_eq_add_neg (latticeEuclideanEmbedding x.val), cubicForm_add ht,
    ← mul_cubicMixed_eq_quadForm, ← mul_cubicMixed_eq_inner]
  ring

/-- The third forward differences of a quadratic function vanish. -/
theorem fwd_fwd_fwd_latticeExt_of_mem_clusterQuadratic [NeZero d] {q : latticeComponent d → ℝ}
    (hq : q ∈ clusterQuadratic (latticeComponent d)) (a b e : Fin d) (y : Fin d → ℤ) :
    fwd e (fwd b (fwd a (latticeExt q))) y = 0 := by
  obtain ⟨α, p, M, hq⟩ := hq
  simp only [fwd, latticeExt, hq, latticeEuclideanEmbedding_add, latticeEuclideanEmbedding_unit,
    inner_add_right, quadForm_add, quadPolar_add_left]
  ring

/-- **The lattice harmonic cubic polynomials** `Ā_3`: the functions `q + cubicForm t (·) / 6`
with `t` symmetric and trace-free and `q` a lattice harmonic quadratic function. -/
def latticeHarmonicCubicPoly (d : ℕ) [NeZero d] : AddSubgroup (latticeComponent d → ℝ) where
  carrier := {v | ∃ t : Fin d → Fin d → Fin d → ℝ, IsSymmTensor t ∧ (∀ k, tensorTrace t k = 0) ∧
    (fun x => v x - cubicForm t (latticeEuclideanEmbedding x.val) / 6) ∈
      latticeHarmonicQuadratic d}
  add_mem' := by
    rintro v w ⟨t, ht, htr, hv⟩ ⟨t', ht', htr', hw⟩
    refine ⟨t + t', isSymmTensor_add ht ht', fun k => by rw [tensorTrace_add, htr, htr', add_zero],
      ?_⟩
    convert (latticeHarmonicQuadratic d).add_mem hv hw using 1
    funext x
    simp only [Pi.add_apply, cubicForm, cubicMixed_add_tensor]
    ring
  zero_mem' := ⟨0, isSymmTensor_zero, fun k => by simp [tensorTrace], by
    convert (latticeHarmonicQuadratic d).zero_mem using 1
    funext x
    simp [cubicForm, cubicMixed_zero_tensor]⟩
  neg_mem' := by
    rintro v ⟨t, ht, htr, hv⟩
    refine ⟨-t, isSymmTensor_neg ht, fun k => by rw [tensorTrace_neg, htr, neg_zero], ?_⟩
    convert (latticeHarmonicQuadratic d).neg_mem hv using 1
    funext x
    simp only [Pi.neg_apply, cubicForm, cubicMixed_neg_tensor]
    ring

theorem latticeHarmonicQuadratic_le_latticeHarmonicCubicPoly [NeZero d] :
    latticeHarmonicQuadratic d ≤ latticeHarmonicCubicPoly d := by
  intro v hv
  refine ⟨0, isSymmTensor_zero, fun k => by simp [tensorTrace], ?_⟩
  convert hv using 1
  funext x
  simp [cubicForm, cubicMixed_zero_tensor]

theorem cubicForm_div_eq_tensorCubicPart (t : Fin d → Fin d → Fin d → ℝ) (y : Fin d → ℤ) :
    cubicForm t (latticeEuclideanEmbedding y) / 6 = tensorCubicPart t 0 y := by
  rw [tensorCubicPart, latticeEuclideanEmbedding_zero_vertex, sub_zero]

/-- Recentring: an element of `Ā_3` with tensor `t` is the cubic part `tensorCubicPart t z` plus a
lattice harmonic quadratic function, for every `z`. -/
theorem sub_tensorCubicPart_mem_latticeHarmonicQuadratic [NeZero d] {v : latticeComponent d → ℝ}
    {t : Fin d → Fin d → Fin d → ℝ} (ht : IsSymmTensor t) (htr : ∀ k, tensorTrace t k = 0)
    (hq : (fun x => v x - cubicForm t (latticeEuclideanEmbedding x.val) / 6) ∈
      latticeHarmonicQuadratic d) (z : Fin d → ℤ) :
    (fun x => v x - tensorCubicPart t z x.val) ∈ latticeHarmonicQuadratic d := by
  have hD : (fun x : latticeComponent d => cubicForm t (latticeEuclideanEmbedding x.val) / 6 -
      tensorCubicPart t z x.val) ∈ latticeHarmonicQuadratic d := by
    refine ⟨?_, fun y => ?_⟩
    · have := (clusterQuadratic (latticeComponent d)).neg_mem
        (tensorCubicPart_sub_mem_clusterQuadratic ht z)
      convert this using 1
      funext x
      simp only [Pi.neg_apply]
      ring
    · have e : latticeExt (fun x : latticeComponent d =>
          cubicForm t (latticeEuclideanEmbedding x.val) / 6 - tensorCubicPart t z x.val) =
          fun y => tensorCubicPart t 0 y - tensorCubicPart t z y := by
        funext y
        simp only [latticeExt, cubicForm_div_eq_tensorCubicPart]
      rw [e, latticeLaplacian_sub, latticeLaplacian_tensorCubicPart ht,
        latticeLaplacian_tensorCubicPart ht]
      simp [htr]
  convert (latticeHarmonicQuadratic d).add_mem hq hD using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- The elements of `Ā_3` are lattice harmonic. -/
theorem latticeLaplacian_latticeExt_eq_zero [NeZero d] {v : latticeComponent d → ℝ}
    (hv : v ∈ latticeHarmonicCubicPoly d) (y : Fin d → ℤ) :
    latticeLaplacian (latticeExt v) y = 0 := by
  obtain ⟨t, ht, htr, hq⟩ := hv
  have e : latticeExt v = fun y => latticeExt (fun x => v x -
      cubicForm t (latticeEuclideanEmbedding x.val) / 6) y + tensorCubicPart t 0 y := by
    funext y
    simp only [latticeExt, cubicForm_div_eq_tensorCubicPart]
    ring
  rw [e, latticeLaplacian_add, hq.2 y, latticeLaplacian_tensorCubicPart ht]
  simp [htr]

/-- The third forward differences of an element of `Ā_3` are the entries of its tensor. -/
theorem fwd_fwd_fwd_latticeExt [NeZero d] {v : latticeComponent d → ℝ}
    {t : Fin d → Fin d → Fin d → ℝ} (ht : IsSymmTensor t)
    (hq : (fun x => v x - cubicForm t (latticeEuclideanEmbedding x.val) / 6) ∈
      clusterQuadratic (latticeComponent d)) (a b e : Fin d) (y : Fin d → ℤ) :
    fwd e (fwd b (fwd a (latticeExt v))) y = t a b e := by
  have e1 : latticeExt v = fun y => latticeExt (fun x => v x -
      cubicForm t (latticeEuclideanEmbedding x.val) / 6) y + tensorCubicPart t 0 y := by
    funext y
    simp only [latticeExt, cubicForm_div_eq_tensorCubicPart]
    ring
  rw [e1, fwd_add, fwd_add, fwd_add]
  simp only
  rw [fwd_fwd_fwd_latticeExt_of_mem_clusterQuadratic hq, fwd_fwd_fwd_tensorCubicPart ht, zero_add]

theorem tensorCubicPart_sub (t t' : Fin d → Fin d → Fin d → ℝ) (c y : Fin d → ℤ) :
    tensorCubicPart (t - t') c y = tensorCubicPart t c y - tensorCubicPart t' c y := by
  simp only [tensorCubicPart, cubicForm, cubicMixed_sub_tensor]
  ring

/-- A cubic part with a symmetric trace-free tensor is a lattice harmonic cubic polynomial. -/
theorem tensorCubicPart_mem_latticeHarmonicCubicPoly [NeZero d] {t : Fin d → Fin d → Fin d → ℝ}
    (ht : IsSymmTensor t) (htr : ∀ k, tensorTrace t k = 0) (c : Fin d → ℤ) :
    (fun x : latticeComponent d => tensorCubicPart t c x.val) ∈ latticeHarmonicCubicPoly d := by
  refine ⟨t, ht, htr, tensorCubicPart_sub_mem_clusterQuadratic ht c, fun y => ?_⟩
  have e : latticeExt (fun x : latticeComponent d => tensorCubicPart t c x.val -
      cubicForm t (latticeEuclideanEmbedding x.val) / 6) =
      fun y => tensorCubicPart t c y - tensorCubicPart t 0 y := by
    funext y
    simp only [latticeExt, cubicForm_div_eq_tensorCubicPart]
  rw [e, latticeLaplacian_sub, latticeLaplacian_tensorCubicPart ht,
    latticeLaplacian_tensorCubicPart ht]
  simp [htr]

end Rigidity.Proofs.Regularity
