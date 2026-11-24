import LatticeProb.Network.BarrierMaximum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homotopy.Path
import PercolationClusterHomogenization.Proofs.Planar.WindingNumber
import PercolationClusterHomogenization.Proofs.Planar.LoopFromCrossings

/-!
# Lemma 5.19: many disjoint paths from `γ` to the support of `u`

This file proves `ManyPathsStep` (`step:5.19-many-paths`, corrected draft L2040-2043). No
literature input is used: the only planar topology is the following
discrete fact about the winding number `windingNumber` of Lemma 5.14.

* `exists_eq_of_crossing`: a lattice loop in the annulus `Q_{2m} \ Q_m` with nonzero winding
  number around the origin meets every lattice path from `Q_m` to the complement of `Q_{2m}`.
  Its proof uses the sum `windAt β y` of the angle increments of the loop `β` seen from `y`. For
  adjacent lattice points `y`, `y'` off the loop, the increment `θ(y) - θ(y')` along a unit step
  `a → b` of the loop equals `h(b) - h(a)` with `h(p) = arg ((p - y) / (p - y'))`: the two sides
  agree modulo `2π`, and all four principal arguments lie in `(-π/2, π/2)` because two nonzero
  lattice vectors differing by a unit vector have a positive inner product. Summing over the
  closed loop gives `windAt β y = windAt β y'` (`windAt_eq_of_step`). Far from the loop the
  increments telescope (`windAt_eq_zero_of_not_mem_cube`), and `windAt` is constant on `Q_m`.

At each scale `m = S₀ 2^j` the loop of Lemma 5.14 meets the path of Lemma 5.18 from `Q_R` to the
complement of `Q_{2m+1}`, where `u ≠ 0`, and the bi-infinite path `γ`, which visits `Q_R` and
leaves every cube. Walking along the loop from its meeting point with the path of Lemma 5.18 to
its first vertex on `γ` and
reversing gives an arc `ρ` from `γ(k)` to a vertex where `u ≠ 0`, meeting `γ` only at its initial
point (`exists_arc_of_loop`). As `S₀` exceeds the scale of the stretch of `γ` between its first
and last visits to `Q_R`, each `k` lies on one of the two tails of `γ`; infinitely many scales
share a tail, and `N` of them give the paths. Arcs at different scales lie in disjoint annuli.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-! ### The winding number of a lattice loop around a lattice point -/

/-- The sum of the angle increments of the closed lattice path `β 0, …, β n, β 0` seen from `y`.
At `y = 0` it is `2π` times `windingNumber β`. -/
noncomputable def windAt {n : ℕ} (β : Fin (n + 1) → Vertex 2) (y : Vertex 2) : ℝ :=
  ∑ i : Fin (n + 1),
    Complex.arg ((toComplex (β (i + 1)) - toComplex y) / (toComplex (β i) - toComplex y))

theorem toComplex_zero : toComplex 0 = 0 := by
  apply Complex.ext <;> simp [toComplex]

theorem windingNumber_eq_windAt {n : ℕ} (β : Fin (n + 1) → Vertex 2) :
    windingNumber β = windAt β 0 / (2 * Real.pi) := by
  simp only [windingNumber, windAt, toComplex_zero, sub_zero]

theorem vertex_eq_of_coords {a b : Vertex 2} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  funext i
  fin_cases i
  exacts [h0, h1]

theorem toComplex_injective : Function.Injective toComplex := fun a b h =>
  vertex_eq_of_coords
    (by exact_mod_cast (toComplex_re a).symm.trans ((congrArg Complex.re h).trans (toComplex_re b)))
    (by exact_mod_cast (toComplex_im a).symm.trans ((congrArg Complex.im h).trans (toComplex_im b)))

theorem toComplex_sub_ne_zero {a b : Vertex 2} (h : a ≠ b) : toComplex a - toComplex b ≠ 0 :=
  sub_ne_zero.2 (toComplex_injective.ne h)

theorem toComplex_sub' (a b : Vertex 2) :
    toComplex a - toComplex b = ⟨((a 0 - b 0 : ℤ) : ℝ), ((a 1 - b 1 : ℤ) : ℝ)⟩ := by
  apply Complex.ext <;> simp [toComplex]

/-- Nonzero integers `x`, `x' = x ± 1` (or `y ≠ 0`) give `x' x + y² > 0`. -/
theorem dot_pos_aux {x x' y : ℤ} (hx : x' = x + 1 ∨ x' = x - 1) (h1 : ¬(x = 0 ∧ y = 0))
    (h2 : ¬(x' = 0 ∧ y = 0)) : 0 < x' * x + y * y := by
  have hxx : 0 ≤ x' * x := by
    rcases (by omega : x ≤ -1 ∨ x = 0 ∨ 1 ≤ x) with h | h | h <;>
      rcases hx with rfl | rfl <;> nlinarith
  rcases eq_or_ne y 0 with rfl | hy
  · have := lt_of_le_of_ne hxx
      (mul_ne_zero (fun h => h2 ⟨h, rfl⟩) (fun h => h1 ⟨h, rfl⟩)).symm
    linarith
  · have := mul_self_pos.2 hy
    linarith

/-- Two nonzero lattice vectors `v`, `w` with `w - v` a unit vector have a positive inner
product. -/
theorem dot_pos_of_unit {v0 v1 w0 w1 : ℤ} (h : |v0 - w0| + |v1 - w1| = 1)
    (hv : ¬(v0 = 0 ∧ v1 = 0)) (hw : ¬(w0 = 0 ∧ w1 = 0)) : 0 < w0 * v0 + w1 * v1 := by
  have hc : ((w0 = v0 + 1 ∨ w0 = v0 - 1) ∧ w1 = v1) ∨
      (w0 = v0 ∧ (w1 = v1 + 1 ∨ w1 = v1 - 1)) := by
    rcases abs_cases (v0 - w0) with ⟨h0, _⟩ | ⟨h0, _⟩ <;>
      rcases abs_cases (v1 - w1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  rcases hc with ⟨hx, rfl⟩ | ⟨rfl, hy⟩
  · exact dot_pos_aux hx hv hw
  · have := dot_pos_aux (y := w0) hy (fun h => hv ⟨h.2, h.1⟩) (fun h => hw ⟨h.2, h.1⟩)
    linarith

/-- The quotient of two nonzero lattice vectors differing by a unit vector lies in the open
right half-plane. -/
theorem re_div_pos_of_int {v0 v1 w0 w1 : ℤ} (h : |v0 - w0| + |v1 - w1| = 1)
    (hv : ¬(v0 = 0 ∧ v1 = 0)) (hw : ¬(w0 = 0 ∧ w1 = 0)) :
    0 < ((⟨w0, w1⟩ : ℂ) / ⟨v0, v1⟩).re := by
  have hdot : (0 : ℝ) < (w0 : ℝ) * v0 + (w1 : ℝ) * v1 := by
    exact_mod_cast dot_pos_of_unit h hv hw
  have hns : (0 : ℝ) < (v0 : ℝ) * v0 + (v1 : ℝ) * v1 := by
    have : 0 < v0 * v0 + v1 * v1 := by
      rcases not_and_or.1 hv with h0 | h0
      · have := mul_self_pos.2 h0
        nlinarith [mul_self_nonneg v1]
      · have := mul_self_pos.2 h0
        nlinarith [mul_self_nonneg v0]
    exact_mod_cast this
  rw [Complex.div_re, ← add_div, Complex.normSq_mk]
  exact div_pos hdot hns

/-- For lattice points with `(a - c) - (b - d)` a unit vector, `a ≠ c` and `b ≠ d`, the quotient
`(b - d) / (a - c)` lies in the open right half-plane. -/
theorem re_div_pos {a b c d : Vertex 2}
    (h : |(a 0 - c 0) - (b 0 - d 0)| + |(a 1 - c 1) - (b 1 - d 1)| = 1) (hac : a ≠ c)
    (hbd : b ≠ d) : 0 < ((toComplex b - toComplex d) / (toComplex a - toComplex c)).re := by
  rw [toComplex_sub', toComplex_sub']
  exact re_div_pos_of_int h (fun h' => hac (vertex_eq_of_coords (by omega) (by omega)))
    (fun h' => hbd (vertex_eq_of_coords (by omega) (by omega)))

/-- Principal arguments in `(-π/2, π/2)`: `arg (B/A) - arg (B'/A') = arg (B/B') - arg (A/A')`,
both sides agreeing modulo `2π`. -/
theorem arg_div_sub_arg_div {A B A' B' : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hA' : A' ≠ 0)
    (hB' : B' ≠ 0) (h1 : 0 < (B / A).re) (h2 : 0 < (B' / A').re) (h3 : 0 < (B / B').re)
    (h4 : 0 < (A / A').re) :
    Complex.arg (B / A) - Complex.arg (B' / A') =
      Complex.arg (B / B') - Complex.arg (A / A') := by
  have e1 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h1))
  have e2 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h2))
  have e3 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h3))
  have e4 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h4))
  have key : ((Complex.arg (B / A) - Complex.arg (B' / A') : ℝ) : Real.Angle) =
      ((Complex.arg (B / B') - Complex.arg (A / A') : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub, Complex.arg_div_coe_angle hB hA,
      Complex.arg_div_coe_angle hB' hA', Complex.arg_div_coe_angle hB hB',
      Complex.arg_div_coe_angle hA hA']
    abel
  have := congrArg Real.Angle.toReal key
  rwa [Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩,
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩] at this

theorem abs_add_abs_of_latticeL1Dist {a b : Vertex 2} (h : latticeL1Dist a b = 1) :
    |a 0 - b 0| + |a 1 - b 1| = 1 := by
  simpa [latticeL1Dist, Fin.sum_univ_two] using h

/-- Adjacent lattice points off a lattice loop see it with the same winding number. -/
theorem windAt_eq_of_step {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) {y y' : Vertex 2}
    (hyy : latticeL1Dist y y' = 1) (hy : ∀ i, β i ≠ y) (hy' : ∀ i, β i ≠ y') :
    windAt β y = windAt β y' := by
  set g : Fin (n + 1) → ℝ := fun i =>
    Complex.arg ((toComplex (β i) - toComplex y) / (toComplex (β i) - toComplex y')) with hg
  have hstep : ∀ i, |(β i 0 - y 0) - (β (i + 1) 0 - y 0)| +
      |(β i 1 - y 1) - (β (i + 1) 1 - y 1)| = 1 := fun i => by
    simp only [sub_sub_sub_cancel_right]
    exact abs_add_abs_of_latticeL1Dist (hβ i)
  have hstep' : ∀ i, |(β i 0 - y' 0) - (β (i + 1) 0 - y' 0)| +
      |(β i 1 - y' 1) - (β (i + 1) 1 - y' 1)| = 1 := fun i => by
    simp only [sub_sub_sub_cancel_right]
    exact abs_add_abs_of_latticeL1Dist (hβ i)
  have hmove : ∀ p : Vertex 2, |(p 0 - y' 0) - (p 0 - y 0)| + |(p 1 - y' 1) - (p 1 - y 1)| = 1 :=
    fun p => by
      simp only [sub_sub_sub_cancel_left]
      exact abs_add_abs_of_latticeL1Dist hyy
  have key : ∀ i, Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
        (toComplex (β i) - toComplex y)) -
      Complex.arg ((toComplex (β (i + 1)) - toComplex y') / (toComplex (β i) - toComplex y')) =
      g (i + 1) - g i := fun i =>
    arg_div_sub_arg_div (toComplex_sub_ne_zero (hy i)) (toComplex_sub_ne_zero (hy (i + 1)))
      (toComplex_sub_ne_zero (hy' i)) (toComplex_sub_ne_zero (hy' (i + 1)))
      (re_div_pos (hstep i) (hy i) (hy (i + 1))) (re_div_pos (hstep' i) (hy' i) (hy' (i + 1)))
      (re_div_pos (hmove _) (hy' (i + 1)) (hy (i + 1))) (re_div_pos (hmove _) (hy' i) (hy i))
  have hsum : ∑ i, (Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
        (toComplex (β i) - toComplex y)) -
      Complex.arg ((toComplex (β (i + 1)) - toComplex y') / (toComplex (β i) - toComplex y'))) =
      ∑ i, (g (i + 1) - g i) := Finset.sum_congr rfl fun i _ => key i
  rw [← sub_eq_zero, windAt, windAt, ← Finset.sum_sub_distrib, hsum, Finset.sum_sub_distrib,
    sub_eq_zero]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) g

/-- If the loop lies in an open half-plane `{z : Re (c (z - y)) > 0}`, its increments seen from
`y` telescope and `windAt` vanishes. -/
theorem windAt_eq_zero_of_re_pos {n : ℕ} {β : Fin (n + 1) → Vertex 2} {y : Vertex 2} (c : ℂ)
    (hc : ∀ i, 0 < (c * (toComplex (β i) - toComplex y)).re) : windAt β y = 0 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simpa using hc 0
  set g : Fin (n + 1) → ℝ := fun i => Complex.arg (c * (toComplex (β i) - toComplex y)) with hg
  have key : ∀ i, Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
      (toComplex (β i) - toComplex y)) = g (i + 1) - g i := by
    intro i
    rw [← mul_div_mul_left (toComplex (β (i + 1)) - toComplex y) _ hc0]
    exact arg_div_of_re_pos (hc i) (hc (i + 1))
  have hsum : ∑ i, Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
      (toComplex (β i) - toComplex y)) = ∑ i, (g (i + 1) - g i) :=
    Finset.sum_congr rfl fun i _ => key i
  rw [windAt, hsum, Finset.sum_sub_distrib, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) g

/-- Outside a cube containing the loop, `windAt` vanishes. -/
theorem windAt_eq_zero_of_not_mem_cube {n : ℕ} {β : Fin (n + 1) → Vertex 2} {M : ℕ}
    {y : Vertex 2} (hβ : ∀ i, β i ∈ cube M) (hy : y ∉ cube M) : windAt β y = 0 := by
  have hy' : ¬ |y 0| ≤ M ∨ ¬ |y 1| ≤ M := by
    by_contra h
    push Not at h
    exact hy fun i => by fin_cases i <;> [exact h.1; exact h.2]
  rcases hy' with h | h <;> rw [abs_le, not_and_or] at h <;> push Not at h
  · rcases h with h | h
    · refine windAt_eq_zero_of_re_pos 1 fun i => ?_
      have := (abs_le.1 (hβ i 0)).1
      have : (y 0 : ℝ) < β i 0 := by exact_mod_cast (by omega : y 0 < β i 0)
      simp [toComplex]
      linarith
    · refine windAt_eq_zero_of_re_pos (-1) fun i => ?_
      have := (abs_le.1 (hβ i 0)).2
      have : (β i 0 : ℝ) < y 0 := by exact_mod_cast (by omega : β i 0 < y 0)
      simp [toComplex]
      linarith
  · rcases h with h | h
    · refine windAt_eq_zero_of_re_pos (-Complex.I) fun i => ?_
      have := (abs_le.1 (hβ i 1)).1
      have : (y 1 : ℝ) < β i 1 := by exact_mod_cast (by omega : y 1 < β i 1)
      simp [toComplex]
      linarith
    · refine windAt_eq_zero_of_re_pos Complex.I fun i => ?_
      have := (abs_le.1 (hβ i 1)).2
      have : (β i 1 : ℝ) < y 1 := by exact_mod_cast (by omega : β i 1 < y 1)
      simp [toComplex]
      linarith

/-- `windAt` is constant along a lattice line `g` off the loop. -/
theorem windAt_eq_of_line {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) (g : ℤ → Vertex 2)
    (hg : ∀ k, latticeL1Dist (g k) (g (k + 1)) = 1) (lo : ℤ) :
    ∀ k : ℕ, (∀ j : ℕ, j ≤ k → ∀ i, β i ≠ g (lo + j)) →
      windAt β (g lo) = windAt β (g (lo + k)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hoff
    rw [ih fun j hj => hoff j (by omega)]
    have := windAt_eq_of_step hβ (hg (lo + k)) (hoff k (by omega))
      (by simpa [add_assoc] using hoff (k + 1) le_rfl)
    simpa [add_assoc] using this

/-- `windAt` is constant on a cube `Q_m` avoided by the loop. -/
theorem windAt_eq_of_mem_cube {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) {m : ℕ} (hout : ∀ i, β i ∉ cube m)
    {x : Vertex 2} (hx : x ∈ cube m) : windAt β x = windAt β 0 := by
  have hoff : ∀ v : Vertex 2, |v 0| ≤ m → |v 1| ≤ m → ∀ i, β i ≠ v := by
    intro v h0 h1 i h
    apply hout i
    rw [h]
    intro j
    fin_cases j
    exacts [h0, h1]
  have h0 := abs_le.1 (hx 0)
  have h1 := abs_le.1 (hx 1)
  have hvert : ∀ a k : ℤ, latticeL1Dist (![a, k] : Vertex 2) ![a, k + 1] = 1 := fun a k => by
    simp [latticeL1Dist, Fin.sum_univ_two]
  have hhor : ∀ k : ℤ, latticeL1Dist (![k, 0] : Vertex 2) ![k + 1, 0] = 1 := fun k => by
    simp [latticeL1Dist, Fin.sum_univ_two]
  have hv : windAt β ![x 0, 0] = windAt β ![x 0, x 1] := by
    rcases le_total 0 (x 1) with h | h
    · have := windAt_eq_of_line hβ (fun k => ![x 0, k]) (fun k => hvert _ k) 0 (x 1).toNat
        fun j hj i => hoff ![x 0, 0 + (j : ℤ)] (hx 0) (show |(0 : ℤ) + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩) i
      simpa [Int.toNat_of_nonneg h] using this
    · have := windAt_eq_of_line hβ (fun k => ![x 0, k]) (fun k => hvert _ k) (x 1) (-x 1).toNat
        fun j hj i => hoff ![x 0, x 1 + (j : ℤ)] (hx 0) (show |x 1 + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩) i
      have he : x 1 + ((-x 1).toNat : ℤ) = 0 := by omega
      rw [he] at this
      exact this.symm
  have hh : windAt β ![0, 0] = windAt β ![x 0, 0] := by
    rcases le_total 0 (x 0) with h | h
    · have := windAt_eq_of_line hβ (fun k => ![k, 0]) hhor 0 (x 0).toNat
        fun j hj i => hoff ![0 + (j : ℤ), 0] (show |(0 : ℤ) + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩)
          (show |(0 : ℤ)| ≤ m by simp) i
      simpa [Int.toNat_of_nonneg h] using this
    · have := windAt_eq_of_line hβ (fun k => ![k, 0]) hhor (x 0) (-x 0).toNat
        fun j hj i => hoff ![x 0 + (j : ℤ), 0] (show |x 0 + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩)
          (show |(0 : ℤ)| ≤ m by simp) i
      have he : x 0 + ((-x 0).toNat : ℤ) = 0 := by omega
      rw [he] at this
      exact this.symm
  have hx' : (![x 0, x 1] : Vertex 2) = x := vertex_eq_of_coords rfl rfl
  have hz : (![0, 0] : Vertex 2) = 0 := vertex_eq_of_coords rfl rfl
  calc windAt β x = windAt β ![x 0, x 1] := by rw [hx']
    _ = windAt β ![x 0, 0] := hv.symm
    _ = windAt β ![0, 0] := hh.symm
    _ = windAt β 0 := by rw [hz]

/-- **The crossing lemma.** A lattice loop in `Q_{2m} \ Q_m` with nonzero winding number around
the origin meets every lattice path from `Q_m` to the complement of `Q_{2m}`. -/
theorem exists_eq_of_crossing {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) {m : ℕ}
    (hβm : ∀ i, β i ∈ cube (2 * m) \ cube m) (hw : windAt β 0 ≠ 0) {P : ℕ → Vertex 2} {L : ℕ}
    (hP : ∀ i < L, latticeL1Dist (P i) (P (i + 1)) = 1) (h0 : P 0 ∈ cube m)
    (hL : P L ∉ cube (2 * m)) : ∃ i ≤ L, ∃ t, β t = P i := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ i ≤ L, windAt β (P i) = windAt β (P 0) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [← ih (by omega)]
      exact (windAt_eq_of_step hβ (hP i (by omega)) (hcon i (by omega))
        (hcon (i + 1) hi)).symm
  apply hw
  rw [← windAt_eq_of_mem_cube hβ (fun i => (hβm i).2) h0, ← hconst L le_rfl]
  exact windAt_eq_zero_of_not_mem_cube (fun i => (hβm i).1) hL

/-! ### Arcs of the loops from `γ` to the support of `u` -/

variable {ω : Configuration 2}

theorem latticeL1Dist_eq_one_of_adj {C : OpenComponent ω} {x y : C}
    (h : (componentGraph C).Adj x y) : latticeL1Dist x.val y.val = 1 :=
  lattice_adj_iff_l1Dist.1 ((C.toSimpleGraph_adj x.2 y.2).1 h).1

open Fin.NatCast

end Rigidity.Proofs.Section5
