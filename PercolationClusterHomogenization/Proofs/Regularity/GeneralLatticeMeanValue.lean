import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# An `ℓ^∞`–`ℓ¹` bound for lattice harmonic functions on `ℤᵈ`

For `g` harmonic on the box `Q_{2L}(z)` of `ℤᵈ`, `L ≥ c_d = 4^{d+1}`,
`max_{Q_L(z)} |g| ≤ C L^{-d} ∑_{Q_{2L}(z)} |g|` (`abs_le_sum_abs_of_latticeHarmonicD`). The
interior bound `sq_le_of_latticeHarmonic` on a box `Q_{P h}(x₀)`, `P = 2 · 4^d`, gives
`g(x₀)² ≤ C₀ h^{-d} B S` with `B` a bound for `|g|` on the larger box and `S = ∑ |g|`, hence
`|g(x₀)| ≤ B / 2^{d+1} + 2^{d+1} C₀ h^{-d} S` (`abs_le_of_latticeHarmonic_stepD`); along the boxes
`Q_{j_k}(z)`, `j_k = L + P ∑_{i < k} h_i`, `h_k = ⌊L / (c_d 2^k)⌋`, the maxima `a_k` satisfy
`a_k ≤ a_{k+1} / 2^{d+1} + b_k`, and the absorption (`le_of_geometric_step`) over
`log₂(L / c_d) + 1` steps gives the bound, the factor `2^{-(d+1) k}` beating the growth `2^{d k}`
of `h_k^{-d}`. On the balls of `ℤᵈ`, with boxes centred at the points of the ball:
`‖g‖_{L̲²(B_ρ(z))} ≤ C ρ^{-d} ∑_{B_{4ρ}(z)} |g|` for `g` harmonic on `B_{4ρ}(z)`
(`componentBallL2_le_sum_abs_of_latticeHarmonicD`), the bound used to pass from `ℓ¹` to `ℓ²` in
the proof of Lemma 7.3 of Armstrong and Dario (arXiv:1609.09431v2). This is the argument of
`componentBallL2_le_sum_abs_of_latticeHarmonic` of the plane in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation

variable {d : ℕ}

theorem self_mem_supBox (z : Fin d → ℤ) (h : ℕ) : z ∈ supBox z h := by
  simp only [supBox, Fintype.mem_piFinset, mem_Icc]
  intro i; constructor <;> omega

theorem supBox_subset_supBox_of_mem {z x₀ : Fin d → ℤ} {j h L : ℕ} (hx₀ : x₀ ∈ supBox z j)
    (hjL : j + h ≤ L) : supBox x₀ h ⊆ supBox z L := by
  intro y hy
  simp only [supBox, Fintype.mem_piFinset, mem_Icc] at hy hx₀ ⊢
  intro i
  have h1 := hy i
  have h2 := hx₀ i
  constructor <;> omega

/-- The constant `4^d (64 d)^d` of the interior bound. -/
noncomputable def interiorConst (d : ℕ) : ℝ := 4 ^ d * (64 * d) ^ d

theorem interiorConst_nonneg (d : ℕ) : 0 ≤ interiorConst d := by
  unfold interiorConst; positivity

/-- **One absorption step.** -/
theorem abs_le_of_latticeHarmonic_stepD (g : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) {j h L : ℕ}
    (hh : 0 < h) (hjL : j + 4 ^ d * (2 * h) ≤ L)
    (hg : ∀ x ∈ supBox z L, latticeLaplacian g x = 0) {B : ℝ}
    (hB : ∀ y ∈ supBox z (j + 4 ^ d * (2 * h)), |g y| ≤ B) {x₀ : Fin d → ℤ}
    (hx₀ : x₀ ∈ supBox z j) :
    |g x₀| ≤ B / 2 ^ (d + 1) + 2 ^ (d + 1) * interiorConst d / (h : ℝ) ^ d *
      ∑ y ∈ supBox z L, |g y| := by
  have hsub : supBox x₀ (4 ^ d * (2 * h)) ⊆ supBox z (j + 4 ^ d * (2 * h)) :=
    supBox_subset_supBox_of_mem hx₀ le_rfl
  have hsubL : supBox x₀ (4 ^ d * (2 * h)) ⊆ supBox z L := supBox_subset_supBox_of_mem hx₀ hjL
  have h1 := sq_le_of_latticeHarmonic g x₀ hh (fun x hx => hg x (hsubL hx))
    (self_mem_supBox x₀ h)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x₀ (hsub (self_mem_supBox x₀ _)))
  set S := ∑ y ∈ supBox z L, |g y| with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  have hsq : ∑ x ∈ supBox x₀ (4 ^ d * (2 * h)), g x ^ 2 ≤ B * S := by
    calc ∑ x ∈ supBox x₀ (4 ^ d * (2 * h)), g x ^ 2 =
          ∑ x ∈ supBox x₀ (4 ^ d * (2 * h)), |g x| * |g x| :=
          sum_congr rfl fun x _ => by rw [← sq, sq_abs]
      _ ≤ ∑ x ∈ supBox x₀ (4 ^ d * (2 * h)), B * |g x| :=
          sum_le_sum fun x hx => mul_le_mul_of_nonneg_right (hB x (hsub hx)) (abs_nonneg _)
      _ = B * ∑ x ∈ supBox x₀ (4 ^ d * (2 * h)), |g x| := (mul_sum _ _ _).symm
      _ ≤ B * S := mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hsubL fun _ _ _ => abs_nonneg _) hB0
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hc : (4 : ℝ) ^ d * (64 * d) ^ d / ((h : ℝ) + 1) ^ d ≤ interiorConst d / (h : ℝ) ^ d :=
    div_le_div_of_nonneg_left (interiorConst_nonneg d) (by positivity)
      (pow_le_pow_left₀ hh'.le (by linarith) d)
  have h2 : g x₀ ^ 2 ≤ interiorConst d / (h : ℝ) ^ d * (B * S) :=
    h1.trans (mul_le_mul hc hsq (sum_nonneg fun _ _ => sq_nonneg _)
      (div_nonneg (interiorConst_nonneg d) (by positivity)))
  set a := B / 2 ^ (d + 1) with ha
  set b := 2 ^ (d + 1) * interiorConst d / (h : ℝ) ^ d * S with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by have := interiorConst_nonneg d; positivity
  have hab : interiorConst d / (h : ℝ) ^ d * (B * S) = a * b := by
    rw [ha, hb]; field_simp
  have hsq' : |g x₀| ^ 2 ≤ (a + b) ^ 2 := by
    rw [sq_abs]; nlinarith [sq_nonneg (a - b)]
  nlinarith [abs_nonneg (g x₀)]

/-- **Absorption.** If `a_k ≤ a_{k+1} / q + b_k` for `k < n`, then
`a_0 ≤ a_n / q^n + ∑_{k < n} b_k / q^k`. -/
theorem le_of_geometric_step {a b : ℕ → ℝ} {q : ℝ} (hq : 0 < q) (n : ℕ)
    (h : ∀ k < n, a k ≤ a (k + 1) / q + b k) :
    a 0 ≤ a n / q ^ n + ∑ k ∈ range n, b k / q ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih fun k hk => h k (by omega)
    have h2 := h n (by omega)
    have h8 : (0 : ℝ) < q ^ n := by positivity
    have h3 : a n / q ^ n ≤ a (n + 1) / q ^ (n + 1) + b n / q ^ n := by
      have := div_le_div_of_nonneg_right h2 h8.le
      rw [add_div, div_div, ← pow_succ'] at this
      exact this
    rw [sum_range_succ]
    linarith

/-- The side `c_d = 4^{d+1}` above which the box bound holds. -/
def meanValueSide (d : ℕ) : ℕ := 4 ^ d * 4

/-- The constant of the box bound. -/
noncomputable def meanValueConst (d : ℕ) : ℝ :=
  (meanValueSide d : ℝ) ^ d + 4 * 2 ^ (d + 1) * interiorConst d * (2 * meanValueSide d) ^ d

theorem meanValueConst_nonneg (d : ℕ) : 0 ≤ meanValueConst d := by
  have := interiorConst_nonneg d
  unfold meanValueConst; positivity

/-- **`ℓ^∞`–`ℓ¹` bound for lattice harmonic functions on the boxes of `ℤᵈ`.** -/
theorem abs_le_sum_abs_of_latticeHarmonicD (g : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ)
    {L : ℕ} (hL : meanValueSide d ≤ L)
    (hg : ∀ x ∈ supBox z (2 * L), latticeLaplacian g x = 0) :
    ∀ x ∈ supBox z L, |g x| ≤ meanValueConst d / (L : ℝ) ^ d * ∑ y ∈ supBox z (2 * L), |g y| := by
  classical
  set c := meanValueSide d with hcdef
  have hc4 : 4 ≤ c := by
    rw [hcdef, meanValueSide]; have := Nat.one_le_pow d 4 (by norm_num); omega
  have hcpos : 0 < c := by omega
  have hcr : (c : ℝ) = 4 ^ d * 4 := by rw [hcdef, meanValueSide]; push_cast; ring
  set S := ∑ y ∈ supBox z (2 * L), |g y| with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  have hL' : (c : ℝ) ≤ L := by exact_mod_cast hL
  have hcpos' : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hLpos : (0 : ℝ) < L := by linarith
  set K := Nat.log 2 (L / c) with hK
  have hLc : 1 ≤ L / c := (Nat.one_le_div_iff hcpos).2 hL
  have hpowK : 2 ^ K ≤ L / c := Nat.pow_log_le_self 2 (by omega)
  have hpowK1 : L / c < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  set hs : ℕ → ℕ := fun k => L / (c * 2 ^ k) with hhs
  have hs_pos : ∀ k ≤ K, 0 < hs k := by
    intro k hk
    have : c * 2 ^ k ≤ L := by
      have h1 : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hk
      have h2 := Nat.mul_le_of_le_div c _ _ hpowK
      nlinarith
    exact Nat.div_pos this (by positivity)
  have hs_le : ∀ k, (hs k : ℝ) ≤ L / (c * 2 ^ k) := by
    intro k
    have := Nat.cast_div_le (m := L) (n := c * 2 ^ k) (α := ℝ)
    simpa [hhs] using this
  have hs_ge : ∀ k ≤ K, (L : ℝ) / (2 * c * 2 ^ k) ≤ hs k := by
    intro k hk
    have hpos := hs_pos k hk
    have hlt : L < (hs k + 1) * (c * 2 ^ k) := by
      have := Nat.lt_succ_iff.2 (le_refl (L / (c * 2 ^ k)))
      exact (Nat.div_lt_iff_lt_mul (by positivity)).1 this
    have hlt' : (L : ℝ) < ((hs k : ℝ) + 1) * (c * 2 ^ k) := by exact_mod_cast hlt
    have h1 : (1 : ℝ) ≤ hs k := by exact_mod_cast hpos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set js : ℕ → ℕ := fun k => L + ∑ i ∈ range k, 4 ^ d * (2 * hs i) with hjs
  have hjs_succ : ∀ k, js (k + 1) = js k + 4 ^ d * (2 * hs k) := by
    intro k; simp only [hjs, sum_range_succ]; ring
  have hjs_le : ∀ k, js k ≤ 2 * L := by
    intro k
    have hsum : ((∑ i ∈ range k, 4 ^ d * (2 * hs i) : ℕ) : ℝ) ≤ L := by
      push_cast
      calc ∑ i ∈ range k, (4 : ℝ) ^ d * (2 * (hs i : ℝ))
          ≤ ∑ i ∈ range k, (L : ℝ) / 2 * (1 / 2) ^ i := by
            refine sum_le_sum fun i _ => ?_
            have h1 := hs_le i
            have e : (4 : ℝ) ^ d * (2 * ((L : ℝ) / (c * 2 ^ i))) = (L : ℝ) / 2 * (1 / 2) ^ i := by
              rw [hcr, one_div_pow]; field_simp; ring
            rw [← e]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (by positivity)
        _ = (L : ℝ) / 2 * ∑ i ∈ range k, (1 / 2 : ℝ) ^ i := (mul_sum _ _ _).symm
        _ ≤ (L : ℝ) / 2 * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have := sum_geometric_two_le k
            simpa [one_div] using this
        _ = L := by ring
    have : ((js k : ℕ) : ℝ) ≤ 2 * L := by
      simp only [hjs]; push_cast at hsum ⊢; linarith
    exact_mod_cast this
  -- the maxima of `|g|` on the boxes
  set as : ℕ → ℝ := fun k => (supBox z (js k)).sup' ⟨z, self_mem_supBox z _⟩ fun y => |g y|
    with has
  have has_ge : ∀ k, ∀ y ∈ supBox z (js k), |g y| ≤ as k := fun k y hy =>
    le_sup' (fun y => |g y|) hy
  set q : ℝ := 2 ^ (d + 1) with hq
  have hq0 : 0 < q := by positivity
  have hstep : ∀ k < K + 1, as k ≤ as (k + 1) / q +
      2 ^ (d + 1) * interiorConst d / (hs k : ℝ) ^ d * S := by
    intro k hk
    apply sup'_le
    intro x hx
    have hjL : js k + 4 ^ d * (2 * hs k) ≤ 2 * L := by rw [← hjs_succ]; exact hjs_le _
    exact abs_le_of_latticeHarmonic_stepD g z (hs_pos k (by omega)) hjL hg
      (B := as (k + 1)) (fun y hy => has_ge (k + 1) y (by rw [hjs_succ]; exact hy)) hx
  have habs := le_of_geometric_step (a := as)
    (b := fun k => 2 ^ (d + 1) * interiorConst d / (hs k : ℝ) ^ d * S) hq0 (K + 1) hstep
  -- the last maximum
  have hlast : as (K + 1) ≤ S := by
    apply sup'_le
    intro y hy
    have hy' : y ∈ supBox z (2 * L) := by
      simp only [supBox, Fintype.mem_piFinset, mem_Icc] at hy ⊢
      intro i; have := hy i; have := hjs_le (K + 1); constructor <;> omega
    exact single_le_sum (f := fun y => |g y|) (fun _ _ => abs_nonneg _) hy'
  have h2K : (L : ℝ) / c ≤ 2 ^ (K + 1) := by
    have h3 : (L : ℝ) / c < ((L / c : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := L) (b := c) hcpos
      have h4 : (L : ℝ) < ((L / c : ℕ) : ℝ) * c + c := by exact_mod_cast this
      rw [div_lt_iff₀ hcpos']; linarith
    have h5 : ((L / c : ℕ) : ℝ) + 1 ≤ 2 ^ (K + 1) := by
      have : L / c + 1 ≤ 2 ^ (K + 1) := hpowK1
      exact_mod_cast this
    linarith
  have hLc1 : 1 ≤ (L : ℝ) / c := by rw [le_div_iff₀ hcpos']; linarith
  have hqK : ((L : ℝ) / c) ^ d ≤ q ^ (K + 1) := by
    calc ((L : ℝ) / c) ^ d ≤ ((L : ℝ) / c) ^ (d + 1) := pow_le_pow_right₀ hLc1 (by omega)
      _ ≤ (2 ^ (K + 1)) ^ (d + 1) := pow_le_pow_left₀ (by positivity) h2K _
      _ = q ^ (K + 1) := by rw [hq, ← pow_mul, ← pow_mul, mul_comm]
  have hfirst : as (K + 1) / q ^ (K + 1) ≤ (c : ℝ) ^ d / (L : ℝ) ^ d * S := by
    have hqpos : (0 : ℝ) < q ^ (K + 1) := by positivity
    rw [div_le_iff₀ hqpos]
    calc as (K + 1) ≤ S := hlast
      _ = (c : ℝ) ^ d / (L : ℝ) ^ d * S * ((L : ℝ) / c) ^ d := by
          rw [div_pow]; field_simp
      _ ≤ (c : ℝ) ^ d / (L : ℝ) ^ d * S * q ^ (K + 1) :=
          mul_le_mul_of_nonneg_left hqK (by positivity)
  have hC0 := interiorConst_nonneg d
  have hsecond : ∑ k ∈ range (K + 1), 2 ^ (d + 1) * interiorConst d / (hs k : ℝ) ^ d * S / q ^ k ≤
      2 * (2 ^ (d + 1) * interiorConst d * (2 * c) ^ d) / (L : ℝ) ^ d * S := by
    have hterm : ∀ k ∈ range (K + 1), 2 ^ (d + 1) * interiorConst d / (hs k : ℝ) ^ d * S / q ^ k ≤
        2 ^ (d + 1) * interiorConst d * (2 * c) ^ d / (L : ℝ) ^ d * S * (1 / 2) ^ k := by
      intro k hk
      have hk' : k ≤ K := Nat.lt_succ_iff.1 (mem_range.1 hk)
      have hge := hs_ge k hk'
      have hpos : (0 : ℝ) < (L : ℝ) / (2 * c * 2 ^ k) := by positivity
      have hsq : 1 / (hs k : ℝ) ^ d ≤ 1 / ((L : ℝ) / (2 * c * 2 ^ k)) ^ d :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hge d)
      have e : 1 / ((L : ℝ) / (2 * c * 2 ^ k)) ^ d / q ^ k =
          (2 * c) ^ d / (L : ℝ) ^ d * (1 / 2) ^ k := by
        have hq' : q ^ k = ((2 : ℝ) ^ k) ^ d * 2 ^ k := by
          rw [hq, ← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
        rw [hq', div_pow, one_div_div, mul_pow, one_div_pow]
        field_simp
      have e2 : 2 ^ (d + 1) * interiorConst d / (hs k : ℝ) ^ d * S / q ^ k =
          2 ^ (d + 1) * interiorConst d * S * (1 / (hs k : ℝ) ^ d / q ^ k) := by ring
      rw [e2]
      calc 2 ^ (d + 1) * interiorConst d * S * (1 / (hs k : ℝ) ^ d / q ^ k)
          ≤ 2 ^ (d + 1) * interiorConst d * S * (1 / ((L : ℝ) / (2 * c * 2 ^ k)) ^ d / q ^ k) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity))
              (by positivity)
        _ = _ := by rw [e]; ring
    calc ∑ k ∈ range (K + 1), 2 ^ (d + 1) * interiorConst d / (hs k : ℝ) ^ d * S / q ^ k
        ≤ ∑ k ∈ range (K + 1),
            2 ^ (d + 1) * interiorConst d * (2 * c) ^ d / (L : ℝ) ^ d * S * (1 / 2) ^ k :=
          sum_le_sum hterm
      _ = 2 ^ (d + 1) * interiorConst d * (2 * c) ^ d / (L : ℝ) ^ d * S *
            ∑ k ∈ range (K + 1), (1 / 2 : ℝ) ^ k := (mul_sum _ _ _).symm
      _ ≤ 2 ^ (d + 1) * interiorConst d * (2 * c) ^ d / (L : ℝ) ^ d * S * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := sum_geometric_two_le (K + 1)
          simpa [one_div] using this
      _ = _ := by ring
  intro x hx
  have hx' : x ∈ supBox z (js 0) := by simpa [hjs] using hx
  have h0 := has_ge 0 x hx'
  have : as 0 ≤ meanValueConst d / (L : ℝ) ^ d * S := by
    refine habs.trans ?_
    have e : meanValueConst d / (L : ℝ) ^ d * S = (c : ℝ) ^ d / (L : ℝ) ^ d * S +
        2 * (2 * (2 ^ (d + 1) * interiorConst d * (2 * c) ^ d) / (L : ℝ) ^ d * S) := by
      rw [meanValueConst, ← hcdef]; ring
    rw [e]
    have hs2 : 0 ≤ 2 * (2 ^ (d + 1) * interiorConst d * (2 * c) ^ d) / (L : ℝ) ^ d * S := by
      positivity
    linarith
  exact h0.trans this

/-- The lower radius of the ball bound. -/
noncomputable def meanValueScale (d : ℕ) : ℝ := 2 * Real.sqrt d * (meanValueSide d + 1)

/-- **`ℓ²`–`ℓ¹` bound for lattice harmonic functions on the balls of `ℤᵈ`**: for `g` harmonic
on `B_{4ρ}(z)`, `ρ ≥ meanValueScale d`, `‖g‖_{L̲²(B_ρ(z))} ≤ C ρ^{-d} ∑_{B_{4ρ}(z)} |g|`. -/
theorem componentBallL2_le_sum_abs_of_latticeHarmonicD [NeZero d] (g : (Fin d → ℤ) → ℝ)
    (z : Vertex d) {ρ : ℝ} (hρ : meanValueScale d ≤ ρ)
    (hg : ∀ y : Fin d → ℤ, dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) <
      4 * ρ → latticeLaplacian g y = 0) :
    componentBallL2 (latticeComponent d) z ρ (fun x => g x.val) ≤
      meanValueConst d * (2 * Real.sqrt d) ^ d / ρ ^ d *
        ∑ x ∈ componentEuclideanBall (latticeComponent d) z (4 * ρ), |g x.val| := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hsd : 0 < Real.sqrt d := by linarith
  have hc0 : (0 : ℝ) ≤ meanValueSide d := Nat.cast_nonneg _
  have hρ0 : 0 < ρ := by
    have : 0 < meanValueScale d := by rw [meanValueScale]; positivity
    linarith
  set L := ⌊ρ / Real.sqrt d⌋₊ with hLdef
  have hLle : (L : ℝ) ≤ ρ / Real.sqrt d := Nat.floor_le (by positivity)
  have hLgt : ρ / Real.sqrt d < L + 1 := Nat.lt_floor_add_one _
  have hρs : 2 * (meanValueSide d + 1) ≤ ρ / Real.sqrt d := by
    rw [le_div_iff₀ hsd]; rw [meanValueScale] at hρ; linarith
  have hLc : meanValueSide d ≤ L := by
    have : (meanValueSide d : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hLge : ρ / (2 * Real.sqrt d) ≤ L := by
    have e : ρ / (2 * Real.sqrt d) = ρ / Real.sqrt d / 2 := by field_simp
    rw [e]; linarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLge
  have hsL : Real.sqrt d * L ≤ ρ := by
    have := mul_le_mul_of_nonneg_left hLle hsd.le
    rwa [mul_div_cancel₀ _ hsd.ne'] at this
  set S := ∑ x ∈ componentEuclideanBall (latticeComponent d) z (4 * ρ), |g x.val| with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  have hK : 0 ≤ meanValueConst d * (2 * Real.sqrt d) ^ d / ρ ^ d * S := by
    have := meanValueConst_nonneg d; positivity
  apply componentBallL2_le_of_abs_le _ _ _ hK
  intro x hx
  have hxz : dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding z) < ρ :=
    (mem_componentEuclideanBall _ _ _ _).1 hx
  have hnear : ∀ y ∈ supBox x.val (2 * L),
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < 4 * ρ := by
    intro y hy
    have h1 := dist_le_of_mem_supBox hy
    have h2 := dist_triangle (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding z)
    have h3 : Real.sqrt d * ((2 * L : ℕ) : ℝ) ≤ 2 * ρ := by push_cast; nlinarith
    linarith
  have hgbox : ∀ y ∈ supBox x.val (2 * L), latticeLaplacian g y = 0 := fun y hy =>
    hg y (hnear y hy)
  have hmax := abs_le_sum_abs_of_latticeHarmonicD g x.val hLc hgbox x.val
    (self_mem_supBox x.val L)
  have hSbox : ∑ y ∈ supBox x.val (2 * L), |g y| ≤ S := by
    have hmem : ∀ y : Fin d → ℤ, y ∈ (latticeComponent d).supp := mem_latticeComponent_supp
    rw [hS]
    calc ∑ y ∈ supBox x.val (2 * L), |g y|
        = ∑ x ∈ (supBox x.val (2 * L)).attach.map ⟨fun y => (⟨y.1, hmem y.1⟩ : latticeComponent d),
            fun a b h => Subtype.ext (congrArg Subtype.val h : _)⟩, |g x.val| := by
          rw [sum_map]; exact (sum_attach _ (fun y => |g y|)).symm
      _ ≤ ∑ x ∈ componentEuclideanBall (latticeComponent d) z (4 * ρ), |g x.val| := by
          apply sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => abs_nonneg _
          intro w hw
          rw [mem_map] at hw
          obtain ⟨y, _, rfl⟩ := hw
          rw [mem_componentEuclideanBall]
          exact hnear y.1 y.2
  have hLd : 1 / (L : ℝ) ^ d ≤ (2 * Real.sqrt d) ^ d / ρ ^ d := by
    rw [← div_pow, one_div, ← inv_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_le_comm₀ hLpos (by positivity), inv_div]
    exact hLge
  have hC := meanValueConst_nonneg d
  calc |g x.val| ≤ meanValueConst d / (L : ℝ) ^ d * ∑ y ∈ supBox x.val (2 * L), |g y| := hmax
    _ ≤ meanValueConst d / (L : ℝ) ^ d * S := mul_le_mul_of_nonneg_left hSbox (by positivity)
    _ = meanValueConst d * (1 / (L : ℝ) ^ d) * S := by ring
    _ ≤ meanValueConst d * ((2 * Real.sqrt d) ^ d / ρ ^ d) * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLd hC) hS0
    _ = meanValueConst d * (2 * Real.sqrt d) ^ d / ρ ^ d * S := by ring

end Rigidity.Proofs.Regularity
