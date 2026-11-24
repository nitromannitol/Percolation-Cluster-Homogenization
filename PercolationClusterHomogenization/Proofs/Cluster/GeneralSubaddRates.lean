import PercolationClusterHomogenization.Proofs.Cluster.GeneralSubaddTail

/-!
# Rates for Proposition 5.2 from Lemma 5.11, in every dimension

Elementary bounds used to pass from the tail form of Lemma 5.11 (`exists_cubeRho_tail_of_decay`)
to the tails of the good event of Proposition 5.2:

* the constants of the bounds on the event of small partition cubes are polynomial in `w = 3^ℓ`:
  `C₁(ℓ) ≤ A w^{2d}` (`cubeRhoCap_le`), `C(ℓ) ≤ A w^{2d+1}` (`rhoSubaddConst_le`) and
  `Yc(ℓ) ≤ A w^d` (`comparisonCap_le`);
* `X^k exp(-a X) ≤ k! (2/a)^k exp(-a X / 2)` for `X ≥ 0` (`pow_mul_exp_neg_mul_le`), which absorbs
  the volume factors of the probabilities into a stretched exponential;
* `√(x^n) = (√x)^n` (`sqrt_pow_eq`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

theorem one_le_three_pow_pow (ℓ k : ℕ) : (1 : ℝ) ≤ ((3 : ℝ) ^ ℓ) ^ k :=
  one_le_pow₀ (one_le_pow₀ (by norm_num))

theorem three_pow_pow_le_pow {ℓ k k' : ℕ} (h : k ≤ k') :
    ((3 : ℝ) ^ ℓ) ^ k ≤ ((3 : ℝ) ^ ℓ) ^ k' :=
  pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) h

theorem cubeRhoCap_le (S : ℝ) (ℓ : ℕ) :
    cubeRhoCap d S ℓ ≤ (3 ^ d / 4 * S ^ 2 * d + d * d * coarseGradConstant d ^ 2 + 1) *
      ((3 : ℝ) ^ ℓ) ^ (2 * d) := by
  unfold cubeRhoCap
  have h1 := one_le_three_pow_pow ℓ (2 * d)
  have h2 : ((3 : ℝ) ^ ℓ) ^ (2 * (d - 1)) ≤ ((3 : ℝ) ^ ℓ) ^ (2 * d) :=
    three_pow_pow_le_pow (by omega)
  have ha : 0 ≤ (3 : ℝ) ^ d / 4 * S ^ 2 * d := by positivity
  have hb : 0 ≤ (d : ℝ) * d * coarseGradConstant d ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem rhoSubaddConst_le (S : ℝ) (ℓ : ℕ) :
    rhoSubaddConst d S ℓ ≤ d * (muSubaddConst d * (1 + 8 * d * Real.exp 1) / 2 +
      3 ^ d / 4 * S ^ 2 * (8 * d * Real.exp 1 + 1)) * ((3 : ℝ) ^ ℓ) ^ (2 * d + 1) := by
  unfold rhoSubaddConst
  set w : ℝ := (3 : ℝ) ^ ℓ with hw
  have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
  have hκ : 2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) ≤ 8 * d * Real.exp 1 * w := by
    rw [pow_succ, ← hw]
    have : (0 : ℝ) ≤ 2 * d * Real.exp 1 := by positivity
    nlinarith
  have hκ0 : 0 ≤ 2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) := by positivity
  have p1 : w ^ (2 * (d - 1)) ≤ w ^ (2 * d + 1) := three_pow_pow_le_pow (by omega)
  have p2 : w ^ (2 * d) * w = w ^ (2 * d + 1) := by rw [pow_succ]
  have p3 : w ≤ w ^ (2 * d + 1) := by
    have := three_pow_pow_le_pow (ℓ := ℓ) (show 1 ≤ 2 * d + 1 by omega)
    rwa [pow_one] at this
  have hmu := muSubaddConst_nonneg d
  have hS2 : 0 ≤ (3 : ℝ) ^ d / 4 * S ^ 2 := by positivity
  have k1 : w ^ (2 * d) * (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1)) ≤
      8 * d * Real.exp 1 * w ^ (2 * d + 1) := by
    rw [← p2]
    have := mul_le_mul_of_nonneg_left hκ (by positivity : (0 : ℝ) ≤ w ^ (2 * d))
    nlinarith
  have k2 : 2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) + 1 ≤
      (8 * d * Real.exp 1 + 1) * w ^ (2 * d + 1) := by
    have h1 : 1 ≤ w ^ (2 * d + 1) := one_le_three_pow_pow ℓ _
    have h8 : 0 ≤ 8 * d * Real.exp 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left p3 h8]
  have k3 : muSubaddConst d * (w ^ (2 * (d - 1)) + w ^ (2 * d) *
      (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1))) ≤
      muSubaddConst d * ((1 + 8 * d * Real.exp 1) * w ^ (2 * d + 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hmu
  have k4 := mul_le_mul_of_nonneg_left k2 hS2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have k5 : muSubaddConst d * (w ^ (2 * (d - 1)) + w ^ (2 * d) *
      (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1))) / 2 +
      3 ^ d / 4 * S ^ 2 * (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) + 1) ≤
      (muSubaddConst d * (1 + 8 * d * Real.exp 1) / 2 +
        3 ^ d / 4 * S ^ 2 * (8 * d * Real.exp 1 + 1)) * w ^ (2 * d + 1) := by
    nlinarith
  calc (d : ℝ) * (muSubaddConst d * (w ^ (2 * (d - 1)) + w ^ (2 * d) *
        (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1))) / 2 +
        3 ^ d / 4 * S ^ 2 * (2 * d * Real.exp 1 * ((3 : ℝ) ^ (ℓ + 1) + 1) + 1))
      ≤ d * ((muSubaddConst d * (1 + 8 * d * Real.exp 1) / 2 +
        3 ^ d / 4 * S ^ 2 * (8 * d * Real.exp 1 + 1)) * w ^ (2 * d + 1)) :=
        mul_le_mul_of_nonneg_left k5 hd0
    _ = _ := by ring

theorem comparisonCap_le (hd : 0 < d) (ℓ : ℕ) :
    comparisonCap d ℓ ≤ (1 + 2 * d + 2 * 3 ^ d * √(4 * d * d * Real.exp 1)) *
      ((3 : ℝ) ^ ℓ) ^ d := by
  unfold comparisonCap
  set w : ℝ := (3 : ℝ) ^ ℓ with hw
  have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
  have hwd : w ≤ w ^ d := by
    have := three_pow_pow_le_pow (ℓ := ℓ) (show 1 ≤ d by omega)
    rwa [pow_one] at this
  have hwd1 : 1 ≤ w ^ d := one_le_three_pow_pow ℓ d
  have hin : (d : ℝ) * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (w + 1))))) ≤
      4 * d * d * Real.exp 1 * (w ^ d) ^ 2 := by
    have e1 : w ^ (2 * (d - 1)) * w ≤ (w ^ d) ^ 2 := by
      have hk : 2 * (d - 1) + 1 ≤ d * 2 := by omega
      calc w ^ (2 * (d - 1)) * w = w ^ (2 * (d - 1) + 1) := (pow_succ w _).symm
        _ ≤ w ^ (d * 2) := pow_le_pow_right₀ hw1 hk
        _ = (w ^ d) ^ 2 := pow_mul w d 2
    have e2 : w ^ (2 * (d - 1)) * (w + 1) ≤ 2 * (w ^ d) ^ 2 := by
      have : w ^ (2 * (d - 1)) ≤ w ^ (2 * (d - 1)) * w := le_mul_of_one_le_right (by positivity) hw1
      nlinarith
    have hde : (0 : ℝ) ≤ d * d * Real.exp 1 := by positivity
    have := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 2 * d * d * Real.exp 1)
    nlinarith
  have hsq : √((d : ℝ) * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (w + 1)))))) ≤
      √(4 * d * d * Real.exp 1) * w ^ d := by
    calc √((d : ℝ) * (w ^ (2 * (d - 1)) * (d * (Real.exp 1 * (2 * (w + 1))))))
        ≤ √(4 * d * d * Real.exp 1 * (w ^ d) ^ 2) := Real.sqrt_le_sqrt hin
      _ = √(4 * d * d * Real.exp 1) * w ^ d := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have k := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * 3 ^ d)
  have k2 := mul_le_mul_of_nonneg_left hwd (by positivity : (0 : ℝ) ≤ 2 * d)
  nlinarith

/-- `X^k exp(-a X) ≤ k! (2/a)^k exp(-a X / 2)` for `X ≥ 0` and `a > 0`. -/
theorem pow_mul_exp_neg_mul_le {a X : ℝ} (ha : 0 < a) (hX : 0 ≤ X) (k : ℕ) :
    X ^ k * Real.exp (-a * X) ≤ (k.factorial : ℝ) * (2 / a) ^ k * Real.exp (-(a / 2) * X) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * X) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf, mul_pow] at h
  have e1 : X ^ k = (2 / a) ^ k * ((a / 2) ^ k * X ^ k) := by
    rw [← mul_assoc, ← mul_pow, show 2 / a * (a / 2) = 1 by field_simp, one_pow, one_mul]
  rw [e1]
  calc (2 / a) ^ k * ((a / 2) ^ k * X ^ k) * Real.exp (-a * X)
      ≤ (2 / a) ^ k * (Real.exp (a / 2 * X) * k.factorial) * Real.exp (-a * X) := by
        gcongr
    _ = (k.factorial : ℝ) * (2 / a) ^ k * (Real.exp (a / 2 * X) * Real.exp (-a * X)) := by ring
    _ = (k.factorial : ℝ) * (2 / a) ^ k * Real.exp (-(a / 2) * X) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- `√(x^n) = (√x)^n` for `x ≥ 0`. -/
theorem sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : √(x ^ n) = (√x) ^ n := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
    Real.mul_self_sqrt hx]

/-- **The bound of Lemma 5.3 is geometrically small** once `(w^{4d+1} ρⁿ)² ≤ (λ₀ⁿ)⁴`: from
`T ≤ A_T w^{2d+1} ρⁿ`, `Y ≤ A_y w^d ρⁿ` and `Λ ≤ A_Λ w^{2d}`. -/
theorem minimalset_bound_le (hd : 0 < d) {T Y Λ S w ρ l A_T A_y A_Λ : ℝ} {n : ℕ}
    (hS : 0 ≤ S) (hw : 1 ≤ w) (hρ0 : 0 ≤ ρ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hT0 : 0 ≤ T) (hT : T ≤ A_T * (w ^ (2 * d + 1) * ρ ^ n))
    (hY0 : 0 ≤ Y) (hY : Y ≤ A_y * (w ^ d * ρ ^ n))
    (hΛ : Λ ≤ A_Λ * w ^ (2 * d))
    (hAT : 0 ≤ A_T) (hAy : 0 ≤ A_y) (hAΛ : 0 ≤ A_Λ)
    (hX : (w ^ (4 * d + 1) * ρ ^ n) ^ 2 ≤ (l ^ n) ^ 4) :
    T + d * Y * S + d / 2 * (2 * d * Y * S + √(4 * d * (Λ + 1) * (T + Y * S))) ≤
      (A_T + d * A_y * S + d / 2 * (2 * d * A_y * S +
        √(4 * d * (A_Λ + 1) * (A_T + A_y * S)))) * l ^ n := by
  set X : ℝ := w ^ (4 * d + 1) * ρ ^ n with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hln : 0 ≤ l ^ n := by positivity
  have hln1 : l ^ n ≤ 1 := pow_le_one₀ hl0 hl1
  have hXl : X ≤ (l ^ n) ^ 2 := by
    have h4 : (l ^ n) ^ 4 = ((l ^ n) ^ 2) ^ 2 := by ring
    rw [h4] at hX
    exact (sq_le_sq₀ hX0 (by positivity)).1 hX
  have hsX : √X ≤ l ^ n := by
    calc √X ≤ √((l ^ n) ^ 2) := Real.sqrt_le_sqrt hXl
      _ = l ^ n := Real.sqrt_sq hln
  have hX1 : X ≤ 1 := hXl.trans (by nlinarith)
  have hXs : X ≤ √X := by
    have h := Real.mul_self_sqrt hX0
    have hs0 := Real.sqrt_nonneg X
    have hs1 : √X ≤ 1 := by rw [Real.sqrt_le_one]; exact hX1
    nlinarith
  have hρn : 0 ≤ ρ ^ n := by positivity
  have hw1 : w ^ (2 * d + 1) * ρ ^ n ≤ X :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw (by omega)) hρn
  have hw2 : w ^ d * ρ ^ n ≤ X :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw (by omega)) hρn
  have hTX : T ≤ A_T * √X := hT.trans (mul_le_mul_of_nonneg_left (hw1.trans hXs) hAT)
  have hYX : Y ≤ A_y * √X := hY.trans (mul_le_mul_of_nonneg_left (hw2.trans hXs) hAy)
  have hin : 4 * d * (Λ + 1) * (T + Y * S) ≤
      4 * d * (A_Λ + 1) * (A_T + A_y * S) * X := by
    have h1 : Λ + 1 ≤ (A_Λ + 1) * w ^ (2 * d) := by
      have : 1 ≤ w ^ (2 * d) := one_le_pow₀ hw
      nlinarith
    have h2 : T + Y * S ≤ (A_T + A_y * S) * (w ^ (2 * d + 1) * ρ ^ n) := by
      have k : Y * S ≤ A_y * (w ^ (2 * d + 1) * ρ ^ n) * S :=
        mul_le_mul_of_nonneg_right (hY.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw (by omega)) hρn) hAy)) hS
      nlinarith
    have h3 : (A_Λ + 1) * w ^ (2 * d) * ((A_T + A_y * S) * (w ^ (2 * d + 1) * ρ ^ n)) =
        (A_Λ + 1) * (A_T + A_y * S) * X := by
      rw [hXdef, show 4 * d + 1 = 2 * d + (2 * d + 1) by ring, pow_add]
      ring
    have h4 := mul_le_mul h1 h2 (by positivity) (by positivity)
    rw [h3] at h4
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 4 * d)
    nlinarith
  have hsq : √(4 * d * (Λ + 1) * (T + Y * S)) ≤
      √(4 * d * (A_Λ + 1) * (A_T + A_y * S)) * √X := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hin
  have hA0 : 0 ≤ √(4 * d * (A_Λ + 1) * (A_T + A_y * S)) := Real.sqrt_nonneg _
  have k1 : d * Y * S ≤ d * (A_y * √X) * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYX (Nat.cast_nonneg d)) hS
  have k2 : 2 * d * Y * S ≤ 2 * d * (A_y * √X) * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYX (by positivity)) hS
  have k3 := mul_le_mul_of_nonneg_left (add_le_add k2 hsq) (by positivity : (0 : ℝ) ≤ d / 2)
  have hfin : T + d * Y * S + d / 2 * (2 * d * Y * S + √(4 * d * (Λ + 1) * (T + Y * S))) ≤
      (A_T + d * A_y * S + d / 2 * (2 * d * A_y * S +
        √(4 * d * (A_Λ + 1) * (A_T + A_y * S)))) * √X := by
    nlinarith
  refine hfin.trans (mul_le_mul_of_nonneg_left hsX ?_)
  positivity

end Rigidity.Percolation
