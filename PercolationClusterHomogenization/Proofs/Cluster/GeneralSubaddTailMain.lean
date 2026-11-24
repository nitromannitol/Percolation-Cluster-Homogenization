import PercolationClusterHomogenization.Proofs.Cluster.GeneralSubaddRates

/-!
# Proposition 5.2 of Armstrong and Dario in every dimension, given the bound of Lemma 5.9:
stretched-exponential tails

`CubeSubaddGood p ω V K λ` says that the partition exists, resolves `V`, and
`|μ(V, q) + (1/2) q · ā⁻¹ q| ≤ K |q|² λ^{scale V}`,
`|ν(V, ā⁻¹ q) - (1/2) q · ā⁻¹ q| ≤ K |q|² λ^{scale V}` for all `q`. For the cubes `□_m` at the
origin its failure has probability at most `K' exp(-c (3^m)^s)`
(`exists_cubeSubaddGood_tail_of_decay`): with `n = ⌊m/2⌋`, `j = m - n - 3` and `ℓ = ⌊n/D⌋`, on the
event of Lemma 5.11 (`exists_cubeRho_tail_of_decay`) the partition cubes have scale at most `ℓ`,
`ρ(□_m)` is small, and Lemma 5.3 (`cubeSubaddGood_of_sizeLe`) gives the bounds; `D` is chosen so
that `9^{4d+1} ≤ ρ̃^{-D}`, `ρ̃ = max(r, 3^{-1/2})`, which makes the polynomial factors in `3^ℓ`
negligible (`minimalset_bound_le`). This is the content of Proposition 5.2 used in
Proposition 5.13, as in the two-dimensional `Rigidity.Proofs.Cluster.exists_planarSubaddGood_tail`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- `3^{-n/2} = (√3)⁻¹ⁿ`. -/
theorem one_div_sqrt_three_pow_eq (n : ℕ) : 1 / √((3 : ℝ) ^ n) = (√(3 : ℝ))⁻¹ ^ n := by
  rw [sqrt_three_pow, one_div, inv_pow]

/-- `((3^m)^s)` with `s = 1/(2D)`: its `2dD`-th power is `(3^m)^d`. -/
theorem three_pow_rpow_pow_eq (m d D : ℕ) (hD : 0 < D) :
    (((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ)))) ^ (2 * d * D) = ((3 : ℝ) ^ m) ^ d := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hexp : 1 / (2 * (D : ℝ)) * ((2 * d * D : ℕ) : ℝ) = (d : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]
    push_cast
    ring
  rw [← Real.rpow_natCast (((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ)))) (2 * d * D),
    ← Real.rpow_mul (by positivity), hexp, Real.rpow_natCast]

/-- `(3^m)^s ≤ 3^k` when `m ≤ 2 D k`, `s = 1/(2D)`. -/
theorem three_pow_rpow_le_three_pow {m D k : ℕ} (hD : 0 < D) (h : m ≤ 2 * D * k) :
    ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ))) ≤ (3 : ℝ) ^ k := by
  rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast (3 : ℝ) k]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h' : (m : ℝ) ≤ 2 * D * k := by exact_mod_cast h
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  linarith

/-- The small cubes: any probability is at most `(K₀ + exp(c' 3⁶)) exp(-c' (3^m)^s)` for
`m < 6`. -/
theorem measure_le_of_lt_six {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (E : Set Ω) {c' K₀ : ℝ} (hc' : 0 < c') (hK₀ : 0 ≤ K₀) {m D : ℕ}
    (hD : 0 < D) (hm : m < 6) :
    μ E ≤ ENNReal.ofReal ((K₀ + Real.exp (c' * 3 ^ 6)) *
      Real.exp (-c' * ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ))))) := by
  set X : ℝ := ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ))) with hX
  have hX0 : 0 ≤ X := by positivity
  have hX6 : X ≤ 3 ^ 6 := by
    have h1 : X ≤ (3 : ℝ) ^ m :=
      three_pow_rpow_le_three_pow hD (Nat.le_mul_of_pos_left m (by omega))
    exact h1.trans (pow_le_pow_right₀ (by norm_num) hm.le)
  refine prob_le_one.trans ?_
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 1 ≤ Real.exp (c' * 3 ^ 6) * Real.exp (-c' * X) := by
    rw [← Real.exp_add]
    refine Real.one_le_exp ?_
    have := mul_le_mul_of_nonneg_left hX6 hc'.le
    linarith
  have h2 : 0 ≤ K₀ * Real.exp (-c' * X) := by positivity
  linarith [show (K₀ + Real.exp (c' * 3 ^ 6)) * Real.exp (-c' * X) =
    K₀ * Real.exp (-c' * X) + Real.exp (c' * 3 ^ 6) * Real.exp (-c' * X) by ring]

/-- The threshold of Lemma 5.11 is at most `A_T w^{2d+1} ρⁿ`, `w = 3^ℓ`. -/
theorem threshold_le {C r ρ S : ℝ} {n ℓ : ℕ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hrρ : r ≤ ρ)
    (h3ρ : (√(3 : ℝ))⁻¹ ≤ ρ) :
    2 * (Real.exp 1 - 1) * (C + 1) * (1 + cubeRhoCap d S ℓ) * r ^ n +
        rhoSubaddConst d S ℓ * (1 / √((3 : ℝ) ^ n)) ≤
      (2 * (Real.exp 1 - 1) * (C + 1) *
          (1 + (3 ^ d / 4 * S ^ 2 * d + d * d * coarseGradConstant d ^ 2 + 1)) +
        d * (muSubaddConst d * (1 + 8 * d * Real.exp 1) / 2 +
          3 ^ d / 4 * S ^ 2 * (8 * d * Real.exp 1 + 1))) *
        (((3 : ℝ) ^ ℓ) ^ (2 * d + 1) * ρ ^ n) := by
  set w : ℝ := (3 : ℝ) ^ ℓ with hw
  have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
  set A_c : ℝ := 3 ^ d / 4 * S ^ 2 * d + d * d * coarseGradConstant d ^ 2 + 1 with hAc
  set A_s : ℝ := d * (muSubaddConst d * (1 + 8 * d * Real.exp 1) / 2 +
    3 ^ d / 4 * S ^ 2 * (8 * d * Real.exp 1 + 1)) with hAs
  have he1 : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hρ0 : 0 ≤ ρ := hr0.trans hrρ
  have hAc0 : 0 ≤ A_c := by positivity
  have k1 : 1 + cubeRhoCap d S ℓ ≤ (1 + A_c) * w ^ (2 * d + 1) := by
    have h1 := cubeRhoCap_le (d := d) S ℓ
    have h2 : w ^ (2 * d) ≤ w ^ (2 * d + 1) := pow_le_pow_right₀ hw1 (by omega)
    have h3 : 1 ≤ w ^ (2 * d + 1) := one_le_pow₀ hw1
    have := mul_le_mul_of_nonneg_left h2 hAc0
    nlinarith
  have k2 : rhoSubaddConst d S ℓ ≤ A_s * w ^ (2 * d + 1) := rhoSubaddConst_le S ℓ
  have k3 : r ^ n ≤ ρ ^ n := pow_le_pow_left₀ hr0 hrρ n
  have k4 : 1 / √((3 : ℝ) ^ n) ≤ ρ ^ n := by
    rw [one_div_sqrt_three_pow_eq]
    exact pow_le_pow_left₀ (by positivity) h3ρ n
  have hCs0 := rhoSubaddConst_nonneg d (S := S) ℓ
  have hcap0 : 0 ≤ 1 + cubeRhoCap d S ℓ := (cubeRhoCap_pos d S ℓ).le.trans (by linarith)
  have hE : 0 ≤ 2 * (Real.exp 1 - 1) * (C + 1) := by positivity
  have hW : 0 ≤ 2 * (Real.exp 1 - 1) * (C + 1) * ((1 + A_c) * w ^ (2 * d + 1)) :=
    mul_nonneg hE (mul_nonneg (by linarith) (by positivity))
  have t1 : 2 * (Real.exp 1 - 1) * (C + 1) * (1 + cubeRhoCap d S ℓ) * r ^ n ≤
      2 * (Real.exp 1 - 1) * (C + 1) * ((1 + A_c) * w ^ (2 * d + 1)) * ρ ^ n :=
    mul_le_mul (mul_le_mul_of_nonneg_left k1 hE) k3 (pow_nonneg hr0 n) hW
  have hAs0 : 0 ≤ A_s := by
    have := muSubaddConst_nonneg d
    positivity
  have t2 : rhoSubaddConst d S ℓ * (1 / √((3 : ℝ) ^ n)) ≤ A_s * w ^ (2 * d + 1) * ρ ^ n :=
    mul_le_mul k2 k4 (by positivity) (mul_nonneg hAs0 (by positivity))
  have e : (2 * (Real.exp 1 - 1) * (C + 1) * (1 + A_c) + A_s) * (w ^ (2 * d + 1) * ρ ^ n) =
      2 * (Real.exp 1 - 1) * (C + 1) * ((1 + A_c) * w ^ (2 * d + 1)) * ρ ^ n +
        A_s * w ^ (2 * d + 1) * ρ ^ n := by ring
  rw [e]
  linarith

/-- `(w^{4d+1} ρⁿ)² ≤ (lⁿ)⁴` for `w = 3^ℓ`, `ℓ = ⌊n/D⌋`, `9^{4d+1} ≤ ρ^{-D}` and `l⁴ = ρ`. -/
theorem pow_mul_pow_sq_le {ρ l : ℝ} {n D : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hD : (9 : ℝ) ^ (4 * d + 1) ≤ ρ⁻¹ ^ D) (hl4 : l ^ 4 = ρ) :
    ((((3 : ℝ) ^ (n / D)) ^ (4 * d + 1)) * ρ ^ n) ^ 2 ≤ (l ^ n) ^ 4 := by
  have hρi : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ0 |>.2 hρ1
  have e1 : (((3 : ℝ) ^ (n / D)) ^ (4 * d + 1)) ^ 2 = ((9 : ℝ) ^ (4 * d + 1)) ^ (n / D) := by
    rw [← pow_mul, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    ring_nf
  have e2 : ((9 : ℝ) ^ (4 * d + 1)) ^ (n / D) ≤ ρ⁻¹ ^ n := by
    calc ((9 : ℝ) ^ (4 * d + 1)) ^ (n / D) ≤ (ρ⁻¹ ^ D) ^ (n / D) :=
          pow_le_pow_left₀ (by positivity) hD _
      _ = ρ⁻¹ ^ (D * (n / D)) := by rw [← pow_mul]
      _ ≤ ρ⁻¹ ^ n := pow_le_pow_right₀ hρi (by rw [mul_comm]; exact Nat.div_mul_le_self n D)
  have e3 : ρ⁻¹ ^ n * (ρ ^ n) ^ 2 = (l ^ n) ^ 4 := by
    calc ρ⁻¹ ^ n * (ρ ^ n) ^ 2 = (ρ⁻¹ * ρ ^ 2) ^ n := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
      _ = ρ ^ n := by rw [show ρ⁻¹ * ρ ^ 2 = ρ by field_simp]
      _ = (l ^ n) ^ 4 := by rw [← hl4]; ring
  calc ((((3 : ℝ) ^ (n / D)) ^ (4 * d + 1)) * ρ ^ n) ^ 2 =
        (((3 : ℝ) ^ (n / D)) ^ (4 * d + 1)) ^ 2 * (ρ ^ n) ^ 2 := by ring
    _ ≤ ρ⁻¹ ^ n * (ρ ^ n) ^ 2 := by
        rw [e1]
        exact mul_le_mul_of_nonneg_right e2 (by positivity)
    _ = (l ^ n) ^ 4 := e3

/-- The comparison error of `□_m` on the event of small partition cubes is at most
`A_y 3^{dℓ} ρⁿ` for `n ≤ m` and `ρ ≥ 3^{-1/2}`. -/
theorem comparisonCap_mul_le (hd : 0 < d) {ρ : ℝ} {m n ℓ : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h3ρ : (√(3 : ℝ))⁻¹ ≤ ρ) (hnm : n ≤ m) :
    comparisonCap d ℓ * (1 / √((3 : ℝ) ^ m)) ≤
      (1 + 2 * d + 2 * 3 ^ d * √(4 * d * d * Real.exp 1)) * (((3 : ℝ) ^ ℓ) ^ d * ρ ^ n) := by
  have h1 := comparisonCap_le hd ℓ
  have h2 : 1 / √((3 : ℝ) ^ m) ≤ ρ ^ n := by
    rw [one_div_sqrt_three_pow_eq]
    exact (pow_le_pow_left₀ (by positivity) h3ρ m).trans (pow_le_pow_of_le_one hρ0.le hρ1 hnm)
  calc comparisonCap d ℓ * (1 / √((3 : ℝ) ^ m)) ≤
        (1 + 2 * d + 2 * 3 ^ d * √(4 * d * d * Real.exp 1)) * ((3 : ℝ) ^ ℓ) ^ d * ρ ^ n :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- **The probabilities of Lemma 5.11 at `n = ⌊m/2⌋`, `j = m - n - 3`, `ℓ = ⌊n/D⌋`** are at most
`K₀ exp(-c' (3^m)^{1/(2D)})`. -/
theorem lemma511_terms_le {a c C₂' c' r : ℝ} {m D : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hC₂' : 0 ≤ C₂') (hc'a : c' ≤ a / 2) (hc'c : c' ≤ c / 2) (hc'7 : c' ≤ 1 / 729)
    (hr13 : 1 / 3 ≤ r) (hd : 2 ≤ d) (hD2 : 2 ≤ D) (hm6 : 6 ≤ m) :
    ((3 : ℝ) ^ (m / 2 + 3 + (m - m / 2 - 3))) ^ d *
          (2 * Real.exp (-a * (3 : ℝ) ^ (m / 2 / D + 3))) +
        ((3 : ℝ) ^ (3 + (m - m / 2 - 3))) ^ d * (C₂' * Real.exp (-c * (3 : ℝ) ^ (m / 2))) +
        (27 : ℝ) ^ d * Real.exp (-(((3 : ℝ) ^ (m - m / 2 - 3)) ^ d * r ^ (m / 2))) ≤
      (2 * (((2 * d * D).factorial : ℝ) * (2 / a) ^ (2 * d * D)) +
          C₂' * (((2 * d * D).factorial : ℝ) * (2 / c) ^ (2 * d * D)) + 27 ^ d) *
        Real.exp (-c' * ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ)))) := by
  have hDpos : 0 < D := by omega
  set n := m / 2 with hn
  set j := m - n - 3 with hj
  set ℓ := n / D with hℓ
  set k := 2 * d * D with hk
  set X : ℝ := ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ))) with hX
  have hX0 : 0 ≤ X := by positivity
  have hm' : n + 3 + j = m := by omega
  have hk2 : ((3 : ℝ) ^ m) ^ d = X ^ k := by
    rw [hk, hX, three_pow_rpow_pow_eq m d D hDpos]
  have hXℓ : X ≤ (3 : ℝ) ^ (ℓ + 3) := by
    refine three_pow_rpow_le_three_pow hDpos ?_
    have h1 := Nat.lt_mul_div_succ n hDpos
    rw [← hℓ] at h1
    have h2 : 2 * D * (ℓ + 3) = 2 * (D * (ℓ + 1)) + 4 * D := by ring
    omega
  have hXn : X ≤ (3 : ℝ) ^ n := by
    refine three_pow_rpow_le_three_pow hDpos ?_
    have h1 : 4 * n ≤ 2 * D * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hXm4 : X ≤ (3 : ℝ) ^ ((m + 3) / 4) := by
    refine three_pow_rpow_le_three_pow hDpos ?_
    have h1 : 4 * ((m + 3) / 4) ≤ 2 * D * ((m + 3) / 4) :=
      Nat.mul_le_mul_right ((m + 3) / 4) (by omega)
    omega
  have hX3j : X ≤ 729 * ((3 : ℝ) ^ j) ^ d * r ^ n := by
    have h1 : ((3 : ℝ) ^ j) ^ 2 ≤ ((3 : ℝ) ^ j) ^ d :=
      pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hd
    have h2 : ((1 : ℝ) / 3) ^ n ≤ r ^ n := pow_le_pow_left₀ (by norm_num) hr13 n
    have h4 : X * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (6 + 2 * j) := by
      calc X * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ ((m + 3) / 4) * (3 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right hXm4 (by positivity)
        _ = (3 : ℝ) ^ ((m + 3) / 4 + n) := by rw [pow_add]
        _ ≤ (3 : ℝ) ^ (6 + 2 * j) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (3 : ℝ) ^ (6 + 2 * j) = 729 * ((3 : ℝ) ^ j) ^ 2 := by
      rw [pow_add, show 2 * j = j * 2 by ring, pow_mul]
      norm_num
    have e2 : ((1 : ℝ) / 3) ^ n * (3 : ℝ) ^ n = 1 := by
      rw [← mul_pow, show (1 : ℝ) / 3 * 3 = 1 by norm_num, one_pow]
    have h5 : X ≤ 729 * ((3 : ℝ) ^ j) ^ 2 * ((1 : ℝ) / 3) ^ n := by
      have h3n : (0 : ℝ) < 3 ^ n := by positivity
      rw [← e]
      calc X = X * (3 : ℝ) ^ n * ((1 : ℝ) / 3) ^ n := by
            rw [mul_assoc, mul_comm ((3 : ℝ) ^ n), e2, mul_one]
        _ ≤ (3 : ℝ) ^ (6 + 2 * j) * ((1 : ℝ) / 3) ^ n :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
    have h6 : 729 * ((3 : ℝ) ^ j) ^ 2 * ((1 : ℝ) / 3) ^ n ≤ 729 * ((3 : ℝ) ^ j) ^ d * r ^ n :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity) (by positivity)
    exact h5.trans h6
  have ht1 : ((3 : ℝ) ^ (n + 3 + j)) ^ d * (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3))) ≤
      2 * ((k.factorial : ℝ) * (2 / a) ^ k) * Real.exp (-c' * X) := by
    rw [hm', hk2]
    have h1 : Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)) ≤ Real.exp (-a * X) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hXℓ ha.le
      linarith
    have h2 := pow_mul_exp_neg_mul_le ha hX0 k
    have h3 : Real.exp (-(a / 2) * X) ≤ Real.exp (-c' * X) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_right hc'a hX0
      linarith
    calc X ^ k * (2 * Real.exp (-a * (3 : ℝ) ^ (ℓ + 3)))
        ≤ X ^ k * (2 * Real.exp (-a * X)) := by gcongr
      _ = 2 * (X ^ k * Real.exp (-a * X)) := by ring
      _ ≤ 2 * ((k.factorial : ℝ) * (2 / a) ^ k * Real.exp (-(a / 2) * X)) := by gcongr
      _ ≤ 2 * ((k.factorial : ℝ) * (2 / a) ^ k * Real.exp (-c' * X)) := by gcongr
      _ = _ := by ring
  have ht2 : ((3 : ℝ) ^ (3 + j)) ^ d * (C₂' * Real.exp (-c * (3 : ℝ) ^ n)) ≤
      C₂' * ((k.factorial : ℝ) * (2 / c) ^ k) * Real.exp (-c' * X) := by
    have hV : ((3 : ℝ) ^ (3 + j)) ^ d ≤ X ^ k := by
      rw [← hk2]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) d
    have h1 : Real.exp (-c * (3 : ℝ) ^ n) ≤ Real.exp (-c * X) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hXn hc.le
      linarith
    have h2 := pow_mul_exp_neg_mul_le hc hX0 k
    have h3 : Real.exp (-(c / 2) * X) ≤ Real.exp (-c' * X) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_right hc'c hX0
      linarith
    calc ((3 : ℝ) ^ (3 + j)) ^ d * (C₂' * Real.exp (-c * (3 : ℝ) ^ n))
        ≤ X ^ k * (C₂' * Real.exp (-c * X)) := by gcongr
      _ = C₂' * (X ^ k * Real.exp (-c * X)) := by ring
      _ ≤ C₂' * ((k.factorial : ℝ) * (2 / c) ^ k * Real.exp (-(c / 2) * X)) := by gcongr
      _ ≤ C₂' * ((k.factorial : ℝ) * (2 / c) ^ k * Real.exp (-c' * X)) := by gcongr
      _ = _ := by ring
  have ht3 : (27 : ℝ) ^ d * Real.exp (-(((3 : ℝ) ^ j) ^ d * r ^ n)) ≤
      27 ^ d * Real.exp (-c' * X) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h1 := mul_le_mul_of_nonneg_right hc'7 hX0
    have h2 : (1 : ℝ) / 729 * X ≤ ((3 : ℝ) ^ j) ^ d * r ^ n := by linarith
    linarith
  have e : (2 * ((k.factorial : ℝ) * (2 / a) ^ k) + C₂' * ((k.factorial : ℝ) * (2 / c) ^ k) +
      27 ^ d) * Real.exp (-c' * X) = 2 * ((k.factorial : ℝ) * (2 / a) ^ k) * Real.exp (-c' * X) +
      C₂' * ((k.factorial : ℝ) * (2 / c) ^ k) * Real.exp (-c' * X) +
      27 ^ d * Real.exp (-c' * X) := by ring
  rw [e]
  linarith

/-- **Proposition 5.2 of Armstrong and Dario** (every dimension `d ≥ 2`, given the bound of
Lemma 5.9, stretched-exponential tails on the cubes at the origin): there are `K`, `λ < 1`, `s`,
`c > 0` and `K'` with `P[¬ CubeSubaddGood p · □_m K λ] ≤ K' exp(-c (3^m)^s)` for every `m`. -/
theorem exists_cubeSubaddGood_tail_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K lam s c K' : ℝ, 0 ≤ K ∧ 0 < lam ∧ lam < 1 ∧ 0 < s ∧ s ≤ 1 ∧ 0 < c ∧ 0 ≤ K' ∧
      ∀ m : ℕ, latticeBondLaw d p {ω | ¬ CubeSubaddGood p ω ⟨m, 0⟩ K lam} ≤
        ENNReal.ofReal (K' * Real.exp (-c * ((3 : ℝ) ^ m) ^ s)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, r, hC, hr13, hr1, a, ha, C₂, hC₂, c, hc, htail⟩ :=
    exists_cubeRho_tail_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i, ∑ j, |((cubeAhom (d := d) p)⁻¹) i j| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hSb : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom (d := d) p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i| :=
    fun v => by rw [hSdef]; exact sum_abs_mulVec_le _ v
  have hs3 : 1 < √(3 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr13
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = max r (√(3 : ℝ))⁻¹ := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact lt_max_of_lt_left hr0
  have hρ1 : ρ < 1 := by rw [hρ]; exact max_lt hr1 (inv_lt_one_of_one_lt₀ hs3)
  have hrρ : r ≤ ρ := by rw [hρ]; exact le_max_left _ _
  have h3ρ : (√(3 : ℝ))⁻¹ ≤ ρ := by rw [hρ]; exact le_max_right _ _
  have hρi : 1 < ρ⁻¹ := (one_lt_inv₀ hρ0).2 hρ1
  obtain ⟨D₀, hD₀⟩ := pow_unbounded_of_one_lt ((9 : ℝ) ^ (4 * d + 1)) hρi
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = D₀ + 2 := ⟨_, rfl⟩
  have hD2 : 2 ≤ D := by omega
  have hDpos : 0 < D := by omega
  have hD : (9 : ℝ) ^ (4 * d + 1) ≤ ρ⁻¹ ^ D :=
    hD₀.le.trans (pow_le_pow_right₀ hρi.le (by omega))
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = √(√ρ) := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hρ0)
  have hl4 : l ^ 4 = ρ := by
    rw [hl, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hρ0.le]
  have hl1 : l < 1 := by
    by_contra h
    have := pow_le_pow_left₀ zero_le_one (not_lt.1 h) 4
    rw [one_pow, hl4] at this
    linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = √l := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; exact Real.sqrt_pos.2 hl0
  have hlam2 : lam ^ 2 = l := by rw [hlam]; exact Real.sq_sqrt hl0.le
  have hlam1 : lam < 1 := by
    by_contra h
    have := pow_le_pow_left₀ zero_le_one (not_lt.1 h) 2
    rw [one_pow, hlam2] at this
    linarith
  have hmu0 := muSubaddConst_nonneg d
  have he1 : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1
    linarith
  obtain ⟨A_T, hAT⟩ : ∃ A_T : ℝ, A_T = 2 * (Real.exp 1 - 1) * (C + 1) *
      (1 + (3 ^ d / 4 * S ^ 2 * d + d * d * coarseGradConstant d ^ 2 + 1)) +
      d * (muSubaddConst d * (1 + 8 * d * Real.exp 1) / 2 +
        3 ^ d / 4 * S ^ 2 * (8 * d * Real.exp 1 + 1)) := ⟨_, rfl⟩
  obtain ⟨A_y, hAy⟩ : ∃ A_y : ℝ, A_y = 1 + 2 * d + 2 * 3 ^ d * √(4 * d * d * Real.exp 1) :=
    ⟨_, rfl⟩
  obtain ⟨A_Λ, hAΛ⟩ : ∃ A_Λ : ℝ, A_Λ = d * d * coarseGradConstant d ^ 2 := ⟨_, rfl⟩
  have hAT0 : 0 ≤ A_T := by rw [hAT]; positivity
  have hAy0 : 0 ≤ A_y := by rw [hAy]; positivity
  have hAΛ0 : 0 ≤ A_Λ := by rw [hAΛ]; positivity
  obtain ⟨A₃, hA₃⟩ : ∃ A₃ : ℝ, A₃ = A_T + d * A_y * S + d / 2 * (2 * d * A_y * S +
      √(4 * d * (A_Λ + 1) * (A_T + A_y * S))) := ⟨_, rfl⟩
  have hA₃0 : 0 ≤ A₃ := by rw [hA₃]; positivity
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = min (a / 2) (min (c / 2) (1 / 729)) := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by
    rw [hc']
    exact lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hc'a : c' ≤ a / 2 := by rw [hc']; exact min_le_left _ _
  have hc'c : c' ≤ c / 2 := by rw [hc']; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc'7 : c' ≤ 1 / 729 := by rw [hc']; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 2 * (((2 * d * D).factorial : ℝ) * (2 / a) ^ (2 * d * D)) +
      2 * C₂.toReal * (((2 * d * D).factorial : ℝ) * (2 / c) ^ (2 * d * D)) + 27 ^ d :=
    ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hs1 : 1 / (2 * (D : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD2
    linarith
  refine ⟨A₃ / lam, lam, 1 / (2 * (D : ℝ)), c', K₀ + Real.exp (c' * 3 ^ 6), by positivity,
    hlam0, hlam1, by positivity, hs1, hc'0, by positivity, fun m => ?_⟩
  by_cases hm : m < 6
  · exact measure_le_of_lt_six _ hc'0 hK₀0 hDpos hm
  have hm6 : 6 ≤ m := not_lt.1 hm
  have hnm : m / 2 ≤ m := Nat.div_le_self m 2
  have hTb := threshold_le (d := d) (S := S) (n := m / 2) (ℓ := m / 2 / D) hC hr0.le hrρ h3ρ
  rw [← hAT] at hTb
  have hYb := comparisonCap_mul_le (d := d) (ℓ := m / 2 / D) hd0 hρ0 hρ1.le h3ρ hnm
  rw [← hAy] at hYb
  have hΛb : (d : ℝ) * d * coarseGradConstant d ^ 2 * ((3 : ℝ) ^ (m / 2 / D)) ^ (2 * (d - 1)) ≤
      A_Λ * ((3 : ℝ) ^ (m / 2 / D)) ^ (2 * d) := by
    rw [hAΛ]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega))
      (by positivity)
  have hXb := pow_mul_pow_sq_le (d := d) (n := m / 2) hρ0 hρ1.le hD hl4
  have hcap := cubeRhoCap_pos d S (m / 2 / D)
  have hsub0 := rhoSubaddConst_nonneg d (S := S) (m / 2 / D)
  have hT0 : 0 ≤ 2 * (Real.exp 1 - 1) * (C + 1) * (1 + cubeRhoCap d S (m / 2 / D)) *
      r ^ (m / 2) + rhoSubaddConst d S (m / 2 / D) * (1 / √((3 : ℝ) ^ (m / 2))) := by
    positivity
  have hneed := minimalset_bound_le hd0 hS0 (one_le_pow₀ (by norm_num)) hρ0.le hl0.le hl1.le hT0
    hTb (mul_nonneg (comparisonCap_nonneg d _) (by positivity)) hYb hΛb hAT0 hAy0 hAΛ0 hXb
  rw [← hA₃] at hneed
  have hlm : l ^ (m / 2) ≤ lam ^ m / lam := by
    rw [← hlam2, ← pow_mul, le_div_iff₀ hlam0, ← pow_succ]
    exact pow_le_pow_of_le_one hlam0.le hlam1.le (by omega)
  have hB : A₃ * l ^ (m / 2) ≤ A₃ / lam * lam ^ m := by
    calc A₃ * l ^ (m / 2) ≤ A₃ * (lam ^ m / lam) := mul_le_mul_of_nonneg_left hlm hA₃0
      _ = A₃ / lam * lam ^ m := by ring
  have hm' : m / 2 + 3 + (m - m / 2 - 3) = m := by omega
  have hsub : {ω : Configuration d | ¬ CubeSubaddGood p ω ⟨m, 0⟩ (A₃ / lam) lam} ⊆
      {ω : Configuration d | ¬ (PartitionSizeLe ω ⟨m / 2 + 3 + (m - m / 2 - 3), 0⟩ (m / 2 / D) ∧
        cubeRho p ω ⟨m / 2 + 3 + (m - m / 2 - 3), 0⟩ ≤
          2 * (Real.exp 1 - 1) * (C + 1) * (1 + cubeRhoCap d S (m / 2 / D)) * r ^ (m / 2) +
            rhoSubaddConst d S (m / 2 / D) * (1 / √((3 : ℝ) ^ (m / 2))))} := by
    intro ω hω hgood
    apply hω
    rw [show (⟨m, 0⟩ : TriadicCube d) = ⟨m / 2 + 3 + (m - m / 2 - 3), 0⟩ by rw [hm']]
    refine cubeSubaddGood_of_sizeLe hd0 p hgood.1 ((Nat.div_le_self (m / 2) D).trans
      (by change m / 2 ≤ m / 2 + 3 + (m - m / 2 - 3); omega)) hS0 hSb hgood.2 ?_
    rw [show (⟨m / 2 + 3 + (m - m / 2 - 3), 0⟩ : TriadicCube d).scale = m from hm']
    exact hneed.trans hB
  refine (measure_mono hsub).trans ((htail hSb (m / 2) (m - m / 2 - 3) (m / 2 / D)
    (Nat.div_le_self _ _)).trans ?_)
  have hC₂' : (2 : ℝ≥0∞) * C₂ = ENNReal.ofReal (2 * C₂.toReal) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC₂]
    norm_num
  rw [hC₂', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := lemma511_terms_le (d := d) (C₂' := 2 * C₂.toReal) (r := r) ha hc (by positivity)
    hc'a hc'c hc'7 hr13 hd hD2 hm6
  rw [← hK₀] at h
  have hE : 0 ≤ Real.exp (c' * 3 ^ 6) * Real.exp (-c' * ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ)))) :=
    by positivity
  calc _ ≤ K₀ * Real.exp (-c' * ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ)))) := by
        convert h using 2
    _ ≤ (K₀ + Real.exp (c' * 3 ^ 6)) * Real.exp (-c' * ((3 : ℝ) ^ m) ^ (1 / (2 * (D : ℝ)))) := by
        rw [add_mul]
        linarith

end Rigidity.Percolation
