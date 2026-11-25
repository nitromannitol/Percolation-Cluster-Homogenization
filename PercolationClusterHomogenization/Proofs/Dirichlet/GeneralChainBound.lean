import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralErrorChain

/-!
# The rate of the error chain of Section 6 in every dimension

With `K = 3^k`, `L = 3^m`, `Λ = 3^{k₀}`, `8k ≤ m + 7`, the sums of the datum
`S₂ ≤ L^d A₂ M²`, `S_t ≤ L^d A_t M^t` and the mesoscopic error `ε ≤ E K^{-c₀}`, the errors of the
chain of `cube_error_chain` are bounded by `δ₁ ≤ B₁ L^d M² K^{-c₀}` (`cubeChainDeltaOne_le`),
`δ₂ ≤ B₂ Λ^{3d} L^d M² K^{-c₀}` (`cubeChainDeltaTwo_le`) and
`δ₃ ≤ (180 K₀ K² Λ^{3d} + 2 C₃) S₂` (`cubeChainDeltaThree_le`), for
`c₀ ≤ min(1/2, 4(1 − 2/t), 4γ)`; the right side of `cube_error_chain` is then at most
`B Λ^{6d} L^{d+2} M² K^{-c₀}` (`cube_chain_le`). The planar form, with `Λ^{12}` and `L⁴`, is
`chain_le`.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation

namespace Rigidity.Dirichlet

/-- The constant of the bound of `δ₁`. -/
noncomputable def cubeChainBoundOne (d : ℕ) (σ E t A2 At : ℝ) : ℝ :=
  2 * (E * σ ^ 2 + (2 * d + 2) * σ) * A2 + 2 * σ * A2 +
    σ * (6 * d * 3 ^ 7) ^ (1 - 2 / t) *
      ((d : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t)) * At) ^ (2 / t)

/-- **The bound of the error `δ₁` of Lemma 6.2.** -/
theorem cubeChainDeltaOne_le {d : ℕ} (hd : 1 ≤ d) {σ ε t E A2 At c₀ M S2 St : ℝ} {m k : ℕ}
    (hσ : 0 < σ) (ht : 2 < t)
    (hE : 0 ≤ E) (hAt : 0 ≤ At) (hM : 0 ≤ M) (hc₀ : c₀ ≤ 1 / 2)
    (hc₀t : c₀ ≤ 4 * (1 - 2 / t)) (hkm : 8 * k ≤ m + 7)
    (hε : ε ≤ E * ((3 : ℝ) ^ k) ^ (-c₀)) (hS20 : 0 ≤ S2)
    (hS2 : S2 ≤ ((3 : ℝ) ^ m) ^ d * (A2 * M ^ 2)) (hSt0 : 0 ≤ St)
    (hSt : St / ((3 : ℝ) ^ m) ^ d ≤ At * M ^ t) :
    cubeChainDeltaOne d σ ε t m k S2 St ≤
      cubeChainBoundOne d σ E t A2 At * (((3 : ℝ) ^ m) ^ d * M ^ 2 * ((3 : ℝ) ^ k) ^ (-c₀)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have e1 : ((((3 ^ (2 * k - k) - 1) * 3 ^ k : ℕ) : ℝ)) = ((3 : ℝ) ^ k - 1) * (3 : ℝ) ^ k := by
    rw [show 2 * k - k = k by omega, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
    push_cast
    ring
  have hKL : ((3 : ℝ) ^ k) ^ 8 ≤ 3 ^ 7 * (3 : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hL0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  unfold cubeChainDeltaOne
  rw [e1]
  push_cast
  simp only [three_pow_mul_eq]
  set K := (3 : ℝ) ^ k with hK
  set L := (3 : ℝ) ^ m with hL
  set Kc := K ^ (-c₀) with hKc
  have hK0 : 0 < K := by linarith
  have hKc0 : 0 ≤ Kc := Real.rpow_nonneg hK0.le _
  have hinvK : 1 / K ≤ Kc := one_div_le_rpow_neg hK1 (by linarith)
  have hsqK : √(1 / K) ≤ Kc := sqrt_one_div_le_rpow_neg hK1 hc₀
  have hX' : 1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d ≤ d * (1 / K) := by
    have e : ((K - 1) * K) ^ d / (K ^ 2) ^ d = (1 + (-(1 / K))) ^ d := by
      rw [← div_pow]
      congr 1
      field_simp
      ring
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / K) by
      have : 1 / K ≤ 1 := by rw [div_le_one hK0]; exact hK1
      linarith) d
    rw [e]
    linarith
  have hsqX : √(1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d) ≤ d * Kc := by
    have h1 : 1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d ≤ (d : ℝ) ^ 2 * (1 / K) := by
      refine hX'.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      nlinarith
    refine (Real.sqrt_le_sqrt h1).trans ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    exact mul_le_mul_of_nonneg_left hsqK (by positivity)
  have hsqK2 : √(1 / K ^ 2) = 1 / K := by
    rw [show (1 : ℝ) / K ^ 2 = (1 / K) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsqK2' : √(K ^ 2) = K := Real.sqrt_sq hK0.le
  have he : 0 ≤ 1 - 2 / t := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact ht.le
  have ht0 : 0 < t := by linarith
  have ha : 2 * ((ε * σ ^ 2 + σ * (1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d) / 2 +
      σ * (√(1 / K ^ 2) + √(1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d) + √(1 / K))) * S2) ≤
      2 * ((E * σ ^ 2 + (2 * d + 2) * σ) * Kc * (L ^ d * (A2 * M ^ 2))) := by
    have hb : ε * σ ^ 2 + σ * (1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d) / 2 +
        σ * (√(1 / K ^ 2) + √(1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d) + √(1 / K)) ≤
        (E * σ ^ 2 + (2 * d + 2) * σ) * Kc := by
      rw [hsqK2]
      have h1 : ε * σ ^ 2 ≤ E * Kc * σ ^ 2 := mul_le_mul_of_nonneg_right hε (sq_nonneg σ)
      have h2 := mul_le_mul_of_nonneg_left (hX'.trans
        (mul_le_mul_of_nonneg_left hinvK (by positivity) : (d : ℝ) * (1 / K) ≤ d * Kc)) hσ.le
      have h3 : σ * (1 / K + √(1 - ((K - 1) * K) ^ d / (K ^ 2) ^ d) + √(1 / K)) ≤
          σ * ((d + 2) * Kc) := mul_le_mul_of_nonneg_left (by linarith) hσ.le
      have h4 : σ * (d * Kc) / 2 + σ * ((d + 2) * Kc) ≤ (2 * d + 2) * σ * Kc := by
        have := mul_nonneg (mul_nonneg hσ.le hKc0) (show (0 : ℝ) ≤ d by positivity)
        nlinarith
      nlinarith
    exact mul_le_mul_of_nonneg_left (mul_le_mul hb hS2 hS20 (by positivity)) (by norm_num)
  have hb' : 2 * (σ / √(K ^ 2) * S2) ≤ 2 * (σ * Kc * (L ^ d * (A2 * M ^ 2))) := by
    rw [hsqK2']
    have hb : σ / K ≤ σ * Kc := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvK hσ.le
    exact mul_le_mul_of_nonneg_left (mul_le_mul hb hS2 hS20 (by positivity)) (by norm_num)
  have hc' : L ^ d * (σ * ((2 * d * (K ^ 4 + 1 + K ^ 2) / L) ^ (1 - 2 / t) *
      ((d : ℝ) ^ (t / 2 - 1) *
        ((1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t * (K ^ 2 / K ^ 4) ^ t)) * St) / L ^ d) ^
          (2 / t))) ≤
      L ^ d * (σ * (((6 * d * 3 ^ 7) ^ (1 - 2 / t) * Kc) * (((d : ℝ) ^ (t / 2 - 1) *
        (1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t)) * At) ^ (2 / t) * M ^ 2))) := by
    have hbase : 2 * d * (K ^ 4 + 1 + K ^ 2) / L ≤ 6 * d * 3 ^ 7 / K ^ 4 := by
      have h4 : K ^ 4 + 1 + K ^ 2 ≤ 3 * K ^ 4 := by
        have := one_le_pow₀ (n := 4) hK1
        have := pow_le_pow_right₀ hK1 (show 2 ≤ 4 by norm_num)
        linarith
      rw [div_le_div_iff₀ hL0 (show (0 : ℝ) < K ^ 4 by positivity)]
      calc 2 * d * (K ^ 4 + 1 + K ^ 2) * K ^ 4 ≤ 2 * d * (3 * K ^ 4) * K ^ 4 := by gcongr
        _ = 6 * d * K ^ 8 := by ring
        _ ≤ 6 * d * (3 ^ 7 * L) := by gcongr
        _ = 6 * d * 3 ^ 7 * L := by ring
    have hpow1 := rpow_le_mul_rpow_neg_of_le_div_pow hK1 (by positivity) (by positivity) he hbase
    have hpow1' : (2 * d * (K ^ 4 + 1 + K ^ 2) / L) ^ (1 - 2 / t) ≤
        (6 * d * 3 ^ 7) ^ (1 - 2 / t) * Kc :=
      hpow1.trans (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hK1 (by push_cast; linarith))
        (by positivity))
    have hq1 : (K ^ 2 / K ^ 4) ^ t ≤ 1 :=
      Real.rpow_le_one (by positivity) ((div_le_one (by positivity)).2
        (pow_le_pow_right₀ hK1 (by norm_num))) ht0.le
    have hc1 : 1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t * (K ^ 2 / K ^ 4) ^ t) ≤
        1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t) := by
      have h := mul_le_mul_of_nonneg_left hq1 (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ t)
      rw [mul_one] at h
      have := mul_le_mul_of_nonneg_left (show 1 + 2 ^ t + (d : ℝ) ^ t * (K ^ 2 / K ^ 4) ^ t ≤
        1 + 2 ^ t + (d : ℝ) ^ t by linarith) (by positivity : (0 : ℝ) ≤ 3 ^ (t - 1))
      linarith
    have hinner : (d : ℝ) ^ (t / 2 - 1) *
        ((1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t * (K ^ 2 / K ^ 4) ^ t)) * St) / L ^ d ≤
        (d : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t)) * At * M ^ t :=
      calc (d : ℝ) ^ (t / 2 - 1) *
            ((1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t * (K ^ 2 / K ^ 4) ^ t)) * St) / L ^ d =
            (d : ℝ) ^ (t / 2 - 1) *
              (1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t * (K ^ 2 / K ^ 4) ^ t)) *
              (St / L ^ d) := by ring
        _ ≤ (d : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t)) *
              (At * M ^ t) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by positivity)) hSt (by positivity)
            (by positivity)
        _ = (d : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t)) * At * M ^ t := by
          ring
    have hpow2 := Real.rpow_le_rpow (by positivity) hinner (by positivity : (0 : ℝ) ≤ 2 / t)
    rw [rpow_two_div_mul_rpow
      (a := (d : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + (d : ℝ) ^ t)) * At) hM
      (by positivity) ht0] at hpow2
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul hpow1' hpow2
      (by positivity) (by positivity)) hσ.le) (by positivity)
  refine (add_le_add (add_le_add ha hb') hc').trans (le_of_eq ?_)
  unfold cubeChainBoundOne
  ring

/-- The bound of the Poincaré constants of the chain. -/
theorem cubeChainP_le {d : ℕ} (hd : 1 ≤ d) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (m k₀ : ℕ) :
    cubeChainP d K₀ m k₀ ≤ 45 / 2 * K₀ * ((3 : ℝ) ^ m) ^ 2 * ((3 : ℝ) ^ k₀) ^ (3 * d) := by
  unfold cubeChainP
  have h3d : (3 : ℝ) ≤ 3 ^ d := le_self_pow₀ (by norm_num) (by omega)
  have ha : (3 : ℝ) ^ d / (3 ^ d - 1) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hΛd : (1 : ℝ) ≤ ((3 : ℝ) ^ k₀) ^ d := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have e1 : (3 : ℝ) ^ (d * k₀) = ((3 : ℝ) ^ k₀) ^ d := by rw [mul_comm, pow_mul]
  have e2 : ((3 : ℝ) ^ k₀) ^ (3 * d) = ((3 : ℝ) ^ k₀) ^ d * ((3 : ℝ) ^ k₀) ^ (2 * d) := by
    rw [← pow_add]
    ring_nf
  rw [e1, e2, pow_succ (3 : ℝ) m]
  have h : 1 + 3 ^ d / (3 ^ d - 1) * ((3 : ℝ) ^ k₀) ^ d ≤ 5 / 2 * ((3 : ℝ) ^ k₀) ^ d := by
    have := mul_le_mul_of_nonneg_right ha (by linarith : (0 : ℝ) ≤ ((3 : ℝ) ^ k₀) ^ d)
    linarith
  have hΛ2 : (0 : ℝ) ≤ ((3 : ℝ) ^ k₀) ^ (2 * d) := by positivity
  calc (1 + 3 ^ d / (3 ^ d - 1) * ((3 : ℝ) ^ k₀) ^ d) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
        ((3 : ℝ) ^ m * 3) ^ 2
      ≤ (5 / 2 * ((3 : ℝ) ^ k₀) ^ d) * K₀ * ((3 : ℝ) ^ k₀) ^ (2 * d) *
        ((3 : ℝ) ^ m * 3) ^ 2 := by gcongr
    _ = 45 / 2 * K₀ * ((3 : ℝ) ^ m) ^ 2 * (((3 : ℝ) ^ k₀) ^ d * ((3 : ℝ) ^ k₀) ^ (2 * d)) := by
        ring

theorem cubeChainPT_le {d : ℕ} (hd : 1 ≤ d) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (k k₀ : ℕ) :
    cubeChainPT d K₀ k k₀ ≤ 45 / 2 * K₀ * ((3 : ℝ) ^ k) ^ 2 * ((3 : ℝ) ^ k₀) ^ (3 * d) :=
  cubeChainP_le hd hK₀ k k₀

/-- **The bound of the error `δ₃`.** -/
theorem cubeChainDeltaThree_le {d : ℕ} (hd : 1 ≤ d) {σ K₀ C₃ S2 : ℝ} {k k₀ : ℕ} (hσ : 0 < σ)
    (hK₀ : 0 ≤ K₀) (hC₃ : 0 ≤ C₃) (hS2 : 0 ≤ S2) :
    cubeChainDeltaThree d σ K₀ C₃ k k₀ S2 ≤
      (180 * K₀ * ((3 : ℝ) ^ k) ^ 2 * ((3 : ℝ) ^ k₀) ^ (3 * d) + 2 * C₃) * S2 := by
  have hPT := cubeChainPT_le hd hK₀ k k₀
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  unfold cubeChainDeltaThree
  push_cast
  simp only [three_pow_mul_eq]
  rw [div_self hσ.ne', one_mul]
  have hq : C₃ * ((3 : ℝ) ^ k) ^ 4 / (((3 : ℝ) ^ k) ^ 4) ^ 2 ≤ C₃ := by
    rw [mul_div_assoc]
    refine mul_le_of_le_one_right hC₃ ?_
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ ((3 : ℝ) ^ k) ^ 4 := one_le_pow₀ hK1
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hPT (by positivity : (0 : ℝ) ≤ 4 * S2)
  have h2 := mul_le_mul_of_nonneg_right hq hS2
  linarith

/-- The constant of the bound of `δ₂`. -/
noncomputable def cubeChainBoundTwo (d : ℕ) (σ E γ t K₀ CA A2 At : ℝ) : ℝ :=
  6 * (E + 4 * d) * A2 +
    9 * d * max σ 1 * (10 * d * (1 + d) * 2 ^ d * max σ 1 / σ + 1) * A2 +
    6 * max σ 1 * (d * (90 * K₀ + CA)) * A2 +
    (2 + 3 * max σ 1 / σ) * (2 * (σ * (20 * d * 3 ^ 7) ^ (1 - 2 / t) *
        ((d : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t)) +
      88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
        (10 * 3 ^ 7) ^ γ * ((d : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t))

/-- **The bound of the error `δ₂` of Lemma 6.3.** -/
theorem cubeChainDeltaTwo_le {d : ℕ} (hd : 1 ≤ d)
    {σ ε γ t E A2 At c₀ M S2 St K₀ CA : ℝ} {m k k₀ : ℕ} (hσ : 0 < σ)
    (ht : 2 < t) (hγ0 : 0 < γ) (hγt : γ * (t / (t - 2)) < 1) (hE : 0 ≤ E) (hA2 : 0 ≤ A2)
    (hAt : 0 ≤ At) (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀) (hCA : 0 ≤ CA) (hc₀ : c₀ ≤ 1 / 2)
    (hc₀t : c₀ ≤ 4 * (1 - 2 / t)) (hc₀γ : c₀ ≤ 4 * γ) (hkm : 8 * k ≤ m + 7)
    (hε : ε ≤ E * ((3 : ℝ) ^ k) ^ (-c₀)) (hS20 : 0 ≤ S2)
    (hS2 : S2 ≤ ((3 : ℝ) ^ m) ^ d * (A2 * M ^ 2)) (hSt0 : 0 ≤ St)
    (hSt : St / ((3 : ℝ) ^ m) ^ d ≤ At * M ^ t) :
    cubeChainDeltaTwo d σ ε γ t K₀ CA m k k₀ S2 St ≤
      cubeChainBoundTwo d σ E γ t K₀ CA A2 At *
        (((3 : ℝ) ^ k₀) ^ (3 * d) * (((3 : ℝ) ^ m) ^ d * M ^ 2 * ((3 : ℝ) ^ k) ^ (-c₀))) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKL : ((3 : ℝ) ^ k) ^ 8 ≤ 3 ^ 7 * (3 : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hL0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hPT := cubeChainPT_le hd hK₀ k k₀
  have h3Λ : (3 : ℝ) ^ (k₀ + 1) = 3 * (3 : ℝ) ^ k₀ := by rw [pow_succ]; ring
  unfold cubeChainDeltaTwo
  push_cast
  simp only [three_pow_mul_eq]
  rw [h3Λ]
  set K := (3 : ℝ) ^ k with hK
  set L := (3 : ℝ) ^ m with hL
  set Λ := (3 : ℝ) ^ k₀ with hΛ
  set Kc := K ^ (-c₀) with hKc
  set PT := cubeChainPT d K₀ k k₀ with hPTdef
  have hK0 : 0 < K := by linarith
  have hKc0 : 0 ≤ Kc := Real.rpow_nonneg hK0.le _
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by norm_num)
  have hΛ6 : 1 ≤ Λ ^ (3 * d) := one_le_pow₀ hΛ1
  have hinvK : 1 / K ≤ Kc := one_div_le_rpow_neg hK1 (by linarith)
  have he : 0 ≤ 1 - 2 / t := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact ht.le
  have ht0 : 0 < t := by linarith
  have hWb : 0 ≤ (2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2))) :=
    div_nonneg (by positivity) (by linarith)
  have hW : 0 ≤ ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
    Real.rpow_nonneg hWb _
  have hd1 : 6 * K ^ d * ((ε + d * (3 * Λ + 1) / K) * (S2 / K ^ d)) ≤
      6 * (E + 4 * d) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2)) := by
    have a1 : E * Kc ≤ E * Λ ^ (3 * d) * Kc := by
      have := mul_le_mul_of_nonneg_left hΛ6 (mul_nonneg hE hKc0)
      linarith
    have a2 : d * (3 * Λ + 1) / K ≤ 4 * d * Λ ^ (3 * d) * Kc := by
      rw [div_eq_mul_one_div]
      have hΛ3 : Λ ≤ Λ ^ (3 * d) := le_self_pow₀ hΛ1 (by omega)
      have : (d : ℝ) * (3 * Λ + 1) ≤ 4 * d * Λ ^ (3 * d) := by
        have h1 : 3 * Λ + 1 ≤ 4 * Λ ^ (3 * d) := by linarith
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ d)
        linarith
      exact mul_le_mul this hinvK (by positivity) (by positivity)
    have hx : ε + d * (3 * Λ + 1) / K ≤ (E + 4 * d) * Λ ^ (3 * d) * Kc := by linarith
    calc 6 * K ^ d * ((ε + d * (3 * Λ + 1) / K) * (S2 / K ^ d))
        = 6 * (ε + d * (3 * Λ + 1) / K) * S2 * (K ^ d / K ^ d) := by ring
      _ = 6 * (ε + d * (3 * Λ + 1) / K) * S2 := by rw [div_self (by positivity), mul_one]
      _ ≤ 6 * ((E + 4 * d) * Λ ^ (3 * d) * Kc) * (L ^ d * (A2 * M ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hS2 hS20 (by positivity)
      _ = 6 * (E + 4 * d) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2)) := by ring
  have he' : 3 * (max σ 1 * (d * (3 * ((1 + d) * 2 ^ d * K ^ 3 * (10 * d * max σ 1 /
      (σ * (K ^ 4) ^ 2)) + 1 / K) * S2))) ≤
      9 * d * max σ 1 * (10 * d * (1 + d) * 2 ^ d * max σ 1 / σ + 1) * Λ ^ (3 * d) * Kc *
        (L ^ d * (A2 * M ^ 2)) := by
    have hK38 : K ^ 3 / (K ^ 4) ^ 2 ≤ 1 / K := by
      rw [div_le_div_iff₀ (show (0 : ℝ) < (K ^ 4) ^ 2 by positivity) hK0,
        show K ^ 3 * K = K ^ 4 by ring, one_mul]
      exact le_self_pow₀ (one_le_pow₀ hK1) (by norm_num)
    have hY : (1 + d) * 2 ^ d * K ^ 3 * (10 * d * max σ 1 / (σ * (K ^ 4) ^ 2)) + 1 / K ≤
        (10 * d * (1 + d) * 2 ^ d * max σ 1 / σ + 1) * Kc := by
      have e : (1 + (d : ℝ)) * 2 ^ d * K ^ 3 * (10 * d * max σ 1 / (σ * (K ^ 4) ^ 2)) =
          10 * d * (1 + d) * 2 ^ d * max σ 1 / σ * (K ^ 3 / (K ^ 4) ^ 2) := by
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hK38
        (by positivity : (0 : ℝ) ≤ 10 * d * (1 + d) * 2 ^ d * max σ 1 / σ)
      have := mul_le_mul_of_nonneg_left hinvK
        (by positivity : (0 : ℝ) ≤ 10 * d * (1 + d) * 2 ^ d * max σ 1 / σ + 1)
      linarith
    calc 3 * (max σ 1 * (d * (3 * ((1 + d) * 2 ^ d * K ^ 3 * (10 * d * max σ 1 /
          (σ * (K ^ 4) ^ 2)) + 1 / K) * S2)))
        = 9 * d * max σ 1 * (((1 + d) * 2 ^ d * K ^ 3 * (10 * d * max σ 1 /
          (σ * (K ^ 4) ^ 2)) + 1 / K) * S2) := by ring
      _ ≤ 9 * d * max σ 1 * (((10 * d * (1 + d) * 2 ^ d * max σ 1 / σ + 1) * Kc) *
          (L ^ d * (A2 * M ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hY hS2 hS20 (by positivity)) (by positivity)
      _ ≤ Λ ^ (3 * d) * (9 * d * max σ 1 * (((10 * d * (1 + d) * 2 ^ d * max σ 1 / σ + 1) *
          Kc) * (L ^ d * (A2 * M ^ 2)))) :=
        le_mul_of_one_le_left (by positivity) hΛ6
      _ = 9 * d * max σ 1 * (10 * d * (1 + d) * 2 ^ d * max σ 1 / σ + 1) * Λ ^ (3 * d) * Kc *
          (L ^ d * (A2 * M ^ 2)) := by ring
  have hf : 6 * max σ 1 * (d * (1 / K ^ 3) ^ 2) *
      (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2) ≤
      6 * max σ 1 * (d * (90 * K₀ + CA)) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2)) := by
    have hPT' : PT ≤ 45 / 2 * K₀ * K ^ 2 * Λ ^ (3 * d) := hPT
    have q1 : (1 / K ^ 3) ^ 2 * K ^ 2 ≤ 1 / K := by
      rw [show (1 / K ^ 3) ^ 2 * K ^ 2 = K ^ 2 / (K ^ 3) ^ 2 by ring,
        div_le_div_iff₀ (show (0 : ℝ) < (K ^ 3) ^ 2 by positivity) hK0,
        show K ^ 2 * K = K ^ 3 by ring, one_mul]
      exact le_self_pow₀ (one_le_pow₀ hK1) (by norm_num)
    have q2 : (1 / K ^ 3) ^ 2 * (K ^ 4 / (K ^ 4) ^ 2) ≤ 1 / K := by
      rw [show (1 / K ^ 3) ^ 2 * (K ^ 4 / (K ^ 4) ^ 2) = K ^ 4 / ((K ^ 3) ^ 2 * (K ^ 4) ^ 2) by
        ring, div_le_div_iff₀ (show (0 : ℝ) < (K ^ 3) ^ 2 * (K ^ 4) ^ 2 by positivity) hK0,
        one_mul]
      calc K ^ 4 * K = K ^ 5 := by ring
        _ ≤ K ^ 14 := pow_le_pow_right₀ hK1 (by norm_num)
        _ = (K ^ 3) ^ 2 * (K ^ 4) ^ 2 := by ring
    have r1 : (1 / K ^ 3) ^ 2 * PT ≤ 45 / 2 * K₀ * Λ ^ (3 * d) * (1 / K) :=
      calc (1 / K ^ 3) ^ 2 * PT ≤ (1 / K ^ 3) ^ 2 * (45 / 2 * K₀ * K ^ 2 * Λ ^ (3 * d)) :=
            mul_le_mul_of_nonneg_left hPT' (by positivity)
        _ = 45 / 2 * K₀ * Λ ^ (3 * d) * ((1 / K ^ 3) ^ 2 * K ^ 2) := by ring
        _ ≤ 45 / 2 * K₀ * Λ ^ (3 * d) * (1 / K) := mul_le_mul_of_nonneg_left q1 (by positivity)
    have r2 : (1 / K ^ 3) ^ 2 * (CA * K ^ 4 / (K ^ 4) ^ 2) ≤ CA * (1 / K) :=
      calc (1 / K ^ 3) ^ 2 * (CA * K ^ 4 / (K ^ 4) ^ 2) =
            CA * ((1 / K ^ 3) ^ 2 * (K ^ 4 / (K ^ 4) ^ 2)) := by ring
        _ ≤ CA * (1 / K) := mul_le_mul_of_nonneg_left q2 hCA
    have s1 := mul_le_mul_of_nonneg_right r1 hS20
    have s2 := mul_le_mul_of_nonneg_right r2 hS20
    have s3 : (90 * K₀ * Λ ^ (3 * d) + CA) * (1 / K) * S2 ≤
        (90 * K₀ + CA) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2)) := by
      have h : 90 * K₀ * Λ ^ (3 * d) + CA ≤ (90 * K₀ + CA) * Λ ^ (3 * d) := by
        have := mul_le_mul_of_nonneg_left hΛ6 hCA
        linarith only [this]
      exact mul_le_mul (mul_le_mul h hinvK (by positivity) (by positivity)) hS2 hS20
        (by positivity)
    have r : (1 / K ^ 3) ^ 2 * (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2) ≤
        (90 * K₀ + CA) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2)) :=
      calc (1 / K ^ 3) ^ 2 * (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2)
          = 4 * ((1 / K ^ 3) ^ 2 * PT * S2) +
            ((1 / K ^ 3) ^ 2 * (CA * K ^ 4 / (K ^ 4) ^ 2) * S2) := by ring
        _ ≤ 4 * (45 / 2 * K₀ * Λ ^ (3 * d) * (1 / K) * S2) + CA * (1 / K) * S2 :=
          add_le_add (mul_le_mul_of_nonneg_left s1 (by norm_num)) s2
        _ = (90 * K₀ * Λ ^ (3 * d) + CA) * (1 / K) * S2 := by ring
        _ ≤ (90 * K₀ + CA) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2)) := s3
    calc 6 * max σ 1 * (d * (1 / K ^ 3) ^ 2) * (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2)
        = 6 * max σ 1 * d * ((1 / K ^ 3) ^ 2 * (PT * (4 * S2) +
          CA * K ^ 4 / (K ^ 4) ^ 2 * S2)) := by ring
      _ ≤ 6 * max σ 1 * d * ((90 * K₀ + CA) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2))) :=
        mul_le_mul_of_nonneg_left r (by positivity)
      _ = 6 * max σ 1 * (d * (90 * K₀ + CA)) * Λ ^ (3 * d) * Kc * (L ^ d * (A2 * M ^ 2)) := by
        ring
  have hg : L ^ d * ((2 + 3 * max σ 1 / σ) * (2 * (σ * ((2 * d *
      (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ (1 - 2 / t) *
        ((d : ℝ) ^ (t / 2 - 1) * (St / L ^ d)) ^ (2 / t))) +
      88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
        ((K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ γ *
        ((d : ℝ) ^ (t / 2 - 1) * (St / L ^ d)) ^ (2 / t))) ≤
      Λ ^ (3 * d) * (L ^ d * ((2 + 3 * max σ 1 / σ) * (2 * (σ * (((20 * d * 3 ^ 7) ^ (1 - 2 / t) *
        Kc) * (((d : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t) * M ^ 2))) +
        88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
          ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
          ((10 * 3 ^ 7) ^ γ * Kc) * (((d : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t) * M ^ 2)))) := by
    have hℓ : K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1 ≤ 10 * K ^ 4 := by
      have h1 : 1 ≤ K ^ 4 := one_le_pow₀ hK1
      have h2 : K ≤ K ^ 4 := le_self_pow₀ hK1 (by norm_num)
      have h3 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
      linarith
    have hb1 : 2 * d * (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L ≤ 20 * d * 3 ^ 7 / K ^ 4 := by
      rw [div_le_div_iff₀ hL0 (show (0 : ℝ) < K ^ 4 by positivity)]
      calc 2 * d * (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) * K ^ 4 ≤
            2 * d * (10 * K ^ 4) * K ^ 4 := by gcongr
        _ = 20 * d * K ^ 8 := by ring
        _ ≤ 20 * d * (3 ^ 7 * L) := by gcongr
        _ = 20 * d * 3 ^ 7 * L := by ring
    have hb2 : (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L ≤ 10 * 3 ^ 7 / K ^ 4 := by
      rw [div_le_div_iff₀ hL0 (show (0 : ℝ) < K ^ 4 by positivity)]
      calc (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) * K ^ 4 ≤ (10 * K ^ 4) * K ^ 4 := by gcongr
        _ = 10 * K ^ 8 := by ring
        _ ≤ 10 * (3 ^ 7 * L) := by gcongr
        _ = 10 * 3 ^ 7 * L := by ring
    have hp1 : (2 * d * (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ (1 - 2 / t) ≤
        (20 * d * 3 ^ 7) ^ (1 - 2 / t) * Kc :=
      (rpow_le_mul_rpow_neg_of_le_div_pow hK1 (by positivity) (by positivity) he hb1).trans
        (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hK1 (by push_cast; linarith))
          (by positivity))
    have hp2 : ((K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ γ ≤ (10 * 3 ^ 7) ^ γ * Kc :=
      (rpow_le_mul_rpow_neg_of_le_div_pow hK1 (by positivity) (by norm_num) hγ0.le hb2).trans
        (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hK1 (by push_cast; linarith))
          (by positivity))
    have hH0 : (d : ℝ) ^ (t / 2 - 1) * (St / L ^ d) ≤ (d : ℝ) ^ (t / 2 - 1) * At * M ^ t := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hSt (by positivity)
    have hH := Real.rpow_le_rpow (by positivity) hH0 (by positivity : (0 : ℝ) ≤ 2 / t)
    rw [rpow_two_div_mul_rpow (a := (d : ℝ) ^ (t / 2 - 1) * At) hM (by positivity) ht0] at hH
    have hA : (0 : ℝ) ≤ 88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
      mul_nonneg (by positivity) hW
    have hmain := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul hp1 hH (by positivity) (by positivity)) hσ.le)
        (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul (mul_le_mul_of_nonneg_left hp2 hA) hH (by positivity) (by positivity)))
      (by positivity : (0 : ℝ) ≤ 2 + 3 * max σ 1 / σ)) (by positivity : (0 : ℝ) ≤ L ^ d)
    exact hmain.trans (le_mul_of_one_le_left (by positivity) hΛ6)
  refine (add_le_add (add_le_add (add_le_add hd1 he') hf) hg).trans (le_of_eq ?_)
  unfold cubeChainBoundTwo
  ring

theorem cubeChainBoundOne_nonneg {d : ℕ} {σ E t A2 At : ℝ} (hσ : 0 < σ) (hE : 0 ≤ E)
    (hA2 : 0 ≤ A2) (hAt : 0 ≤ At) : 0 ≤ cubeChainBoundOne d σ E t A2 At := by
  unfold cubeChainBoundOne
  positivity

theorem cubeChainBoundTwo_nonneg {d : ℕ} {σ E γ t K₀ CA A2 At : ℝ} (hσ : 0 < σ)
    (hγt : γ * (t / (t - 2)) < 1) (hE : 0 ≤ E) (hA2 : 0 ≤ A2) (hAt : 0 ≤ At) (hK₀ : 0 ≤ K₀)
    (hCA : 0 ≤ CA) : 0 ≤ cubeChainBoundTwo d σ E γ t K₀ CA A2 At := by
  have hWb : 0 ≤ (2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2))) :=
    div_nonneg (by positivity) (by linarith)
  have hW : 0 ≤ ((2 * (d : ℝ)) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
    Real.rpow_nonneg hWb _
  unfold cubeChainBoundTwo
  positivity

/-- The constant of the bound of the error chain. -/
noncomputable def cubeChainBound (d : ℕ) (σ E γ t A2 At K₀ C₃ CA : ℝ) : ℝ :=
  45 * K₀ * (cubeChainBoundOne d σ E t A2 At + cubeChainBoundTwo d σ E γ t K₀ CA A2 At) +
    2 * 3 ^ 14 * (180 * K₀ + 2 * C₃) * A2

/-- **The bound of the error chain**: with `K = 3^k`, `L = 3^m`, `Λ = 3^{k₀}`, the right side of
`cube_error_chain` is at most `B Λ^{6d} L^{d+2} M² K^{-c₀}`. -/
theorem cube_chain_le {d : ℕ} (hd : 1 ≤ d)
    {σ ε γ t E A2 At c₀ M S2 St K₀ C₃ CA : ℝ} {m k k₀ : ℕ} (hσ : 0 < σ)
    (ht : 2 < t) (hγ0 : 0 < γ) (hγt : γ * (t / (t - 2)) < 1) (hE : 0 ≤ E) (hA2 : 0 ≤ A2)
    (hAt : 0 ≤ At) (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀) (hC₃ : 0 ≤ C₃) (hCA : 0 ≤ CA)
    (hc₀ : c₀ ≤ 1 / 2) (hc₀t : c₀ ≤ 4 * (1 - 2 / t)) (hc₀γ : c₀ ≤ 4 * γ) (hkm : 8 * k ≤ m + 7)
    (hε : ε ≤ E * ((3 : ℝ) ^ k) ^ (-c₀)) (hS20 : 0 ≤ S2)
    (hS2 : S2 ≤ ((3 : ℝ) ^ m) ^ d * (A2 * M ^ 2)) (hSt0 : 0 ≤ St)
    (hSt : St / ((3 : ℝ) ^ m) ^ d ≤ At * M ^ t) :
    2 * (cubeChainP d K₀ m k₀ * ((cubeChainDeltaOne d σ ε t m k S2 St +
        cubeChainDeltaTwo d σ ε γ t K₀ CA m k k₀ S2 St) / 1)) +
        2 * cubeChainDeltaThree d σ K₀ C₃ k k₀ S2 ≤
      cubeChainBound d σ E γ t A2 At K₀ C₃ CA *
        ((((3 : ℝ) ^ k₀) ^ (3 * d)) ^ 2 *
          (((3 : ℝ) ^ m) ^ d * ((3 : ℝ) ^ m) ^ 2 * M ^ 2 * ((3 : ℝ) ^ k) ^ (-c₀))) := by
  have h1 := cubeChainDeltaOne_le hd hσ ht hE hAt hM hc₀ hc₀t hkm hε hS20 hS2 hSt0 hSt
  have h2 := cubeChainDeltaTwo_le hd (k₀ := k₀) (K₀ := K₀) (CA := CA) hσ ht hγ0 hγt hE hA2 hAt
    hM hK₀ hCA hc₀ hc₀t hc₀γ hkm hε hS20 hS2 hSt0 hSt
  have h3 := cubeChainDeltaThree_le hd (k := k) (k₀ := k₀) hσ hK₀ hC₃ hS20
  have hP := cubeChainP_le hd hK₀ m k₀
  have hP0 := cubeChainP_nonneg d hK₀ m k₀
  have hB1 := cubeChainBoundOne_nonneg (d := d) hσ hE hA2 hAt (σ := σ) (t := t)
  have hB2 := cubeChainBoundTwo_nonneg (d := d) hσ hγt hE hA2 hAt hK₀ hCA (γ := γ)
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hKL : ((3 : ℝ) ^ k) ^ 8 ≤ 3 ^ 7 * (3 : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  set K := (3 : ℝ) ^ k with hK
  set L := (3 : ℝ) ^ m with hL
  set Λ := ((3 : ℝ) ^ k₀) ^ (3 * d) with hΛ
  set Ld := L ^ d with hLd
  set Kc := K ^ (-c₀) with hKc
  have hKc0 : 0 ≤ Kc := Real.rpow_nonneg (by linarith) _
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hΛ12 : Λ ≤ Λ ^ 2 := le_self_pow₀ hΛ1 (by norm_num)
  have hK2 := sq_le_mul_rpow_neg hK1 (by linarith : c₀ ≤ 14) hKL
  have hK2' : 1 ≤ 3 ^ 14 * L ^ 2 * Kc := le_trans (one_le_pow₀ hK1) hK2
  have hLd0 : 0 ≤ Ld := by positivity
  have hX0 : 0 ≤ Ld * M ^ 2 * Kc := by positivity
  have hD : cubeChainDeltaOne d σ ε t m k S2 St + cubeChainDeltaTwo d σ ε γ t K₀ CA m k k₀ S2 St ≤
      (cubeChainBoundOne d σ E t A2 At + cubeChainBoundTwo d σ E γ t K₀ CA A2 At) *
        (Λ * (Ld * M ^ 2 * Kc)) := by
    have : cubeChainBoundOne d σ E t A2 At * (Ld * M ^ 2 * Kc) ≤
        cubeChainBoundOne d σ E t A2 At * (Λ * (Ld * M ^ 2 * Kc)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX0 hΛ1) hB1
    linarith
  have hPD : cubeChainP d K₀ m k₀ * ((cubeChainDeltaOne d σ ε t m k S2 St +
        cubeChainDeltaTwo d σ ε γ t K₀ CA m k k₀ S2 St) / 1) ≤
      45 / 2 * K₀ * L ^ 2 * Λ * ((cubeChainBoundOne d σ E t A2 At +
        cubeChainBoundTwo d σ E γ t K₀ CA A2 At) * (Λ * (Ld * M ^ 2 * Kc))) := by
    rw [div_one]
    exact (mul_le_mul_of_nonneg_left hD hP0).trans
      (mul_le_mul_of_nonneg_right hP (by positivity))
  have h3' : cubeChainDeltaThree d σ K₀ C₃ k k₀ S2 ≤
      3 ^ 14 * (180 * K₀ + 2 * C₃) * A2 * (Λ ^ 2 * (Ld * L ^ 2 * M ^ 2 * Kc)) := by
    have hc : 180 * K₀ * K ^ 2 * Λ + 2 * C₃ ≤
        (180 * K₀ + 2 * C₃) * (3 ^ 14 * L ^ 2 * Kc * Λ ^ 2) := by
      have e1 : 180 * K₀ * K ^ 2 * Λ ≤ 180 * K₀ * (3 ^ 14 * L ^ 2 * Kc) * Λ ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hK2 (by positivity)) hΛ12 (by positivity)
          (by positivity)
      have e2 : 2 * C₃ ≤ 2 * C₃ * (3 ^ 14 * L ^ 2 * Kc * Λ ^ 2) :=
        le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le hK2' (one_le_pow₀ hΛ1))
      linarith
    calc cubeChainDeltaThree d σ K₀ C₃ k k₀ S2
        ≤ (180 * K₀ * K ^ 2 * Λ + 2 * C₃) * S2 := h3
      _ ≤ ((180 * K₀ + 2 * C₃) * (3 ^ 14 * L ^ 2 * Kc * Λ ^ 2)) * (Ld * (A2 * M ^ 2)) :=
        mul_le_mul hc hS2 hS20 (by positivity)
      _ = 3 ^ 14 * (180 * K₀ + 2 * C₃) * A2 * (Λ ^ 2 * (Ld * L ^ 2 * M ^ 2 * Kc)) := by ring
  unfold cubeChainBound
  linarith

end Rigidity.Dirichlet
