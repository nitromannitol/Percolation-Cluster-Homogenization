import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorAtScale
import PercolationClusterHomogenization.Proofs.Dirichlet.GeneralScaleForms
import PercolationClusterHomogenization.Proofs.Partition.AlmostSure

/-!
# Corrected planes on the infinite cluster of `ℤᵈ` from the sublinearity (1.18)

Every slope has a corrected plane on the infinite cluster of supercritical bond percolation on
`ℤᵈ`, `d ≥ 2` (Armstrong and Dario, arXiv:1609.09431v2, Theorem 2 (ii) at `k = 1`, with the
sublinearity in the uniform norm of Remark 1.1 and (1.22)), from the bound (1.18) with an almost
surely finite scale (`correctedPlaneExistence_of_sublinearL2Ae`), by the argument of the Remark
after (1.19):

* the Lipschitz estimate at every centre (`exists_all_centres_constant_approximation`), with the
  maximum of its minimal scales over the boxes (`ae_eventually_scale_le_three`), bounds the
  increments of the corrector `χ` along the open edges by `C |q| E^{(d+1)γ}` at the scale
  `E = 3^m`;
* the minimal scales of Proposition 2.4 (`cubeMinimalScales_holds`) bound the sizes of the
  partition cubes of `□_{m+3}` by `3 E^γ`;
* the uniform bound at the scale `E` (`abs_corrector_le_at_scale`), with the box of side
  `t = ⌊E^{1-2η}⌋`, gives `|χ(x)| ≤ c |q| E^{1-η}` on `{|x_i| ≤ E}`, `η = δ/(2d)`,
  `γ = η/(2d+1)` (`corrector_scale_arith`);
* `componentSlopeAsymptotics_of_scale_bound` turns it into the slope asymptotics.
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- **The arithmetic of the uniform bound at one scale**: the bound of `abs_corrector_le_at_scale`
with `Y₀ = E^γ`, `Y₀^{2d+1} = E^η`, `t ≤ E^{1-2η} ≤ t + 1` and
`b = ‖χ‖_{L̲²(B_{15 d E})} ≤ K |q| 15 d E^{1-δ}` is at most `c |q| E^{1-η}`. -/
theorem corrector_scale_arith (hd : 2 ≤ d) {E Y Q K C₀ κ δ η b : ℝ} {t : ℕ} (hE : 1 ≤ E)
    (hY1 : 1 ≤ Y) (hYE : Y ^ (2 * d + 1) = E ^ η) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (h2η : 2 * η * d = δ) (h3η : 3 * η ≤ δ)
    (hη4 : η ≤ 1 / 4) (ht : (t : ℝ) ≤ E ^ (1 - 2 * η)) (ht1 : E ^ (1 - 2 * η) ≤ (t : ℝ) + 1)
    (hb0 : 0 ≤ b) (hbE : b ≤ K * Q * (15 * d) * E)
    (hbδ : b ≤ K * Q * (15 * d) * E ^ (1 - δ)) :
    7 ^ d * (3 * Y) ^ d * (2 * d * (2 * (2 * (3 * Y + 2) + 3) ^ d * C₀ *
        ((3 * Y + 2) / E) * (Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * b +
          Q * E) + Q)) +
      Real.sqrt (2 * (7 ^ d * (3 * Y) ^ d) * ((33 * d * E) ^ d * b ^ 2) /
          ((t : ℝ) + 1) ^ d +
        2 * (d * t * (7 ^ d * (3 * Y) ^ d * (2 * d * (2 * (2 * (3 * Y + 2) + 3) ^ d * C₀ *
          ((3 * Y + 2) / E) * (Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * b +
            Q * E) + Q)))) ^ 2) ≤
      (2 * d * 21 ^ d * (10 * 13 ^ d * C₀ *
          (15 * d * Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * K + 1) + 1) +
        Real.sqrt (2 * 21 ^ d * (33 * d) ^ d * (15 * d * K) ^ 2) +
        Real.sqrt 2 * d * (2 * d * 21 ^ d * (10 * 13 ^ d * C₀ *
          (15 * d * Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * K + 1) + 1))) *
        Q * E ^ (1 - η) := by
  have hE0 : 0 < E := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set cr := Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) with hcr
  have hcr0 : 0 ≤ cr := Real.sqrt_nonneg _
  set cL := 10 * 13 ^ d * C₀ * (15 * d * cr * K + 1) + 1 with hcL
  have hcL0 : 0 ≤ cL := by positivity
  set c₁ := 2 * d * 21 ^ d * cL with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set c₂ := 2 * 21 ^ d * (33 * d) ^ d * (15 * d * K) ^ 2 with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  set ρ := 3 * Y + 2 with hρ
  have hρY : ρ ≤ 5 * Y := by linarith
  have hρ3 : 2 * ρ + 3 ≤ 13 * Y := by linarith
  -- the increments
  set L := 2 * (2 * ρ + 3) ^ d * C₀ * (ρ / E) * (cr * b + Q * E) + Q with hL
  have hYd1 : 1 ≤ Y ^ (d + 1) := one_le_pow₀ hY1
  have hL' : L ≤ cL * Q * Y ^ (d + 1) := by
    have h1 : cr * b + Q * E ≤ (15 * d * cr * K + 1) * Q * E := by
      have := mul_le_mul_of_nonneg_left hbE hcr0
      nlinarith
    have h2 : (ρ / E) * (cr * b + Q * E) ≤ 5 * Y * ((15 * d * cr * K + 1) * Q) := by
      calc (ρ / E) * (cr * b + Q * E) ≤ (5 * Y / E) * ((15 * d * cr * K + 1) * Q * E) := by
            gcongr
        _ = 5 * Y * ((15 * d * cr * K + 1) * Q) := by
            rw [div_mul_eq_mul_div, div_eq_iff hE0.ne']; ring
    have h3 : (2 * ρ + 3) ^ d ≤ 13 ^ d * Y ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hρ3 d
    have h4 : 2 * (2 * ρ + 3) ^ d * C₀ * ((ρ / E) * (cr * b + Q * E)) ≤
        2 * (13 ^ d * Y ^ d) * C₀ * (5 * Y * ((15 * d * cr * K + 1) * Q)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) hC₀) h2
        (by positivity) (by positivity)
    have e : 2 * (13 ^ d * Y ^ d) * C₀ * (5 * Y * ((15 * d * cr * K + 1) * Q)) =
        (10 * 13 ^ d * C₀ * (15 * d * cr * K + 1)) * Q * Y ^ (d + 1) := by
      rw [pow_succ]; ring
    have hQY : Q ≤ Q * Y ^ (d + 1) := le_mul_of_one_le_right hQ hYd1
    calc L = 2 * (2 * ρ + 3) ^ d * C₀ * ((ρ / E) * (cr * b + Q * E)) + Q := by rw [hL]; ring
      _ ≤ (10 * 13 ^ d * C₀ * (15 * d * cr * K + 1)) * Q * Y ^ (d + 1) + Q * Y ^ (d + 1) := by
          rw [← e]; linarith
      _ = cL * Q * Y ^ (d + 1) := by rw [hcL]; ring
  have hL0 : 0 ≤ L := by positivity
  -- the coarse increments
  set L₁ := 7 ^ d * (3 * Y) ^ d * (2 * d * L) with hL₁
  have hEη : E ^ η ≤ E ^ (1 - η) := Real.rpow_le_rpow_of_exponent_le hE (by linarith)
  have hL₁' : L₁ ≤ c₁ * Q * E ^ η := by
    have e1 : (7 : ℝ) ^ d * (3 * Y) ^ d = 21 ^ d * Y ^ d := by rw [mul_pow, ← mul_assoc, ← mul_pow]; norm_num
    rw [hL₁, e1, ← hYE]
    calc 21 ^ d * Y ^ d * (2 * d * L) ≤ 21 ^ d * Y ^ d * (2 * d * (cL * Q * Y ^ (d + 1))) := by
          gcongr
      _ = c₁ * Q * Y ^ (2 * d + 1) := by
          rw [hc₁, show 2 * d + 1 = d + (d + 1) by ring, pow_add]; ring
  have hL₁0 : 0 ≤ L₁ := by positivity
  -- the second term
  set T₂ := 2 * (d * t * L₁) ^ 2 with hT₂
  have hT₂' : T₂ ≤ (Real.sqrt 2 * d * c₁ * Q * E ^ (1 - η)) ^ 2 := by
    have h1 : (t : ℝ) * L₁ ≤ E ^ (1 - 2 * η) * (c₁ * Q * E ^ η) :=
      mul_le_mul ht hL₁' hL₁0 (by positivity)
    have h2 : E ^ (1 - 2 * η) * E ^ η = E ^ (1 - η) := by
      rw [← Real.rpow_add hE0]; ring_nf
    have h3 : d * t * L₁ ≤ d * c₁ * Q * E ^ (1 - η) := by
      calc d * t * L₁ = d * ((t : ℝ) * L₁) := by ring
        _ ≤ d * (E ^ (1 - 2 * η) * (c₁ * Q * E ^ η)) := by gcongr
        _ = d * c₁ * Q * (E ^ (1 - 2 * η) * E ^ η) := by ring
        _ = d * c₁ * Q * E ^ (1 - η) := by rw [h2]
    have h4 : (d * t * L₁) ^ 2 ≤ (d * c₁ * Q * E ^ (1 - η)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3 2
    have e : (Real.sqrt 2 * d * c₁ * Q * E ^ (1 - η)) ^ 2 = 2 * (d * c₁ * Q * E ^ (1 - η)) ^ 2 := by
      rw [show Real.sqrt 2 * d * c₁ * Q * E ^ (1 - η) = Real.sqrt 2 * (d * c₁ * Q * E ^ (1 - η)) by
        ring, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [hT₂, e]
    linarith
  -- the first term
  set T₁ := 2 * (7 ^ d * (3 * Y) ^ d) * ((33 * d * E) ^ d * b ^ 2) / ((t : ℝ) + 1) ^ d
    with hT₁
  have hT₁' : T₁ ≤ (Real.sqrt c₂ * Q * E ^ (1 - η)) ^ 2 := by
    have e1 : (7 : ℝ) ^ d * (3 * Y) ^ d = 21 ^ d * Y ^ d := by
      rw [mul_pow, ← mul_assoc, ← mul_pow]; norm_num
    have hYd : Y ^ d ≤ E ^ η := by
      rw [← hYE]; exact pow_le_pow_right₀ hY1 (by omega)
    have hb2 : b ^ 2 ≤ (K * Q * (15 * d)) ^ 2 * E ^ ((1 - δ) * 2) := by
      have h := pow_le_pow_left₀ hb0 hbδ 2
      rw [mul_pow, ← Real.rpow_natCast (E ^ (1 - δ)), ← Real.rpow_mul hE0.le] at h
      simpa using h
    have htd : E ^ ((1 - 2 * η) * d) ≤ ((t : ℝ) + 1) ^ d := by
      rw [Real.rpow_mul hE0.le, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) ht1 d
    have hEd : E ^ d = E ^ (d : ℝ) := (Real.rpow_natCast E d).symm
    have hpos : 0 < E ^ ((1 - 2 * η) * d) := Real.rpow_pos_of_pos hE0 _
    have hcomb : E ^ (d : ℝ) * E ^ ((1 - δ) * 2) / E ^ ((1 - 2 * η) * d) = E ^ (2 - δ) := by
      rw [← Real.rpow_add hE0, ← Real.rpow_sub hE0]
      congr 1
      linear_combination h2η
    have hnum : 2 * (7 ^ d * (3 * Y) ^ d) * ((33 * d * E) ^ d * b ^ 2) ≤
        2 * 21 ^ d * E ^ η * (33 * d) ^ d * (K * Q * (15 * d)) ^ 2 *
          (E ^ (d : ℝ) * E ^ ((1 - δ) * 2)) := by
      rw [e1, mul_pow, hEd]
      have h0 : 0 ≤ E ^ (d : ℝ) := by positivity
      calc 2 * (21 ^ d * Y ^ d) * ((33 * d) ^ d * E ^ (d : ℝ) * b ^ 2)
          ≤ 2 * (21 ^ d * E ^ η) * ((33 * d) ^ d * E ^ (d : ℝ) *
              ((K * Q * (15 * d)) ^ 2 * E ^ ((1 - δ) * 2))) := by
            gcongr
        _ = _ := by ring
    have hT₁a : T₁ ≤ 2 * 21 ^ d * E ^ η * (33 * d) ^ d * (K * Q * (15 * d)) ^ 2 *
        (E ^ (d : ℝ) * E ^ ((1 - δ) * 2)) / E ^ ((1 - 2 * η) * d) := by
      rw [hT₁]
      exact div_le_div₀ (by positivity) hnum hpos htd
    have e2 : 2 * 21 ^ d * E ^ η * (33 * d) ^ d * (K * Q * (15 * d)) ^ 2 *
        (E ^ (d : ℝ) * E ^ ((1 - δ) * 2)) / E ^ ((1 - 2 * η) * d) =
        c₂ * Q ^ 2 * (E ^ η * E ^ (2 - δ)) := by
      rw [mul_div_assoc, hcomb, hc₂]; ring
    have h3 : E ^ η * E ^ (2 - δ) ≤ E ^ ((1 - η) * 2) := by
      rw [← Real.rpow_add hE0]
      exact Real.rpow_le_rpow_of_exponent_le hE (by linarith)
    have e3 : (Real.sqrt c₂ * Q * E ^ (1 - η)) ^ 2 = c₂ * Q ^ 2 * E ^ ((1 - η) * 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hc₂0, ← Real.rpow_natCast (E ^ (1 - η)),
        ← Real.rpow_mul hE0.le]
      norm_num
    rw [e3]
    refine hT₁a.trans ?_
    rw [e2]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  -- the square root
  have hsq : Real.sqrt (T₁ + T₂) ≤ Real.sqrt c₂ * Q * E ^ (1 - η) +
      Real.sqrt 2 * d * c₁ * Q * E ^ (1 - η) := by
    have ha : 0 ≤ Real.sqrt c₂ * Q * E ^ (1 - η) := by positivity
    have hb' : 0 ≤ Real.sqrt 2 * d * c₁ * Q * E ^ (1 - η) := by positivity
    rw [Real.sqrt_le_left (by positivity)]
    calc T₁ + T₂ ≤ (Real.sqrt c₂ * Q * E ^ (1 - η)) ^ 2 +
          (Real.sqrt 2 * d * c₁ * Q * E ^ (1 - η)) ^ 2 := add_le_add hT₁' hT₂'
      _ ≤ _ := by
          rw [add_sq]
          linarith [mul_nonneg ha hb']
  have hfinal : L₁ ≤ c₁ * Q * E ^ (1 - η) :=
    hL₁'.trans (mul_le_mul_of_nonneg_left hEη (by positivity))
  calc L₁ + Real.sqrt (T₁ + T₂)
      ≤ c₁ * Q * E ^ (1 - η) + (Real.sqrt c₂ * Q * E ^ (1 - η) +
          Real.sqrt 2 * d * c₁ * Q * E ^ (1 - η)) := add_le_add hfinal hsq
    _ = (c₁ + Real.sqrt c₂ + Real.sqrt 2 * d * c₁) * Q * E ^ (1 - η) := by ring

end Rigidity.Proofs.Regularity.GeneralDim
