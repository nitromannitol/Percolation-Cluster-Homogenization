import PercolationClusterHomogenization.Proofs.Regularity.GeneralMesoscopicTwoTopBounds
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicTwoMain

/-!
# Lemma 7.3 at `k = 2` in every dimension, for one configuration

`mesoscopicDegreeTwo_coreD`: for one configuration of `ℤᵈ` with a unique infinite cluster `𝒞_∞`
and the partition into good cubes, under the conclusion of Lemma 7.1 of Armstrong and Dario
(arXiv:1609.09431v2) in the ball form of the proof of Lemma 7.3 (`CubeHarmonicApproximationAt`),
bounds on the partition cubes in `B_R` (sides at most `S'` with `(4 √d S')^{d/2} ≤ c R^{α/2}` and
`√d S' ≤ R / 4`, moments `∑ 3^s ≤ K₁ R^d` and `∑ 3^{d s} ≤ K₂ R^d`) and the density of `𝒞_∞` in
cubes, the estimate (7.18) at `k = 2` holds on `[r₀ X, R / 2]` with `δ = α / 2`:
`D̃_2(r) ≤ C (r / R)³ D̃_2(R) + C r^{-α/2} (r / R) ‖u‖_R`, with `D̃_2(r)` the excess of `u` over the
harmonic quadratic polynomials in the normalization `‖·‖_r = r^{-d/2} ‖·‖_{ℓ²(𝒞_∞ ∩ B_r)}`.

The proof follows the source as in the plane (`mesoscopicDegreeTwo_core`): Lemma 7.2 at `k = 2`
and `k = 0` for `[u]_𝒫` on the balls of `ℤᵈ` up to the top scale `T = R / (8A)`
(`armstrongDario_lemma_7_2_two_latticeHarmonicD`, `armstrongDario_lemma_7_2_zero_latticeHarmonic`),
the top-scale bounds (`coarse_top_boundsD`, `harmonicApproximation_error_leD`), Step 1
(`clusterExcess_two_leD`, `clusterExcess_zero_leD`) to return to `u`, and the Lipschitz bound
`D̃_0(s) ≤ C s R^{-1} D̃_0(R)` proved first by an induction over the scales `s, A s, A² s, …`.
The radius factors between balls are `(t / s)^{d/2}` (`clusterBallVolumeL2_le_sqrt_mul`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The excess of a cluster function over a family, on a smaller ball. -/
theorem iInf_clusterBallVolumeL2_le_of_leD {ι : Type*} [Nonempty ι] (C : OpenComponent ω)
    {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) (u : C → ℝ) (w : ι → C → ℝ) :
    (⨅ i, clusterBallVolumeL2 C s (u - w i)) ≤
      0 + Real.sqrt ((R / s) ^ d) * ⨅ i, clusterBallVolumeL2 C R (u - w i) :=
  le_add_mul_iInf (Real.sqrt_nonneg _) fun i => by
    rw [zero_add]
    exact (iInf_le_of_le (fun _ => Real.sqrt_nonneg _) i).trans
      (clusterBallVolumeL2_le_sqrt_mul C hs hsR _)

/-- The harmonic approximation error at the top scale. -/
theorem coarse_error_le_auxD {T R α c Kq G : ℝ} (hT1 : 1 ≤ T) (h4T : 4 * T ≤ R) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hc : 0 ≤ c) (hKq : 0 ≤ Kq) (hG : 0 ≤ G) :
    (4 * T) ^ (1 - α) * (2 * (c * R ^ (α / 2)) * G + Kq * G / T) ≤
      (2 * c + Kq) * R ^ (1 - α / 2) * G := by
  have hT0 : 0 < T := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have h1 : (4 * T) ^ (1 - α) ≤ R ^ (1 - α) :=
    Real.rpow_le_rpow (by positivity) h4T (by linarith)
  have h2 : R ^ (1 - α) ≤ R ^ (1 - α / 2) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have h3 : R ^ (1 - α) * R ^ (α / 2) = R ^ (1 - α / 2) := by
    rw [← Real.rpow_add hR0]; congr 1; ring
  have hKT : Kq * G / T ≤ Kq * G := div_le_self (by positivity) hT1
  have hR10 : 0 ≤ R ^ (1 - α) := by positivity
  calc (4 * T) ^ (1 - α) * (2 * (c * R ^ (α / 2)) * G + Kq * G / T)
      ≤ R ^ (1 - α) * (2 * (c * R ^ (α / 2)) * G + Kq * G) :=
        mul_le_mul h1 (by linarith) (by positivity) hR10
    _ = 2 * c * G * (R ^ (1 - α) * R ^ (α / 2)) + Kq * G * R ^ (1 - α) := by ring
    _ ≤ 2 * c * G * R ^ (1 - α / 2) + Kq * G * R ^ (1 - α / 2) := by
        rw [h3]
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Kq * G)
        linarith
    _ = (2 * c + Kq) * R ^ (1 - α / 2) * G := by ring

/-- The oscillation of the coarsening at the top scale. -/
theorem top_zero_auxD {Ct Ca B' D0R D0T R A T Q G C₃ : ℝ} (hA0 : 0 < A) (hR0 : 0 < R)
    (hT : T = R / (8 * A)) (hG : G = D0R / R) (hCt : 0 ≤ Ct)
    (hC₃ : C₃ = 8 * A * (Ct * Q + Ca))
    (hD0T : D0T ≤ Ct * B' + Ca * D0R) (hB'R : B' ≤ Q * R * G) :
    D0T / T ≤ C₃ * G := by
  have hT0 : 0 < T := by rw [hT]; positivity
  rw [div_le_iff₀ hT0]
  have hD0RG : D0R = R * G := by
    rw [hG, mul_div_assoc', eq_div_iff hR0.ne']; ring
  have e : C₃ * G * T = (Ct * Q + Ca) * R * G := by
    rw [hC₃, hT, mul_div_assoc', div_eq_iff (by positivity)]; ring
  rw [e]
  have h1 : Ct * B' ≤ Ct * (Q * R * G) := mul_le_mul_of_nonneg_left hB'R hCt
  rw [hD0RG] at hD0T
  calc D0T ≤ Ct * B' + Ca * (R * G) := hD0T
    _ ≤ Ct * (Q * R * G) + Ca * (R * G) := by linarith
    _ = (Ct * Q + Ca) * R * G := by ring

/-- Lemma 7.2 at `k = 0` below the top scale, with the top-scale bounds inserted. -/
theorem zero_step_auxD {C₀ C₃ C₄ cE G ρ T D0T ET EX α : ℝ}
    (hC₄ : C₄ = C₀ * (2 * C₃ + cE)) (hρ1 : 1 ≤ ρ) (hα0 : 0 < α)
    (hT0 : 0 < T) (hC₀ : 0 ≤ C₀) (hcE : 0 ≤ cE) (hG : 0 ≤ G) (hD0T0 : 0 ≤ D0T) (hET0 : 0 ≤ ET)
    (hD0TT : D0T / T ≤ C₃ * G) (hETG : ET ≤ cE * G)
    (hEX : EX ≤ C₀ * (ρ / T) * D0T + C₀ * ρ ^ (1 - α) * (D0T / T + ET / ρ)) :
    EX ≤ C₄ * ρ * G := by
  have hρ0 : 0 < ρ := by linarith
  have hρα : ρ ^ (1 - α) ≤ ρ := by
    calc ρ ^ (1 - α) ≤ ρ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
      _ = ρ := Real.rpow_one ρ
  have hD0T0' : 0 ≤ D0T / T := div_nonneg hD0T0 hT0.le
  have h2 : C₀ * (ρ / T) * D0T ≤ C₀ * ρ * (C₃ * G) := by
    have e : C₀ * (ρ / T) * D0T = C₀ * ρ * (D0T / T) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hD0TT (by positivity)
  have h3 : ρ ^ (1 - α) * (D0T / T) ≤ ρ * (C₃ * G) := mul_le_mul hρα hD0TT hD0T0' hρ0.le
  have h4 : ρ ^ (1 - α) * (ET / ρ) ≤ cE * G * ρ := by
    have h5 : ρ ^ (1 - α) / ρ ≤ 1 := (div_le_one hρ0).2 hρα
    have e : ρ ^ (1 - α) * (ET / ρ) = ρ ^ (1 - α) / ρ * ET := by ring
    rw [e]
    have h6 : ρ ^ (1 - α) / ρ * ET ≤ ET := by
      have := mul_le_mul_of_nonneg_right h5 hET0; linarith
    have h7 : cE * G ≤ cE * G * ρ :=
      le_mul_of_one_le_right (by positivity) hρ1
    linarith
  have h8 : C₀ * ρ ^ (1 - α) * (D0T / T + ET / ρ) ≤
      C₀ * (ρ * (C₃ * G) + cE * G * ρ) := by
    have e : C₀ * ρ ^ (1 - α) * (D0T / T + ET / ρ) =
        C₀ * (ρ ^ (1 - α) * (D0T / T) + ρ ^ (1 - α) * (ET / ρ)) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) hC₀
  have e2 : C₄ * ρ * G =
      C₀ * ρ * (C₃ * G) + C₀ * (ρ * (C₃ * G) + cE * G * ρ) := by rw [hC₄]; ring
  rw [e2]
  linarith


/-- The assembly below the top scale. -/
theorem below_top_auxD {r R T A α K Q cE c₃ Ct Ca Cb C₂ C₃ C₅ C G D2R D2T D0T ET B' N Dr CCr EXr : ℝ}
    (hr1 : 1 ≤ r) (hrR : r ≤ R) (hA0 : 0 < A) (hT : T = R / (8 * A)) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hcE : 0 ≤ cE) (hc₃ : 0 ≤ c₃) (hCt : 0 ≤ Ct)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hC₂ : 0 ≤ C₂) (hC₅ : 0 ≤ C₅) (hG : 0 ≤ G) (hD2R : 0 ≤ D2R)
    (hD0T : 0 ≤ D0T) (hET : 0 ≤ ET) (hB' : B' = Q * R ^ (1 - α / 2) * G)
    (hGN : G ≤ N / R) (hC6 : c₃ * C₂ * (8 * A) ^ 3 * Ca ≤ C)
    (hC7 : K * A * C₅ + c₃ * C₂ * (8 * A) ^ 3 * (Ct * Q + Cb) +
      c₃ * C₂ * (C₃ + cE) ≤ C)
    (h1 : Dr ≤ CCr + c₃ * EXr) (hcc : CCr ≤ K * A * C₅ * G)
    (h4 : EXr ≤ C₂ * (r / T) ^ 3 * D2T + C₂ * r ^ (1 - α) * (D0T / T + ET / r))
    (hD2T : D2T ≤ Ct * B' + Ca * D2R + Cb * G) (hD0TT : D0T / T ≤ C₃ * G)
    (hETG : ET ≤ cE * G) :
    Dr ≤ C * (r / R) ^ 3 * D2R + C * r ^ (-(α / 2)) * (r / R) * N := by
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by linarith
  have hT0 : 0 < T := by rw [hT]; positivity
  have hrβ1 : 1 ≤ r ^ (1 - α / 2) := Real.one_le_rpow hr1 (by linarith)
  have hrβ0 : 0 ≤ r ^ (1 - α / 2) := by linarith
  have hrT3 : (r / T) ^ 3 = (8 * A) ^ 3 * (r / R) ^ 3 := by
    rw [hT, ← mul_pow, div_div_eq_mul_div, mul_div_assoc', mul_comm r (8 * A)]
  have hrR3 : (r / R) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hR0).2 hrR)
  have hrR30 : 0 ≤ (r / R) ^ 3 := by positivity
  have hcube := rpow_cube_le hr1 hrR (by linarith : 0 ≤ α / 2)
  -- the top term
  have hB'r : (r / R) ^ 3 * B' ≤ Q * r ^ (1 - α / 2) * G := by
    have e : (r / R) ^ 3 * B' = Q * G * ((r / R) ^ 3 * R ^ (1 - α / 2)) := by
      rw [hB']; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ Q * G)
    calc Q * G * ((r / R) ^ 3 * R ^ (1 - α / 2))
        ≤ Q * G * r ^ (1 - α / 2) := this
      _ = Q * r ^ (1 - α / 2) * G := by ring
  have hGr : (r / R) ^ 3 * G ≤ r ^ (1 - α / 2) * G :=
    mul_le_mul_of_nonneg_right (hrR3.trans hrβ1) hG
  have h6 : (r / R) ^ 3 * D2T ≤ (r / R) ^ 3 * (Ct * B' + Ca * D2R + Cb * G) :=
    mul_le_mul_of_nonneg_left hD2T hrR30
  have h7 : Ct * ((r / R) ^ 3 * B') ≤ Ct * (Q * r ^ (1 - α / 2) * G) :=
    mul_le_mul_of_nonneg_left hB'r hCt
  have h8 : Cb * ((r / R) ^ 3 * G) ≤ Cb * (r ^ (1 - α / 2) * G) :=
    mul_le_mul_of_nonneg_left hGr hCb
  have h9 : (r / R) ^ 3 * D2T ≤ (Ct * Q + Cb) * (r ^ (1 - α / 2) * G) +
      Ca * ((r / R) ^ 3 * D2R) := by
    have e : (r / R) ^ 3 * (Ct * B' + Ca * D2R + Cb * G) =
        Ct * ((r / R) ^ 3 * B') + Ca * ((r / R) ^ 3 * D2R) + Cb * ((r / R) ^ 3 * G) := by ring
    have e2 : Ct * (Q * r ^ (1 - α / 2) * G) + Cb * (r ^ (1 - α / 2) * G) =
        (Ct * Q + Cb) * (r ^ (1 - α / 2) * G) := by ring
    rw [e] at h6
    linarith
  have h5 : C₂ * (r / T) ^ 3 * D2T ≤ C₂ * (8 * A) ^ 3 * ((Ct * Q + Cb) *
      (r ^ (1 - α / 2) * G) + Ca * ((r / R) ^ 3 * D2R)) := by
    rw [hrT3]
    have := mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ C₂ * (8 * A) ^ 3)
    calc C₂ * ((8 * A) ^ 3 * (r / R) ^ 3) * D2T =
          C₂ * (8 * A) ^ 3 * ((r / R) ^ 3 * D2T) := by ring
      _ ≤ _ := this
  -- the error term
  have hrα : r ^ (1 - α) ≤ r ^ (1 - α / 2) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hrα1 : r ^ (1 - α) ≤ r := by
    calc r ^ (1 - α) ≤ r ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
      _ = r := Real.rpow_one r
  have hD0T0 : 0 ≤ D0T / T := div_nonneg hD0T hT0.le
  have h10 : r ^ (1 - α) * (D0T / T) ≤ r ^ (1 - α / 2) * (C₃ * G) :=
    mul_le_mul hrα hD0TT hD0T0 hrβ0
  have h11 : r ^ (1 - α) * (ET / r) ≤ cE * G * r ^ (1 - α / 2) := by
    have h5 : r ^ (1 - α) / r ≤ 1 := (div_le_one hr0).2 hrα1
    have e : r ^ (1 - α) * (ET / r) = r ^ (1 - α) / r * ET := by ring
    rw [e]
    have h6 : r ^ (1 - α) / r * ET ≤ ET := by
      have := mul_le_mul_of_nonneg_right h5 hET; linarith
    have h7 : cE * G ≤ cE * G * r ^ (1 - α / 2) :=
      le_mul_of_one_le_right (by positivity) hrβ1
    linarith
  have h12 : C₂ * r ^ (1 - α) * (D0T / T + ET / r) ≤
      C₂ * (C₃ + cE) * (r ^ (1 - α / 2) * G) := by
    have e : C₂ * r ^ (1 - α) * (D0T / T + ET / r) =
        C₂ * (r ^ (1 - α) * (D0T / T) + r ^ (1 - α) * (ET / r)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (add_le_add h10 h11) hC₂
    calc _ ≤ _ := this
      _ = C₂ * (C₃ + cE) * (r ^ (1 - α / 2) * G) := by ring
  have hKA : K * A * C₅ * G ≤ K * A * C₅ * (r ^ (1 - α / 2) * G) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hG hrβ1) (by positivity)
  -- assemble
  have hP0 : 0 ≤ r ^ (1 - α / 2) * G := mul_nonneg hrβ0 hG
  have hQ0 : 0 ≤ (r / R) ^ 3 * D2R := mul_nonneg hrR30 hD2R
  have hsum : Dr ≤ (c₃ * C₂ * (8 * A) ^ 3 * Ca) * ((r / R) ^ 3 * D2R) +
      (K * A * C₅ + c₃ * C₂ * (8 * A) ^ 3 * (Ct * Q + Cb) +
        c₃ * C₂ * (C₃ + cE)) * (r ^ (1 - α / 2) * G) := by
    have h14 := h4.trans (add_le_add h5 h12)
    have h14' := mul_le_mul_of_nonneg_left h14 hc₃
    have e : c₃ * (C₂ * (8 * A) ^ 3 * ((Ct * Q + Cb) * (r ^ (1 - α / 2) * G) +
        Ca * ((r / R) ^ 3 * D2R)) + C₂ * (C₃ + cE) * (r ^ (1 - α / 2) * G)) =
        (c₃ * C₂ * (8 * A) ^ 3 * Ca) * ((r / R) ^ 3 * D2R) +
          (c₃ * C₂ * (8 * A) ^ 3 * (Ct * Q + Cb) + c₃ * C₂ * (C₃ + cE)) *
            (r ^ (1 - α / 2) * G) := by ring
    linarith
  have hrβ : r ^ (1 - α / 2) * G ≤ r ^ (-(α / 2)) * (r / R) * N := by
    have e : r ^ (1 - α / 2) = r * r ^ (-(α / 2)) := by
      rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]
    rw [e]
    have := mul_le_mul_of_nonneg_left hGN (by positivity : (0 : ℝ) ≤ r * r ^ (-(α / 2)))
    calc r * r ^ (-(α / 2)) * G ≤ r * r ^ (-(α / 2)) * (N / R) := this
      _ = r ^ (-(α / 2)) * (r / R) * N := by ring
  have hC0 : 0 ≤ C := le_trans (by positivity) hC6
  have h15 := mul_le_mul_of_nonneg_right hC6 hQ0
  have h16 := mul_le_mul_of_nonneg_right hC7 hP0
  have h17 : C * (r ^ (1 - α / 2) * G) ≤ C * (r ^ (-(α / 2)) * (r / R) * N) :=
    mul_le_mul_of_nonneg_left hrβ hC0
  have e1 : C * (r / R) ^ 3 * D2R = C * ((r / R) ^ 3 * D2R) := by ring
  have e2 : C * r ^ (-(α / 2)) * (r / R) * N = C * (r ^ (-(α / 2)) * (r / R) * N) := by ring
  rw [e1, e2]
  linarith


/-- The crude bound above the top scale. -/
theorem base_auxD {f R s D0R A G : ℝ} (hs : 0 < s) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hRs : R ≤ 16 * A * s) (hD : D0R = R * G) (h : f ≤ 0 + Real.sqrt ((R / s) ^ d) * D0R) :
    f ≤ Real.sqrt ((16 * A) ^ d) * (16 * A) * s * G := by
  have hRs' : R / s ≤ 16 * A := by rw [div_le_iff₀ hs]; linarith
  have h1 : Real.sqrt ((R / s) ^ d) ≤ Real.sqrt ((16 * A) ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (div_nonneg hR hs.le) hRs' d)
  have h2 : D0R ≤ 16 * A * s * G := by rw [hD]; exact mul_le_mul_of_nonneg_right hRs hG
  have hD0 : 0 ≤ D0R := by rw [hD]; positivity
  rw [zero_add] at h
  calc f ≤ Real.sqrt ((R / s) ^ d) * D0R := h
    _ ≤ Real.sqrt ((16 * A) ^ d) * (16 * A * s * G) :=
        mul_le_mul h1 h2 hD0 (Real.sqrt_nonneg _)
    _ = Real.sqrt ((16 * A) ^ d) * (16 * A) * s * G := by ring

/-- **The induction over the scales `s, A s, A² s, …`** for the Lipschitz bound of order zero:
if `f(s) ≤ B₀ s G` above `T / 2` and `f(s) ≤ K s^{-1} f(A s) + c₃ C₄ s G` on `[s₁, T / 2]`
with `s₁ > 2 K A`, then `f(s) ≤ max B₀ (2 c₃ C₄) s G` on `[s₁, R / 2]`. -/
theorem le_of_scale_inductionD {f : ℝ → ℝ} {A K s₁ T R C₄ G B₀ c₃ : ℝ} (hA : 2 ≤ A) (hK : 0 ≤ K)
    (hG : 0 ≤ G) (hB₀ : 0 ≤ B₀) (hs₁ : 2 * K * A < s₁) (hs₁0 : 0 < s₁)
    (hAT : A * (T / 2) ≤ R / 2)
    (hbase : ∀ s, T / 2 < s → s ≤ R / 2 → f s ≤ B₀ * s * G)
    (hstep : ∀ s, s₁ ≤ s → s ≤ T / 2 → f s ≤ K / s * f (A * s) + c₃ * C₄ * s * G) :
    ∀ s, s₁ ≤ s → s ≤ R / 2 → f s ≤ max B₀ (2 * c₃ * C₄) * s * G := by
  set C₅ := max B₀ (2 * c₃ * C₄) with hC₅
  have hA0 : 0 < A := by linarith
  have hA1 : 1 < A := by linarith
  have hC₅0 : 0 ≤ C₅ := hB₀.trans (le_max_left _ _)
  have hclaim : ∀ n : ℕ, ∀ s, s₁ ≤ s → s ≤ R / 2 → T / 2 < A ^ n * s → f s ≤ C₅ * s * G := by
    intro n
    induction n with
    | zero =>
      intro s _ hsR hs
      rw [pow_zero, one_mul] at hs
      have := hbase s hs hsR
      have : B₀ * s * G ≤ C₅ * s * G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by linarith)) hG
      linarith
    | succ n ih =>
      intro s hs hsR hsn
      by_cases hsT : T / 2 < s
      · have := hbase s hsT hsR
        have : B₀ * s * G ≤ C₅ * s * G :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by linarith)) hG
        linarith
      · push Not at hsT
        have hs0 : 0 < s := hs₁0.trans_le hs
        have hAs1 : s₁ ≤ A * s := hs.trans (le_mul_of_one_le_left hs0.le hA1.le)
        have hAsR : A * s ≤ R / 2 := (mul_le_mul_of_nonneg_left hsT hA0.le).trans hAT
        have hAsn : T / 2 < A ^ n * (A * s) := by rw [← mul_assoc, ← pow_succ]; exact hsn
        have hih := ih (A * s) hAs1 hAsR hAsn
        have h1 := hstep s hs hsT
        have hKs : 0 ≤ K / s := div_nonneg hK hs0.le
        have h2 : K / s * f (A * s) ≤ K / s * (C₅ * (A * s) * G) :=
          mul_le_mul_of_nonneg_left hih hKs
        have h3 : K / s * (C₅ * (A * s) * G) = K * A * C₅ * G := by field_simp
        have h4 : K * A * C₅ * G ≤ C₅ * s * G / 2 := by
          have : 2 * K * A ≤ s := by linarith
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hC₅0 hG)
          nlinarith
        have h5 : c₃ * C₄ * s * G ≤ C₅ * s * G / 2 := by
          have : 2 * c₃ * C₄ ≤ C₅ := le_max_right _ _
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hs0.le hG)
          nlinarith
        linarith
  intro s hs hsR
  have hs0 : 0 < s := hs₁0.trans_le hs
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T / 2 / s) hA1
  exact hclaim n s hs hsR (by rwa [div_lt_iff₀ hs0] at hn)


/-- The crude bound near the top scale. -/
theorem near_top_auxD {r R T A α C Dr D2R N : ℝ} (hA : 2 ≤ A) (hr0 : 0 < r) (hR0 : 0 < R)
    (hT : T = R / (8 * A)) (hrT : T / 2 < r) (hD2R : 0 ≤ D2R) (hN : 0 ≤ N)
    (hC : Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 ≤ C)
    (h1 : Dr ≤ 0 + Real.sqrt ((R / r) ^ d) * D2R) :
    Dr ≤ C * (r / R) ^ 3 * D2R + C * r ^ (-(α / 2)) * (r / R) * N := by
  have hA0 : 0 < A := by linarith
  rw [hT] at hrT
  have hRr16 := lt_mul_of_half_div_lt hA hrT
  have hRr : R / r ≤ 16 * A := by rw [div_le_iff₀ hr0]; exact hRr16.le
  have hrR : 1 ≤ (16 * A) ^ 3 * (r / R) ^ 3 := by
    rw [← mul_pow]
    apply one_le_pow₀
    rw [mul_div_assoc', le_div_iff₀ hR0]
    linarith
  have hs : Real.sqrt ((R / r) ^ d) ≤ Real.sqrt ((16 * A) ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hRr d)
  have h2 : Real.sqrt ((R / r) ^ d) * D2R ≤ Real.sqrt ((16 * A) ^ d) * D2R :=
    mul_le_mul_of_nonneg_right hs hD2R
  have h3 : Real.sqrt ((16 * A) ^ d) * D2R ≤
      Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 * (r / R) ^ 3 * D2R := by
    have := mul_le_mul_of_nonneg_left hrR
      (by positivity : (0 : ℝ) ≤ Real.sqrt ((16 * A) ^ d) * D2R)
    calc Real.sqrt ((16 * A) ^ d) * D2R = Real.sqrt ((16 * A) ^ d) * D2R * 1 := by ring
      _ ≤ Real.sqrt ((16 * A) ^ d) * D2R * ((16 * A) ^ 3 * (r / R) ^ 3) := this
      _ = Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 * (r / R) ^ 3 * D2R := by ring
  have h4 : Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 * (r / R) ^ 3 * D2R ≤
      C * (r / R) ^ 3 * D2R := by
    have h0 : 0 ≤ (r / R) ^ 3 * D2R := by positivity
    have := mul_le_mul_of_nonneg_right hC h0
    calc Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 * (r / R) ^ 3 * D2R =
          Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 * ((r / R) ^ 3 * D2R) := by ring
      _ ≤ C * ((r / R) ^ 3 * D2R) := this
      _ = C * (r / R) ^ 3 * D2R := by ring
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  have h5 : 0 ≤ C * r ^ (-(α / 2)) * (r / R) * N := by positivity
  rw [zero_add] at h1
  linarith

/-- The lower scale of the lattice iterations in every dimension. -/
noncomputable def coreLatticeScaleD (d : ℕ) : ℝ :=
  max (latticeLemmaScaleCubic d) (max (latticeHRScale d) (24 * Real.sqrt d))

theorem one_le_coreLatticeScaleD (d : ℕ) : 1 ≤ coreLatticeScaleD d :=
  (one_le_latticeLemmaScaleCubic d).trans (le_max_left _ _)

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in every dimension, for one
configuration.** -/
theorem mesoscopicDegreeTwo_coreD [NeZero d] {A α K K₁ K₂ κ cS : ℝ} (hA : 2 ≤ A) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hκ : 0 < κ) (hcS : 0 ≤ cS) :
    ∃ C r₀ : ℝ, 0 < C ∧ 1 ≤ r₀ ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω)
      (h : HasUniqueInfiniteOpenComponent ω) (X ℓ R S' : ℝ) (u : uniqueInfiniteComponent h → ℝ),
      1 ≤ X → r₀ * X ≤ R → quadLocality d (capFraction d κ) * max ℓ 1 ≤ R →
      IsHarmonicInBall (uniqueInfiniteComponent h) R u →
      CubeHarmonicApproximationAt (uniqueInfiniteComponent h) A α K X →
      0 ≤ S' → Real.sqrt d * S' ≤ R / 4 →
      Real.sqrt ((4 * Real.sqrt d * S') ^ d) ≤ cS * R ^ (α / 2) →
      (∀ y : Vertex d,
        dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < R →
          (3 : ℝ) ^ (partitionCube ω y).scale ≤ S') →
      (∑ y ∈ latticeBallPointsD 0 R, (3 : ℝ) ^ (partitionCube ω y).scale ≤ K₁ * R ^ d) →
      (∑ y ∈ latticeBallPointsD 0 R, ((3 : ℝ) ^ (partitionCube ω y).scale) ^ d ≤ K₂ * R ^ d) →
      ClusterCubeDensity (uniqueInfiniteComponent h) 0 (quadLocality d (capFraction d κ)) ℓ κ →
      ∀ r : ℝ, r₀ * X ≤ r → r ≤ R / 2 →
        (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
            clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) ≤
          C * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
              clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w)) +
            C * r ^ (-(α / 2)) * (r / R) * clusterBallVolumeL2 (uniqueInfiniteComponent h) R u := by
  obtain ⟨C₂, hC₂, h72₂⟩ := armstrongDario_lemma_7_2_two_latticeHarmonicD d hA hα0
  obtain ⟨C₀, hC₀, h72₀⟩ := armstrongDario_lemma_7_2_zero_latticeHarmonic d hA hα0
  obtain ⟨Ca, Cb, hCa, hCb, htop⟩ := coarse_top_boundsD (d := d) hA hK₁ hK₂ hκ
  have hA0 : 0 < A := by linarith
  have hA2 : 1 ≤ 8 * A ^ 2 := by have := pow_le_pow_left₀ (by norm_num) hA 2; linarith
  set Ct := coarseTopConstD d with hCtdef
  have hCt0 : 0 ≤ Ct := coarseTopConstD_nonneg d
  obtain ⟨Xlat, hXlat⟩ : ∃ x : ℝ, x = coreLatticeScaleD d := ⟨_, rfl⟩
  have hXlat1 : 1 ≤ Xlat := hXlat ▸ one_le_coreLatticeScaleD d
  have hXlat2 : latticeLemmaScaleCubic d ≤ Xlat := by
    rw [hXlat, coreLatticeScaleD]; exact le_max_left _ _
  have hXlat3 : max (latticeHRScale d) (24 * Real.sqrt d) ≤ Xlat := by
    rw [hXlat, coreLatticeScaleD]; exact le_max_right _ _
  obtain ⟨Q, hQ⟩ : ∃ x : ℝ, x = 2 * cS + Real.sqrt (2 ^ d) * K := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  obtain ⟨cE, hcE⟩ : ∃ x : ℝ, x = K * (8 * A) * Real.sqrt ((8 * A) ^ d) := ⟨_, rfl⟩
  have hcE0 : 0 ≤ cE := by rw [hcE]; positivity
  obtain ⟨C₃, hC₃⟩ : ∃ x : ℝ, x = 8 * A * (Ct * Q + Ca) := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  obtain ⟨C₄, hC₄⟩ : ∃ x : ℝ, x = C₀ * (2 * C₃ + cE) := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ x : ℝ, x = Real.sqrt ((16 * A) ^ d) * (16 * A) := ⟨_, rfl⟩
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; positivity
  obtain ⟨c₃, hc₃⟩ : ∃ x : ℝ, x = (5 : ℝ) ^ d := ⟨_, rfl⟩
  have hc₃0 : 0 ≤ c₃ := by rw [hc₃]; positivity
  obtain ⟨C₅, hC₅⟩ : ∃ x : ℝ, x = max B₀ (2 * c₃ * C₄) := ⟨_, rfl⟩
  have hC₅0 : 0 ≤ C₅ := by rw [hC₅]; exact hB₀0.trans (le_max_left _ _)
  obtain ⟨ρ₁, hρ₁⟩ : ∃ x : ℝ, x = 2 * K * A + 1 := ⟨_, rfl⟩
  obtain ⟨r₀, hr₀⟩ : ∃ x : ℝ, x = max (8 * A ^ 2 * Xlat) (max (topScaleD d A) (max C₂ (max C₀
      (max ρ₁ 3)))) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ x : ℝ, x = c₃ * C₂ * (8 * A) ^ 3 * Ca + Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 +
      (K * A * C₅ + c₃ * C₂ * (8 * A) ^ 3 * (Ct * Q + Cb) + c₃ * C₂ * (C₃ + cE)) + 1 :=
    ⟨_, rfl⟩
  have hC6p : 0 ≤ c₃ * C₂ * (8 * A) ^ 3 * Ca := by positivity
  have hC7p : 0 ≤ K * A * C₅ + c₃ * C₂ * (8 * A) ^ 3 * (Ct * Q + Cb) + c₃ * C₂ * (C₃ + cE) := by
    positivity
  have hC16p : 0 ≤ Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 := by positivity
  have hC6 : c₃ * C₂ * (8 * A) ^ 3 * Ca ≤ C := by rw [hC]; linarith
  have hC7 : K * A * C₅ + c₃ * C₂ * (8 * A) ^ 3 * (Ct * Q + Cb) + c₃ * C₂ * (C₃ + cE) ≤ C := by
    rw [hC]; linarith
  have hC16 : Real.sqrt ((16 * A) ^ d) * (16 * A) ^ 3 ≤ C := by rw [hC]; linarith
  have hCpos : 0 < C := by rw [hC]; linarith
  have hr₀a : 8 * A ^ 2 * Xlat ≤ r₀ := by rw [hr₀]; exact le_max_left _ _
  have hr₀b : topScaleD d A ≤ r₀ := by rw [hr₀]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hr₀c : C₂ ≤ r₀ := by
    rw [hr₀]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hr₀d : C₀ ≤ r₀ := by
    rw [hr₀]; exact (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)
  have hr₀e : ρ₁ ≤ r₀ := by
    rw [hr₀]; exact ((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hr₀f : 3 ≤ r₀ := by
    rw [hr₀]; exact ((((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hr₀1 : 1 ≤ r₀ := by linarith
  have hXlatr₀ : Xlat ≤ r₀ := (le_mul_of_one_le_left (by linarith) hA2).trans hr₀a
  refine ⟨C, r₀, hCpos, hr₀1, ?_⟩
  intro ω hP h X ℓ R S' u hX hR hRq harm hca hS'0 hS' hS'c hsize hm₁ hm₂ hcube r hr hrR
  -- the scales
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hr₀R : r₀ ≤ R := le_trans (le_mul_of_one_le_right (zero_le_one.trans hr₀1) hX) hR
  have hr₀r : r₀ ≤ r := le_trans (le_mul_of_one_le_right (zero_le_one.trans hr₀1) hX) hr
  have hRtop : topScaleD d A ≤ R := hr₀b.trans hr₀R
  obtain ⟨-, -, hT3', -, hR1, hR4⟩ := topScaleD_facts hA hRtop
  have hR0 : 0 < R := by linarith
  have hr1 : 1 ≤ r := hr₀1.trans hr₀r
  have hr0 : 0 < r := by linarith
  have hrRle : r ≤ R := hrR.trans (half_le_self hR0.le)
  obtain ⟨T, hT⟩ : ∃ x : ℝ, x = R / (8 * A) := ⟨_, rfl⟩
  obtain ⟨hT0, hTR, hThalf, hAThalf, hRT, h4TR⟩ := scale_facts hA hR0 hT
  have hT1 : 1 ≤ T := by rw [hT]; linarith
  obtain ⟨X', hX'⟩ : ∃ x : ℝ, x = max X Xlat := ⟨_, rfl⟩
  have hXX' : X ≤ X' := by rw [hX']; exact le_max_left _ _
  have hXlatX' : Xlat ≤ X' := by rw [hX']; exact le_max_right _ _
  have hX'X : X' ≤ Xlat * X := by
    rw [hX']
    exact max_le (le_mul_of_one_le_left hX0 hXlat1)
      (le_mul_of_one_le_right (zero_le_one.trans hXlat1) hX)
  have hX'1 : 1 ≤ X' := hX.trans hXX'
  have hAX'T : A * X' ≤ T := by
    rw [hT, le_div_iff₀ (by positivity)]
    have h1 : 8 * A ^ 2 * Xlat * X ≤ R := (mul_le_mul_of_nonneg_right hr₀a hX0).trans hR
    have h2 := mul_le_mul_of_nonneg_left hX'X (by positivity : (0 : ℝ) ≤ 8 * A ^ 2)
    have e : A * X' * (8 * A) = 8 * A ^ 2 * X' := by ring
    have e2 : 8 * A ^ 2 * (Xlat * X) = 8 * A ^ 2 * Xlat * X := by ring
    rw [e]
    linarith
  have hX'T : X' ≤ T / A := by rw [le_div_iff₀ hA0]; linarith
  have hAXT : A * X ≤ T := (mul_le_mul_of_nonneg_left hXX' hA0.le).trans hAX'T
  have hX4T : X ≤ 4 * T := by
    have : X ≤ A * X := le_mul_of_one_le_left hX0 (by linarith)
    linarith
  -- the hypotheses at the radii `T`, `R / 2` and `R`
  obtain ⟨HA_T, -, -⟩ := hca T hAXT u (harm.of_le (hTR.trans (half_le_self hR0.le)))
  obtain ⟨HA_H, -, -⟩ := hca (R / 2) (hAXT.trans hTR) u (harm.of_le (half_le_self hR0.le))
  obtain ⟨-, CC, -⟩ := hca R ((hAXT.trans hTR).trans (half_le_self hR0.le)) u harm
  obtain ⟨D0R, hD0R⟩ : ∃ x : ℝ,
      x = ⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) :=
    ⟨_, rfl⟩
  obtain ⟨D2R, hD2R⟩ : ∃ x : ℝ, x = ⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
      clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w) := ⟨_, rfl⟩
  have hD0R0 : 0 ≤ D0R := by
    rw [hD0R]; exact iInf_nonneg_of_nonneg fun _ => Real.sqrt_nonneg _
  have hD2R0 : 0 ≤ D2R := by
    rw [hD2R]; exact iInf_nonneg_of_nonneg fun _ => Real.sqrt_nonneg _
  -- the harmonic approximation error at `4T` and the top-scale bounds
  have hB := harmonicApproximation_error_leD hP h u hA hK hR4 hS'0 hS'
    (by rw [← hT]; exact hX4T) hsize HA_H
  rw [← hD0R, ← hT] at hB
  obtain ⟨G, hG⟩ : ∃ x : ℝ, x = D0R / R := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; exact div_nonneg hD0R0 hR0.le
  have hD0RG : D0R = R * G := by rw [hG, mul_div_assoc', eq_div_iff hR0.ne']; ring
  rw [← hG] at hB
  have hcrude : 2 * Real.sqrt ((4 * Real.sqrt d * S') ^ d) * G ≤ 2 * (cS * R ^ (α / 2)) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS'c (by norm_num)) hG0
  have hBB' := coarse_error_le_auxD (T := T) (R := R) (G := G) (c := cS)
    (Kq := Real.sqrt (2 ^ d) * K) hT1 h4TR hα0 hα1 hcS (by positivity) hG0
  have hrp : 0 ≤ (4 * T) ^ (1 - α) := Real.rpow_nonneg (by positivity) _
  obtain ⟨B', hB'⟩ : ∃ x : ℝ, x = Q * R ^ (1 - α / 2) * G := ⟨_, rfl⟩
  have hBle : ballDist (componentBallSeminorm (latticeComponent d) 0)
      (latticeHarmonicClass 0 (4 * (R / (8 * A)))) (4 * (R / (8 * A)))
      (fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) ≤ B' := by
    rw [← hT, hB', hQ]
    refine hB.trans ((mul_le_mul_of_nonneg_left
      (c := 2 * (cS * R ^ (α / 2)) * G + Real.sqrt (2 ^ d) * K * G / T) ?_ hrp).trans hBB')
    linarith
  obtain ⟨hD2T, hD0T⟩ := htop ω hP h ℓ R S' B' u hRtop hRq hS'0 hS' hsize hm₁ hm₂ hcube hBle
  rw [← hD0R, ← hD2R, ← hT] at hD2T
  rw [← hD0R, ← hT] at hD0T
  rw [← hG] at hD2T
  -- the error term at `T`
  obtain ⟨ET, hET⟩ : ∃ x : ℝ, x = K / T * ⨅ a : ℝ,
      clusterBallVolumeL2 (uniqueInfiniteComponent h) T (u - fun _ => a) := ⟨_, rfl⟩
  rw [← hET] at HA_T
  have hET0 : 0 ≤ ET := by
    rw [hET]
    exact mul_nonneg (div_nonneg hK hT0.le)
      (iInf_nonneg_of_nonneg fun _ => Real.sqrt_nonneg _)
  have hETG : ET ≤ cE * G := by
    have h1 := iInf_clusterBallVolumeL2_le_of_leD (ι := ℝ) (uniqueInfiniteComponent h) hT0
      (hTR.trans (half_le_self hR0.le)) u fun a => fun _ => a
    rw [zero_add, ← hD0R, hRT] at h1
    rw [hET]
    have e : K / T * (Real.sqrt ((8 * A) ^ d) * D0R) = cE * G := by
      rw [hD0RG, hcE, hT]; field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left h1 (div_nonneg hK hT0.le)
  -- the top-scale oscillation
  have hB'R : B' ≤ Q * R * G := by
    have : R ^ (1 - α / 2) ≤ R := by
      calc R ^ (1 - α / 2) ≤ R ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hR1 (sub_le_self _ (half_pos hα0).le)
        _ = R := Real.rpow_one R
    rw [hB']
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hQ0) hG0
  have hD0TT := top_zero_auxD hA0 hR0 hT hG hCt0 hC₃ hD0T hB'R
  -- Lemma 7.2 at `k = 0` below the top scale
  have hHA_T' := HA_T.mono_scale hXX'
  have hXs : max (latticeHRScale d) (24 * Real.sqrt d) ≤ X' := hXlat3.trans hXlatX'
  have hk0 : ∀ ρ : ℝ, max X' C₀ ≤ ρ → ρ ≤ T / 2 →
      ballExcess (componentBallSeminorm (latticeComponent d) 0)
        (clusterConstants (latticeComponent d)) ρ
        (fun x : latticeComponent d => partitionCoarse (uniqueInfiniteComponent h) u x.val) ≤
        C₄ * ρ * G := fun ρ hρ hρT =>
    zero_step_auxD hC₄ (hX'1.trans ((le_max_left _ _).trans hρ)) hα0 hT0 hC₀.le hcE0 hG0
      (ballExcess_nonneg _ _ _ _) hET0 hD0TT hETG
      (h72₀ 0 T X' ET _ hX'1 hXs hX'T hET0 hHA_T' ρ hρ hρT)
  -- the Lipschitz bound of order zero
  obtain ⟨s₁, hs₁⟩ : ∃ x : ℝ, x = max (max X' C₀) (max ρ₁ 3) := ⟨_, rfl⟩
  have hs₁ρ : ρ₁ ≤ s₁ := by rw [hs₁]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hs₁3 : 3 ≤ s₁ := by rw [hs₁]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hs₁X : max X' C₀ ≤ s₁ := by rw [hs₁]; exact le_max_left _ _
  have hs₁KA : 2 * K * A < s₁ := by rw [hρ₁] at hs₁ρ; linarith
  have hs₁0 : 0 < s₁ := by linarith
  have hlip : ∀ s, s₁ ≤ s → s ≤ R / 2 →
      (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) s (u - fun _ => a)) ≤
        C₅ * s * G := by
    rw [hC₅]
    refine le_of_scale_inductionD (f := fun s => ⨅ a : ℝ,
      clusterBallVolumeL2 (uniqueInfiniteComponent h) s (u - fun _ => a)) hA hK hG0 hB₀0
      hs₁KA hs₁0 hAThalf ?_ ?_
    · intro s hsT hsR
      have hs0 : 0 < s := by linarith
      have h1 := iInf_clusterBallVolumeL2_le_of_leD (ι := ℝ) (uniqueInfiniteComponent h) hs0
        (hsR.trans (half_le_self hR0.le)) u fun a => fun _ => a
      rw [← hD0R] at h1
      rw [hB₀]
      exact base_auxD hs0 hR0.le hG0 (lt_mul_of_half_div_lt hA (by rw [← hT]; exact hsT)).le
        hD0RG h1
    · intro s hs hsT
      have h1 := clusterExcess_zero_leD h u (by linarith : (1 : ℝ) ≤ s)
      have h2 := CC s (hXX'.trans ((le_max_left _ _).trans (hs₁X.trans hs))) (hsT.trans hThalf)
      have h3 := hk0 s (hs₁X.trans hs) hsT
      rw [← hc₃] at h1
      have h4 := add_le_add h2 (mul_le_mul_of_nonneg_left h3 hc₃0)
      have e : c₃ * (C₄ * s * G) = c₃ * C₄ * s * G := by ring
      rw [e] at h4
      exact h1.trans h4
  -- the conclusion
  have hGu : G ≤ clusterBallVolumeL2 (uniqueInfiniteComponent h) R u / R := by
    have h1 : (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a)) ≤
        clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => (0 : ℝ)) :=
      iInf_le_of_le (fun _ => Real.sqrt_nonneg _) 0
    have e : (u - fun _ => (0 : ℝ)) = u := by funext x; simp
    rw [e, ← hD0R] at h1
    rw [hG]
    exact div_le_div_of_nonneg_right h1 hR0.le
  have hu0 : 0 ≤ clusterBallVolumeL2 (uniqueInfiniteComponent h) R u := Real.sqrt_nonneg _
  rw [← hD2R]
  by_cases hrT : r ≤ T / 2
  · -- below the top scale
    have h1 := clusterExcess_two_leD h u hr1
    rw [← hc₃] at h1
    have hXr : X ≤ r := le_trans (le_mul_of_one_le_left hX0 hr₀1) hr
    have h2 := CC r hXr (hrT.trans hThalf)
    have hX'r : X' ≤ r := hX'X.trans ((mul_le_mul_of_nonneg_right hXlatr₀ hX0).trans hr)
    have hs₁r : s₁ ≤ r := by
      rw [hs₁]
      exact max_le (max_le hX'r (hr₀d.trans hr₀r)) (max_le (hr₀e.trans hr₀r) (hr₀f.trans hr₀r))
    have hAr1 : s₁ ≤ A * r := hs₁r.trans (le_mul_of_one_le_left hr0.le (one_le_two.trans hA))
    have hArR : A * r ≤ R / 2 := (mul_le_mul_of_nonneg_left hrT hA0.le).trans hAThalf
    have h3 := hlip (A * r) hAr1 hArR
    have hcc : clusterBallVolumeL2 (uniqueInfiniteComponent h) r
        (u - fun x => partitionCoarse (uniqueInfiniteComponent h) u x.val) ≤ K * A * C₅ * G := by
      refine h2.trans ?_
      have e : K / r * (C₅ * (A * r) * G) = K * A * C₅ * G := by field_simp
      rw [← e]
      exact mul_le_mul_of_nonneg_left h3 (div_nonneg hK hr0.le)
    have hrX'C : max X' C₂ ≤ r := max_le hX'r (hr₀c.trans hr₀r)
    have h4 := h72₂ 0 T X' ET _ (hXlat2.trans hXlatX') hX'T hET0 hHA_T' r hrX'C hrT
    exact below_top_auxD hr1 hrRle hA0 hT hα0 hα1 hK hQ0 hcE0 hc₃0 hCt0 hCa hCb hC₂.le hC₅0 hG0
      hD2R0 (ballExcess_nonneg _ _ _ _) hET0 hB' hGu hC6 hC7 h1 hcc h4 hD2T hD0TT hETG
  · -- near the top scale
    push Not at hrT
    have h1 := iInf_clusterBallVolumeL2_le_of_leD
      (ι := clusterHarmonicQuadratic (uniqueInfiniteComponent h)) (uniqueInfiniteComponent h) hr0
      hrRle u fun w => (w : uniqueInfiniteComponent h → ℝ)
    rw [← hD2R] at h1
    exact near_top_auxD hA hr0 hR0 hT hrT hD2R0 hu0 hC16 h1

end Rigidity.Proofs.Regularity
