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

end Rigidity.Proofs.Regularity
