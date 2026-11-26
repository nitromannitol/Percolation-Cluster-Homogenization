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

/-- Every slope has a corrected plane on the infinite cluster of `ℤᵈ` (Armstrong–Dario, Theorem 2
(ii) for `k = 1`, with the sublinearity in the uniform norm of Remark 1.1 and (1.22)). -/
def CorrectedPlaneExistence (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin d → ℝ,
      ∃ u : uniqueInfiniteComponent h → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u

/-- **The uniform bound of the corrector at the scale `E = 3^m`** above the minimal scales: from
(1.18) on `B_{15 d E}`, the Lipschitz estimate at the vertices of `□_{m+3}` with minimal scales at most
`3^{(m+1)γ}`, the partition cubes of `□_{m+3}` of sides at most `3^{d(m+3)/(d + d/γ)}` and the density
of the cluster, `|χ(x)| ≤ c |q|₁ E^{1-η}` on `{|x_i| ≤ E}`. -/
theorem abs_corrector_le_of_scales [NeZero d] (hd : 2 ≤ d) {ω : Configuration d}
    (hP : PartitionEvent ω) (C : OpenComponent ω) (hinf : C.supp.Infinite) (q : Fin d → ℝ)
    (u : C → ℝ) (hu : u ∈ harmonicGrowthSpace C 1) {δ δ₁ K C₀ κ η γ X₁ M₄ : ℝ}
    (hK : 0 ≤ K) (hC₀ : 0 < C₀) (hκ : 0 < κ) (hδδ : δ ≤ δ₁)
    (h2η : 2 * η * d = δ) (h3η : 3 * η ≤ δ) (hη4 : η ≤ 1 / 4) (hγ0 : 0 < γ)
    (hγη : γ * (2 * d + 1) = η) (hγle : γ ≤ η) (hdt : (d : ℝ) / (d + d / γ) ≤ γ)
    (hL2 : ∀ r : ℝ, X₁ ≤ r →
      componentBallL2 C 0 r (fun x => u x - componentSlope C q x) ≤ K * (∑ i, |q i|) * r ^ (1 - δ₁))
    {Y : Vertex d → ℝ}
    (hLip : ∀ z : Vertex d, ∀ R : ℝ, 2 * Y z ≤ R → ∀ v : C → ℝ,
      (∀ x ∈ componentEuclideanBall C z R,
        (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C z R) →
          componentLaplacian C v x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, Y z ≤ r → r ≤ R / 2 →
        componentBallL2 C z r (v - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C z R v)
    {m : ℕ} (hmd : d + 1 ≤ m)
    (hYbox : ∀ z ∈ triScaleBox d (m + 1), Y z ≤ (3 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * γ))
    (hmin : ∀ y ∈ (⟨m + 3, 0⟩ : TriadicCube d).vertices,
      (3 : ℝ) ^ (partitionCube ω y).scale ≤ (3 : ℝ) ^ ((d : ℝ) * ((m + 3 : ℕ) : ℝ) / (d + d / γ)))
    (hcube : ClusterCubeDensity C 0 ((d : ℝ) * (14 * 3 ^ (d + 1) + 1) + 1) M₄ κ)
    (hM₄ : 3 ^ (d + 1) * M₄ ≤ 3 ^ m) (hX₁ : X₁ ≤ 3 ^ m) (hE100 : 100 ≤ (3 : ℝ) ^ m)
    (x : C) (hx : ∀ i, |((x.val i : ℤ) : ℝ)| ≤ 3 ^ m) :
    |u x - componentSlope C q x| ≤
      (2 * d * 21 ^ d * (10 * 13 ^ d * C₀ *
          (15 * d * Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * K + 1) + 1) +
        Real.sqrt (2 * 21 ^ d * (33 * d) ^ d * (15 * d * K) ^ 2) +
        Real.sqrt 2 * d * (2 * d * 21 ^ d * (10 * 13 ^ d * C₀ *
          (15 * d * Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) * K + 1) + 1))) *
        (∑ i, |q i|) * ((3 : ℝ) ^ m) ^ (1 - η) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set Q : ℝ := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set E : ℝ := 3 ^ m with hEdef
  have hE1 : 1 ≤ E := by linarith
  have hE0 : 0 < E := by linarith
  set Y₀ : ℝ := E ^ γ with hY₀def
  have hY1 : 1 ≤ Y₀ := Real.one_le_rpow hE1 hγ0.le
  have hYE : Y₀ ^ (2 * d + 1) = E ^ η := by
    rw [hY₀def, ← Real.rpow_natCast, ← Real.rpow_mul hE0.le]
    congr 1
    push_cast
    linarith
  have hY10 : 10 * Y₀ ≤ E := by
    have h1 : Y₀ ≤ E ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE1 (by linarith)
    have h2 : (10 : ℝ) ≤ E ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    have h3 : E ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) = E := by
      rw [← Real.rpow_add hE0]; norm_num
    calc 10 * Y₀ ≤ E ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := mul_le_mul h2 h1 (by positivity)
          (by positivity)
      _ = E := h3
  have hpowγ : ∀ j : ℕ, j ≤ 3 → (3 : ℝ) ^ (((m + j : ℕ) : ℝ) * γ) ≤ 3 * Y₀ := by
    intro j hj
    have e : (3 : ℝ) ^ (((m + j : ℕ) : ℝ) * γ) =
        (3 : ℝ) ^ ((m : ℝ) * γ) * (3 : ℝ) ^ ((j : ℝ) * γ) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
    have e2 : (3 : ℝ) ^ ((m : ℝ) * γ) = Y₀ := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have h3 : (3 : ℝ) ^ ((j : ℝ) * γ) ≤ 3 := by
      have hj' : (j : ℝ) ≤ 3 := by exact_mod_cast hj
      calc (3 : ℝ) ^ ((j : ℝ) * γ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              ((mul_le_mul_of_nonneg_right hj' hγ0.le).trans (by linarith))
        _ = 3 := Real.rpow_one 3
    calc (3 : ℝ) ^ (((m + j : ℕ) : ℝ) * γ) = Y₀ * (3 : ℝ) ^ ((j : ℝ) * γ) := by rw [e, e2]
      _ ≤ Y₀ * 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 * Y₀ := by ring
  have hsc : ∀ y ∈ (⟨m + 3, 0⟩ : TriadicCube d).vertices,
      (3 : ℝ) ^ (partitionCube ω y).scale ≤ 3 * Y₀ := by
    intro y hy
    have h1 := hmin y hy
    refine h1.trans ((Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_).trans (hpowγ 3 le_rfl))
    rw [mul_div_right_comm, mul_comm (((m + 3 : ℕ) : ℝ)) γ]
    exact mul_le_mul_of_nonneg_right hdt (by positivity)
  have hscm : ∀ y ∈ triadicCubeFinset d (m + 3) 0, (partitionCube ω y).scale ≤ m := by
    intro y hy
    have h1 := hsc y (mem_cubeFinset_iff_vertices.1 hy)
    have h2 : (3 : ℝ) ^ (partitionCube ω y).scale ≤ 3 ^ m := h1.trans (by linarith)
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h2
  have hYz : ∀ z ∈ (⟨m + 3, 0⟩ : TriadicCube d).vertices, Y z ≤ 3 * Y₀ := by
    intro z hz
    have hzbox : z ∈ triScaleBox d (m + 1) := mem_triScaleBox.2 fun i => by
      have h1 := (mem_triadicCube_zero_iff'.1 hz) i
      have e : (3 : ℤ) ^ (m + 1 + 2) = 3 ^ (m + 3) := by ring_nf
      rw [e]
      have := abs_nonneg (z i)
      linarith
    exact (hYbox z hzbox).trans (hpowγ 1 (by norm_num))
  have hℓ : M₄ ≤ 3 ^ (m - (d + 1)) := by
    have e : (3 : ℝ) ^ m = 3 ^ (d + 1) * 3 ^ (m - (d + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [hEdef, e] at hM₄
    exact le_of_mul_le_mul_left hM₄ (by positivity)
  -- the bound (1.18) on the ball `B_{15 d E}`
  set b := componentBallL2 C 0 (15 * d * E)
    (componentCorrector C q u) with hbdef
  have hb0 : 0 ≤ b := componentBallL2_nonneg _ _ _ _
  have h15 : (1 : ℝ) ≤ 15 * d := by linarith
  have hbδ : b ≤ K * Q * (15 * d) * E ^ (1 - δ) := by
    have h1 : b ≤ K * Q * (15 * d * E) ^ (1 - δ₁) :=
      hL2 (15 * d * E) (hX₁.trans (le_mul_of_one_le_left hE0.le h15))
    have h2 : (15 * d * E) ^ (1 - δ₁) ≤ (15 * d * E) ^ (1 - δ) :=
      Real.rpow_le_rpow_of_exponent_le (h15.trans (le_mul_of_one_le_right (by linarith) hE1))
        (by linarith)
    have h3 : (15 * d * E) ^ (1 - δ) ≤ 15 * d * E ^ (1 - δ) := by
      rw [Real.mul_rpow (by positivity) hE0.le]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (15 * (d : ℝ)) ^ (1 - δ) ≤ (15 * d) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h15 (by linarith)
        _ = 15 * d := Real.rpow_one _
    calc b ≤ K * Q * (15 * d * E) ^ (1 - δ₁) := h1
      _ ≤ K * Q * (15 * d * E ^ (1 - δ)) := by
          gcongr
          exact h2.trans h3
      _ = K * Q * (15 * d) * E ^ (1 - δ) := by ring
  have hbE : b ≤ K * Q * (15 * d) * E := by
    refine hbδ.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc E ^ (1 - δ) ≤ E ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE1 (by linarith)
      _ = E := Real.rpow_one E
  -- the side of the box
  set t : ℕ := ⌊E ^ (1 - 2 * η)⌋₊ with htdef
  have ht : (t : ℝ) ≤ E ^ (1 - 2 * η) := Nat.floor_le (by positivity)
  have ht1 : E ^ (1 - 2 * η) ≤ (t : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have htE : (t : ℝ) ≤ 3 ^ m := by
    refine ht.trans ?_
    calc E ^ (1 - 2 * η) ≤ E ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE1 (by linarith)
      _ = E := Real.rpow_one E
  have hbound := abs_corrector_le_at_scale hP C hinf q u hu.1 hmd
    (Y₀ := Y₀) (C₀ := C₀) (κ := κ) (ℓ := M₄) (b := b) (Yz := Y) hY1 hY10
    hC₀.le hκ hsc hscm (fun z => hLip z.val) hYz hcube hℓ le_rfl t htE x hx
  have harith := corrector_scale_arith hd (E := E) (Y := Y₀) (Q := Q) (K := K) (C₀ := C₀)
    (κ := κ) (δ := δ) (η := η) (b := b) (t := t) hE1 hY1 hYE hQ0 hK hC₀.le h2η h3η hη4 ht ht1
    hb0 hbE hbδ
  exact hbound.trans harith

/-- **Every slope has a corrected plane on the infinite cluster of `ℤᵈ`**, `d ≥ 2`, from (1.18)
with an almost surely finite scale, by the Remark after (1.19) of Armstrong and Dario. -/
theorem correctedPlaneExistence_of_sublinearL2Ae [NeZero d] (hd : 2 ≤ d)
    (h118 : CorrectorSublinearL2Ae d) : CorrectedPlaneExistence d := by
  intro p hpc hp1
  obtain ⟨δ₁, K, hδ₁, hK, hae₁⟩ := h118 p hpc hp1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₁ 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδ₁ one_pos
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
  have hδδ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = δ / (2 * d) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η * d = δ := by rw [hηdef]; field_simp
  have h3η : 3 * η ≤ δ := by nlinarith
  have hη4 : η ≤ 1 / 4 := by nlinarith
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = η / (2 * d + 1) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  have hγη : γ * (2 * d + 1) = η := by rw [hγdef]; field_simp
  have hγle : γ ≤ η := by rw [hγdef]; exact div_le_self hη0.le (by linarith)
  have ht₀ : (1 : ℝ) ≤ d / γ := by rw [le_div_iff₀ hγ0]; linarith
  have hdt : (d : ℝ) / (d + d / γ) ≤ γ := by
    have e : γ * ((d : ℝ) / γ) = d := mul_div_cancel₀ _ hγ0.ne'
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨s₃, θ₃, C₀, hs₃, hθ₃, hC₀, Y, -, -, hYi, hYb, hae₃⟩ :=
    exists_all_centres_constant_approximation hd p hpc hp1
  have hBC := ae_eventually_scale_le_three hs₃ hθ₃ hγ0 hYi hYb
  obtain ⟨s₅, C₅, -, -, M₅, -, -, -, hM₅ae⟩ := Rigidity.Dirichlet.cubeMinimalScales_holds hd hpc ((d : ℝ) / γ) ht₀
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₄, θ₄, -, -, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) ((d : ℝ) * (14 * 3 ^ (d + 1) + 1) + 1)
  obtain ⟨M₄, -, -, -, hM₄ae⟩ := hcube 0
  set κ : ℝ := theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  filter_upwards [hae₁, hae₃, hBC, hM₅ae, hM₄ae, ae_partitionEvent hd hpc] with
    ω hω₁ hω₃ hωBC hω₅ hω₄ hP
  intro h q
  obtain ⟨u, hu, X₁, hL2⟩ := hω₁ h q
  refine ⟨u, hu, ?_⟩
  obtain ⟨-, hω₃'⟩ := hω₃
  have hLip := hω₃' h
  have hinf := uniqueInfiniteComponent_infinite h
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hωBC
  obtain ⟨ma, hma⟩ := eventually_le_three_pow
    (max (max X₁ (M₅ ω)) (max (3 ^ (d + 1) * M₄ ω) 100))
  set Q : ℝ := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set cr := Real.sqrt ((33 * d) ^ d * 3 ^ (d * (d + 1)) / κ) with hcr
  set c : ℝ := 2 * d * 21 ^ d * (10 * 13 ^ d * C₀ * (15 * d * cr * K + 1) + 1) +
    Real.sqrt (2 * 21 ^ d * (33 * d) ^ d * (15 * d * K) ^ 2) +
    Real.sqrt 2 * d * (2 * d * 21 ^ d * (10 * 13 ^ d * C₀ * (15 * d * cr * K + 1) + 1)) with hc
  have hc0 : 0 ≤ c := by positivity
  refine componentSlopeAsymptotics_of_scale_bound (uniqueInfiniteComponent h) q u
    (c := c * Q) hη0 (by positivity) (m₀ := max ma (max k₀ (d + 1))) fun m hm x hx => ?_
  have hma' : ma ≤ m := (le_max_left _ _).trans hm
  have hk₀' : k₀ ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmd : d + 1 ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hEm := hma m hma'
  exact abs_corrector_le_of_scales hd hP (uniqueInfiniteComponent h) hinf q u hu hK hC₀ hκ hδδ
    h2η h3η hη4 hγ0 hγη hγle hdt hL2 (Y := fun z => Y z ω) (fun z => hLip z) hmd
    (fun z hz => hk₀ (m + 1) (by omega) z hz) ((hω₅ (m + 3) (((le_max_right _ _).trans
      (le_max_left _ _)).trans hEm |>.trans (pow_le_pow_right₀ (by norm_num) (by omega)))).2)
    (hω₄ h) (((le_max_left _ _).trans (le_max_right _ _)).trans hEm)
    (((le_max_left _ _).trans (le_max_left _ _)).trans hEm)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hEm) x hx

end Rigidity.Proofs.Regularity.GeneralDim
