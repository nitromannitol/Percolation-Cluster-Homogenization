import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorBasic
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityConcentration
import PercolationClusterHomogenization.Proofs.Density.ScaleInputsFaithful

/-!
# (1.18) on the infinite cluster of `ℤᵈ` from the approximation of affine functions

`CubeAffineApproximationAe d` is the input of Step 3 of the proof of Proposition 3.1 of Armstrong,
Kuusi and Mourrat (arXiv:1602.00512v1), for `k = 1`, on the infinite cluster of `ℤᵈ`: almost
surely, for every slope `q` and every large `m`, a function harmonic on `𝒞_∞ ∩ B_{3^m}` within
`K |q|₁ 3^{m(1-δ)}` of `q · x` in `L̲²(𝒞_∞ ∩ B_{3^m})`. Armstrong and Dario (arXiv:1609.09431v2,
proof of Theorem 2) obtain it from their Theorem 1.

`correctorSublinearL2Ae_of_affineApproximationAe` proves (1.18) with an almost surely finite scale
(`CorrectorSublinearL2Ae d`) from it, the order-zero regularity of Theorem 2 (iii)
(`exists_origin_constant_approximation`) and the density of the cluster, by the construction of
Step 3 (`exists_harmonic_of_approximations`).
-/

namespace Rigidity.Proofs.Regularity.GeneralDim

open Finset Filter Topology MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- The approximation of affine functions by harmonic functions on growing balls of the infinite
cluster of `ℤᵈ`, above an almost surely finite scale. -/
def CubeAffineApproximationAe (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin d → ℝ,
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ v : uniqueInfiniteComponent h → ℝ,
          HarmonicOnBall (uniqueInfiniteComponent h) v (3 ^ m) ∧
          componentBallL2 (uniqueInfiniteComponent h) 0 (3 ^ m)
              (fun x => v x - componentSlope (uniqueInfiniteComponent h) q x) ≤
            K * (∑ i, |q i|) * ((3 : ℝ) ^ m) ^ (1 - δ)

/-- **Armstrong–Dario, (1.18), in dimension `d`, with an almost surely finite scale** (Theorem 2
(ii) for `k = 1`): every slope has an element of `𝒜_1` whose corrector is sublinear in `L̲²` with
a rate. -/
def CorrectorSublinearL2Ae (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin d → ℝ,
        ∃ u : uniqueInfiniteComponent h → ℝ,
          u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 ∧ ∃ X : ℝ, ∀ r : ℝ, X ≤ r →
            componentBallL2 (uniqueInfiniteComponent h) 0 r
                (fun x => u x - componentSlope (uniqueInfiniteComponent h) q x) ≤
              K * (∑ i, |q i|) * r ^ (1 - δ)

theorem three_pow_rpow_eq {m : ℕ} (δ : ℝ) :
    ((3 : ℝ) ^ m) ^ (1 - δ) = 3 ^ m * ((3 : ℝ) ^ (-δ)) ^ m := by
  rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by norm_num), inv_pow]
  have e : ((3 : ℝ) ^ m) ^ δ = ((3 : ℝ) ^ δ) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [e, div_eq_mul_inv]

/-- **The corrector of one slope with the bound (1.18)** on one configuration, from the
approximations on growing balls, the Lipschitz estimate at the origin and the comparability of the
cluster in consecutive triadic balls. -/
theorem exists_corrector_of_scales {ω : Configuration d} (C : OpenComponent ω) (q : Fin d → ℝ)
    {m₀ : ℕ} {K δ X₀ C₀ ρ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hρ : 1 ≤ ρ)
    (hC₀ : 0 ≤ C₀) (hX₀ : X₀ ≤ 3 ^ m₀)
    (hv : ∀ m, m₀ ≤ m → ∃ v : C → ℝ, HarmonicOnBall C v (3 ^ m) ∧
      componentBallL2 C 0 (3 ^ m) (fun x => v x - componentSlope C q x) ≤
        K * (∑ i, |q i|) * ((3 : ℝ) ^ m) ^ (1 - δ))
    (hLip : ∀ R : ℝ, 2 * X₀ ≤ R → ∀ w : C → ℝ, HarmonicOnBall C w R →
      ∃ c : ℝ, ∀ r : ℝ, X₀ ≤ r → r ≤ R / 2 →
        componentBallL2 C 0 r (w - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C 0 R w)
    (hpos : ∀ m, m₀ ≤ m → 0 < (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card)
    (hratio : ∀ m, m₀ ≤ m → ((componentEuclideanBall C 0 ((3 : ℝ) ^ (m + 1))).card : ℝ) ≤
      ρ ^ 2 * (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card) :
    ∃ u : C → ℝ, u ∈ harmonicGrowthSpace C 1 ∧ ∀ r : ℝ, 3 ^ (m₀ + 1) ≤ r →
      componentBallL2 C 0 r (fun x => u x - componentSlope C q x) ≤
        3 * ρ * (K * (1 + (1 + ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) +
          C₀ * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (1 - (3 : ℝ) ^ (-δ)) +
          (ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (3 * (3 : ℝ) ^ (-δ) - 1))) *
          (∑ i, |q i|) * r ^ (1 - δ) := by
  set ε : ℝ := (3 : ℝ) ^ (-δ) with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h3ε : 1 < 3 * ε := by
    have e : 3 * ε = (3 : ℝ) ^ (1 - δ) := by
      rw [hεdef, Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num),
        div_eq_mul_inv]
    rw [e]; exact Real.one_lt_rpow (by norm_num) (by linarith)
  set Q := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hv' : ∀ m, m₀ ≤ m → ∃ v : C → ℝ, HarmonicOnBall C v (3 ^ m) ∧
      componentBallL2 C 0 (3 ^ m) (fun x => v x - componentSlope C q x) ≤
        K * Q * 3 ^ m * ε ^ m := by
    intro m hm
    obtain ⟨v, hvh, hvb⟩ := hv m hm
    refine ⟨v, hvh, hvb.trans (le_of_eq ?_)⟩
    rw [three_pow_rpow_eq, hεdef]; ring
  obtain ⟨u, hharm, hb⟩ := exists_harmonic_of_approximations C (componentSlope C q)
    (A := K * Q) (by positivity) hε hε1 h3ε (by linarith) hC₀ hX₀ hv' hLip hpos hratio
  set Γ : ℝ := 1 + (1 + ρ + C₀) * (3 * ρ * ε + 1) + C₀ * (3 * ρ * ε + 1) / (1 - ε) +
    (ρ + C₀) * (3 * ρ * ε + 1) / (3 * ε - 1) with hΓ
  have hΓ0 : 0 ≤ Γ := by
    have : 0 < 1 - ε := by linarith
    have : 0 < 3 * ε - 1 := by linarith
    positivity
  have hA' : K * Q + (1 + ρ + C₀) * (K * Q) * (3 * ρ * ε + 1) +
      C₀ * (K * Q) * (3 * ρ * ε + 1) / (1 - ε) +
      (ρ + C₀) * (K * Q) * (3 * ρ * ε + 1) / (3 * ε - 1) = K * Γ * Q := by
    rw [hΓ]; ring
  -- the bound on every radius
  have hbound : ∀ r : ℝ, 3 ^ (m₀ + 1) ≤ r →
      componentBallL2 C 0 r (fun x => u x - componentSlope C q x) ≤
        3 * ρ * (K * Γ) * Q * r ^ (1 - δ) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
    set n : ℕ := ⌊r⌋₊ with hn
    have h3n : 3 ^ (m₀ + 1) ≤ n := by
      rw [hn]; apply Nat.le_floor; push_cast; exact hr
    set j : ℕ := Nat.log 3 n + 1 with hj
    have hlow : 3 ^ (j - 1) ≤ n := by
      have h1 : 1 ≤ 3 ^ (m₀ + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [hj, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 3 (by omega)
    have hhigh : n < 3 ^ j := by rw [hj]; exact Nat.lt_pow_succ_log_self (by norm_num) n
    have hjm : m₀ + 2 ≤ j := by
      have := Nat.le_log_of_pow_le (by norm_num) h3n
      omega
    have hrj : r ≤ 3 ^ j := by
      have h1 : r < n + 1 := Nat.lt_floor_add_one r
      have h2 : ((n + 1 : ℕ) : ℝ) ≤ 3 ^ j := by exact_mod_cast hhigh
      push_cast at h2; linarith
    have hjr : (3 : ℝ) ^ (j - 1) ≤ r := by
      have h1 : ((3 ^ (j - 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast hlow
      have h2 : (n : ℝ) ≤ r := Nat.floor_le hr0.le
      push_cast at h1; linarith
    have hsub : componentEuclideanBall C 0 ((3 : ℝ) ^ (j - 1)) ⊆ componentEuclideanBall C 0 r := by
      intro x hx; rw [mem_componentEuclideanBall] at hx ⊢; linarith
    have hposr : 0 < (componentEuclideanBall C 0 r).card :=
      lt_of_lt_of_le (hpos (j - 1) (by omega)) (Finset.card_le_card hsub)
    have h1 := componentBallL2_le_sqrt_card_div_mul C 0 hrj hposr
      (fun x => u x - componentSlope C q x)
    have hratio' : ((componentEuclideanBall C 0 ((3 : ℝ) ^ j)).card : ℝ) /
        (componentEuclideanBall C 0 r).card ≤ ρ ^ 2 := by
      have hn : (0 : ℝ) < (componentEuclideanBall C 0 r).card := by exact_mod_cast hposr
      rw [div_le_iff₀ hn]
      have hr1 := hratio (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at hr1
      have hc : ((componentEuclideanBall C 0 ((3 : ℝ) ^ (j - 1))).card : ℝ) ≤
          (componentEuclideanBall C 0 r).card := by exact_mod_cast Finset.card_le_card hsub
      nlinarith
    have h2 := hb j (by omega)
    rw [hA'] at h2
    have h3 : (3 : ℝ) ^ j * ε ^ j ≤ 3 * r ^ (1 - δ) := by
      have e : (3 : ℝ) ^ j * ε ^ j = ((3 : ℝ) ^ j) ^ (1 - δ) := by rw [three_pow_rpow_eq, hεdef]
      rw [e]
      have h3j : (3 : ℝ) ^ j ≤ 3 * r := by
        have : (3 : ℝ) ^ j = 3 * 3 ^ (j - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ j)]
        rw [this]; linarith
      calc ((3 : ℝ) ^ j) ^ (1 - δ) ≤ (3 * r) ^ (1 - δ) :=
            Real.rpow_le_rpow (by positivity) h3j (by linarith)
        _ = (3 : ℝ) ^ (1 - δ) * r ^ (1 - δ) := Real.mul_rpow (by norm_num) hr0.le
        _ ≤ 3 * r ^ (1 - δ) := by
            have : (3 : ℝ) ^ (1 - δ) ≤ 3 := by
              calc (3 : ℝ) ^ (1 - δ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 3 := Real.rpow_one 3
            exact mul_le_mul_of_nonneg_right this (by positivity)
    calc componentBallL2 C 0 r (fun x => u x - componentSlope C q x)
        ≤ Real.sqrt (((componentEuclideanBall C 0 ((3 : ℝ) ^ j)).card : ℝ) /
            (componentEuclideanBall C 0 r).card) *
            componentBallL2 C 0 ((3 : ℝ) ^ j) (fun x => u x - componentSlope C q x) := h1
      _ ≤ ρ * (K * Γ * Q * 3 ^ j * ε ^ j) := by
          apply mul_le_mul _ h2 (componentBallL2_nonneg _ _ _ _) (by linarith)
          rw [Real.sqrt_le_left (by linarith)]; exact hratio'
      _ = ρ * (K * Γ) * Q * (3 ^ j * ε ^ j) := by ring
      _ ≤ ρ * (K * Γ) * Q * (3 * r ^ (1 - δ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 * ρ * (K * Γ) * Q * r ^ (1 - δ) := by ring
  refine ⟨u, ⟨hharm, ?_⟩, fun r hr => (hbound r hr).trans (le_of_eq (by rw [hΓ, hεdef]))⟩
  -- the linear growth
  set B : ℝ := 3 * ρ * (K * Γ) * Q + Q with hBdef
  have hev : ∀ᶠ R : ℝ in atTop, (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u ≤ B / R := by
    refine Filter.eventually_atTop.2 ⟨max (3 ^ (m₀ + 1)) 1, fun R hR => ?_⟩
    have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
    have hR3 : 3 ^ (m₀ + 1) ≤ R := (le_max_left _ _).trans hR
    have hR0 : 0 < R := by linarith
    have hu : componentBallL2 C 0 R u ≤ B * R := by
      have e : u = fun x => (u x - componentSlope C q x) + componentSlope C q x := by
        funext x; ring
      rw [e]
      refine (Rigidity.Proofs.S2.componentBallL2_add_le C 0 R _ _).trans ?_
      have h1 := hbound R hR3
      have h2 : componentBallL2 C 0 R (componentSlope C q) ≤ Q * R :=
        componentBallL2_le_of_abs_le C 0 R (by positivity) fun x hx => abs_componentSlope_le C q hx
      have h3 : R ^ (1 - δ) ≤ R := by
        calc R ^ (1 - δ) ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
          _ = R := Real.rpow_one R
      have h4 : 3 * ρ * (K * Γ) * Q * R ^ (1 - δ) ≤ 3 * ρ * (K * Γ) * Q * R :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      calc _ ≤ 3 * ρ * (K * Γ) * Q * R ^ (1 - δ) + Q * R := add_le_add h1 h2
        _ ≤ 3 * ρ * (K * Γ) * Q * R + Q * R := by linarith
        _ = B * R := by rw [hBdef]; ring
    rw [show (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u = componentBallL2 C 0 R u / R ^ 2 by
      rw [div_eq_inv_mul]]
    rw [div_le_div_iff₀ (by positivity) hR0]
    nlinarith [componentBallL2_nonneg C 0 R u]
  have hev0 : ∀ᶠ R : ℝ in atTop, 0 ≤ (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u := by
    refine Filter.eventually_atTop.2 ⟨0, fun R hR => ?_⟩
    exact mul_nonneg (inv_nonneg.2 (by positivity)) (componentBallL2_nonneg _ _ _ _)
  have hlim : Tendsto (fun R : ℝ => B / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hev0 hev

theorem two_mul_le_three_pow_succ (d : ℕ) : 2 * d ≤ 3 ^ (d + 1) := by
  induction d with
  | zero => norm_num
  | succ n ih =>
      have h1 := Nat.one_le_pow (n + 1) 3 (by norm_num)
      rw [pow_succ]
      omega

/-- The ratio of the cluster in consecutive triadic balls, from the density of the cluster. -/
theorem card_ball_bounds [NeZero d] {ω : Configuration d} (C : OpenComponent ω) {Λ ℓ κ : ℝ}
    (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 Λ ℓ κ) (hΛ : (d : ℝ) < Λ) {m : ℕ}
    (hm : d + 1 ≤ m) (hℓ : ℓ ≤ 3 ^ (m - (d + 1))) :
    0 < (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card ∧
      ((componentEuclideanBall C 0 ((3 : ℝ) ^ (m + 1))).card : ℝ) ≤
        (Real.sqrt ((3 : ℝ) ^ (d * (d + 3)) / κ)) ^ 2 *
          (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card := by
  set k := m - (d + 1) with hk
  have hmk : m = k + (d + 1) := by omega
  have h := card_componentEuclideanBall_ge C hcube hℓ (x := (0 : Vertex d)) (a := 0)
    (fun i => by simp) (by simpa using hΛ)
  have h2d : (2 * d : ℝ) ≤ 3 ^ (d + 1) := by exact_mod_cast two_mul_le_three_pow_succ d
  have hsub : componentEuclideanBall C 0 (2 * d * 3 ^ k) ⊆
      componentEuclideanBall C 0 ((3 : ℝ) ^ m) := by
    intro x hx
    rw [mem_componentEuclideanBall] at hx ⊢
    have e : (3 : ℝ) ^ m = 3 ^ (d + 1) * 3 ^ k := by rw [hmk, pow_add, mul_comm]
    have : (2 * d : ℝ) * 3 ^ k ≤ 3 ^ (d + 1) * 3 ^ k :=
      mul_le_mul_of_nonneg_right h2d (by positivity)
    linarith
  have hlow : κ * 3 ^ (d * k) ≤ (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card :=
    h.trans (by exact_mod_cast Finset.card_le_card hsub)
  have hpos : (0 : ℝ) < κ * 3 ^ (d * k) := by positivity
  refine ⟨by exact_mod_cast lt_of_lt_of_le hpos hlow, ?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have hbig := card_componentEuclideanBall_le C (0 : Vertex d)
    (by positivity : (0 : ℝ) ≤ 3 ^ (m + 1))
  have hb : (2 * (3 : ℝ) ^ (m + 1) + 3) ^ d ≤ 3 ^ (d * (d + 3)) * 3 ^ (d * k) := by
    have h1 : (2 * (3 : ℝ) ^ (m + 1) + 3) ≤ 3 ^ (m + 2) := by
      have : (3 : ℝ) ≤ 3 ^ (m + 1) := by
        calc (3 : ℝ) = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have e2 : (3 : ℝ) ^ (m + 2) = 3 * 3 ^ (m + 1) := by ring
      linarith
    have e3 : ((3 : ℝ) ^ (m + 2)) ^ d = 3 ^ (d * (d + 3)) * 3 ^ (d * k) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      rw [hmk]
      ring
    rw [← e3]
    exact pow_le_pow_left₀ (by positivity) h1 d
  calc ((componentEuclideanBall C 0 ((3 : ℝ) ^ (m + 1))).card : ℝ)
      ≤ (2 * (3 : ℝ) ^ (m + 1) + 3) ^ d := hbig
    _ ≤ 3 ^ (d * (d + 3)) * 3 ^ (d * k) := hb
    _ = 3 ^ (d * (d + 3)) / κ * (κ * 3 ^ (d * k)) := by field_simp
    _ ≤ 3 ^ (d * (d + 3)) / κ * (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **(1.18) in dimension `d` with an almost surely finite scale** from the approximation of affine
functions with an almost surely finite scale, the order-zero regularity and the density of the
cluster, by Step 3 of AKM2, Proposition 3.1. -/
theorem correctorSublinearL2Ae_of_affineApproximationAe [NeZero d] (hd : 2 ≤ d)
    (hA : CubeAffineApproximationAe d) : CorrectorSublinearL2Ae d := by
  intro p hpc hp1
  obtain ⟨δA, KA, hδA, hKA, haeA⟩ := hA p hpc hp1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δA (1 / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδA (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_right _ _
  have hδδ : δ ≤ δA := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨s₃, θ₃, C₀, hs₃, hθ₃, hC₀, X₃, -, -, -, -, hae₃⟩ :=
    exists_origin_constant_approximation hd p hpc hp1
  have hθp : 0 < theta d p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨s₄, θ₄, -, -, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (d + 1)
  obtain ⟨M₄, -, hM₄0, -, hM₄ae⟩ := hcube 0
  set κ : ℝ := theta d p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    have := theta_le_one d p
    rw [hκdef]; linarith
  set ρ : ℝ := Real.sqrt ((3 : ℝ) ^ (d * (d + 3)) / κ) with hρdef
  have hρ1 : 1 ≤ ρ := by
    have h3 : (1 : ℝ) ≤ 3 ^ (d * (d + 3)) := one_le_pow₀ (by norm_num)
    rw [hρdef, Real.le_sqrt (by norm_num) (by positivity), one_pow, le_div_iff₀ hκ]; linarith
  set Γ : ℝ := 1 + (1 + ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) +
    C₀ * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (1 - (3 : ℝ) ^ (-δ)) +
    (ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (3 * (3 : ℝ) ^ (-δ) - 1) with hΓ
  have hε1 : (3 : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h3ε : 1 < 3 * (3 : ℝ) ^ (-δ) := by
    have e : 3 * (3 : ℝ) ^ (-δ) = (3 : ℝ) ^ (1 - δ) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num), div_eq_mul_inv]
    rw [e]; exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hΓ0 : 0 ≤ Γ := by
    have : 0 < 1 - (3 : ℝ) ^ (-δ) := by linarith
    have : 0 < 3 * (3 : ℝ) ^ (-δ) - 1 := by linarith
    positivity
  refine ⟨δ, 3 * ρ * (KA * Γ), hδ0, by positivity, ?_⟩
  filter_upwards [haeA, hae₃, hM₄ae] with ω hωA hω₃ hω₄
  intro h q
  obtain ⟨-, hω₃'⟩ := hω₃
  have hLip := hω₃' h
  obtain ⟨mA, hmA⟩ := hωA h q
  obtain ⟨mR, hmR⟩ := eventually_le_three_pow
    (max (X₃ ω) (max (3 ^ (d + 1) * M₄ ω) (3 ^ (d + 1))))
  set m₀ := max mA mR with hm₀
  have hR := hmR m₀ (le_max_right _ _)
  have hX3 : X₃ ω ≤ 3 ^ m₀ := (le_max_left _ _).trans hR
  have hM4 : 3 ^ (d + 1) * M₄ ω ≤ 3 ^ m₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hR
  have h81 : (3 : ℝ) ^ (d + 1) ≤ 3 ^ m₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hR
  have hm₀4 : d + 1 ≤ m₀ := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h81
  have hle : ∀ m, m₀ ≤ m → (3 : ℝ) ^ m₀ ≤ 3 ^ m := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hballs : ∀ m, m₀ ≤ m → 0 < (componentEuclideanBall (uniqueInfiniteComponent h) 0
      ((3 : ℝ) ^ m)).card ∧
      ((componentEuclideanBall (uniqueInfiniteComponent h) 0 ((3 : ℝ) ^ (m + 1))).card : ℝ) ≤
        ρ ^ 2 * (componentEuclideanBall (uniqueInfiniteComponent h) 0 ((3 : ℝ) ^ m)).card := by
    intro m hm
    refine card_ball_bounds _ hκ (hω₄ h) (by linarith) (by omega) ?_
    have h1 : 3 ^ (d + 1) * M₄ ω ≤ 3 ^ m := hM4.trans (hle m hm)
    have e : (3 : ℝ) ^ m = 3 ^ (d + 1) * 3 ^ (m - (d + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [e] at h1
    exact le_of_mul_le_mul_left h1 (by positivity)
  obtain ⟨u, hu, hb⟩ := exists_corrector_of_scales (uniqueInfiniteComponent h) q (m₀ := m₀)
    (K := KA) (δ := δ) (X₀ := X₃ ω) (C₀ := C₀) (ρ := ρ) hKA hδ0 hδ2 hρ1 hC₀.le hX3
    (fun m hm => by
      obtain ⟨v, hvh, hvb⟩ := hmA m ((le_max_left _ _).trans hm)
      refine ⟨v, hvh, hvb.trans ?_⟩
      have h3m : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h3m (by linarith))
        (by positivity))
    hLip (fun m hm => (hballs m hm).1) (fun m hm => (hballs m hm).2)
  exact ⟨u, hu, 3 ^ (m₀ + 1), fun r hr => (hb r hr).trans (le_of_eq (by rw [hΓ]))⟩

end Rigidity.Proofs.Regularity.GeneralDim
