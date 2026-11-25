import PercolationClusterHomogenization.Proofs.Regularity.OrderOneOriginSublinear
import LatticeProb.External.SupercriticalBondCorrectorInput

/-!
# The sublinearity (1.18) of the correctors from (7.18) and the corrected planes

Armstrong and Dario (arXiv:1609.09431v2), Theorem 2 (i) at `k = 1`, quantify the sublinearity of
the correctors: a function `u ∈ 𝒜_1(𝒞_∞)` whose corrector `u - q · x` is sublinear is within
`C |q| r^{1-δ}` of `q · x + c` on `B_r` for every `r ≥ 𝒳`. The proof, as in Armstrong, Kuusi and
Mourrat, Proposition 3.1, is deterministic once (7.18) holds above `𝒳`:

* letting `R → ∞` in (7.18) at `k = 2` and using the linear growth of `u`, the excess of `u` over
  the harmonic quadratic polynomials on `B_r` is at most `A 5^d |q|₁ r^{1-δ}`
  (`excess_two_le_of_slopeAsymptotics`);
* the harmonic quadratic polynomials `w_k` near `u` on the balls `B_{2^k r₀}` have coefficients
  whose differences between consecutive scales are bounded by (7.23); the slopes converge to `q`
  and the quadratic parts to `0` by the sublinearity of `u - q · x`, so that by telescoping
  `u - q · x` is within `C |q|₁ r^{1-δ}` of the constant of the first scale on every `B_r`,
  `r ≥ r₀` (`exists_const_sublinear_of_excess`).

With (7.18) at `k = 2` in every dimension (`mesoscopicDegreeTwoAt_holds`) and the existence of the
corrected planes, this gives (1.18) with a minimal scale of class `O_s`
(`correctorSublinearL2At_of_correctedPlanes`), hence Theorem 2 (iii) at `k = 1` from
`LatticeProb.External.SupercriticalBondCorrectorInput` alone
(`armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput`).
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ} {ω : Configuration d}

/-- The normalization `r^{-d/2} ‖·‖_{ℓ²}` of a function bounded by `M` on `C ∩ B_r`, `r ≥ 1`. -/
theorem clusterBallVolumeL2_le_of_abs_le (C : OpenComponent ω) {r M : ℝ} (hr : 1 ≤ r)
    (hM : 0 ≤ M) {f : C → ℝ} (hf : ∀ x ∈ componentEuclideanBall C 0 r, |f x| ≤ M) :
    clusterBallVolumeL2 C r f ≤ 5 ^ d * M := by
  have hr0 : 0 < r := by linarith
  rw [clusterBallVolumeL2_eq C hr0.le]
  have h1 := componentBallL2_le_of_abs_le C 0 r hM hf
  have h2 : Real.sqrt (((componentEuclideanBall C 0 r).card : ℝ) / r ^ d) ≤ 5 ^ d := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
    exact (card_componentEuclideanBall_le C 0 hr0.le).trans (two_mul_add_three_pow_le hr)
  exact mul_le_mul h2 h1 (componentBallL2_nonneg _ _ _ _) (by positivity)

theorem abs_coord_le_of_mem_componentEuclideanBall (C : OpenComponent ω) {ρ : ℝ} {x : C}
    (hx : x ∈ componentEuclideanBall C 0 ρ) (i : Fin d) : |(x.val i : ℝ)| ≤ ρ := by
  have h := (abs_sub_le_dist_latticeEuclideanEmbedding x.val 0 i).trans
    ((mem_componentEuclideanBall _ _ _ _).1 hx).le
  simpa using h

theorem abs_componentSlope_le_mul (C : OpenComponent ω) (q : Fin d → ℝ) {r : ℝ} {x : C}
    (hx : x ∈ componentEuclideanBall C 0 r) :
    |componentSlope C q x| ≤ (∑ i, |q i|) * r := by
  rw [componentSlope, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_coord_le_of_mem_componentEuclideanBall C hx i)
    (abs_nonneg _)

/-- **Step A: the excess of order two above the scale of (7.18).** -/
theorem excess_two_le_of_slopeAsymptotics (C : OpenComponent ω) {X A δ : ℝ} {q : Fin d → ℝ}
    {u : C → ℝ} (hX1 : 1 ≤ X) (hA : 0 ≤ A)
    (hmeso : ∀ R, 2 * X ≤ R → ∀ r, X ≤ r → r ≤ R / 2 →
      (⨅ w : clusterHarmonicQuadratic C, clusterBallVolumeL2 C r (u - w)) ≤
        A * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic C, clusterBallVolumeL2 C R (u - w)) +
          A * r ^ (-δ) * (r / R) * clusterBallVolumeL2 C R u)
    (hsub : componentSlopeAsymptotics C q u) :
    ∀ r, X ≤ r → (⨅ w : clusterHarmonicQuadratic C, clusterBallVolumeL2 C r (u - w)) ≤
      A * 5 ^ d * (∑ i, |q i|) * r ^ (1 - δ) := by
  intro r hr
  have hr1 : 1 ≤ r := hX1.trans hr
  have hr0 : 0 < r := by linarith
  set B := ∑ i, |q i| with hB
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hrδ : 0 < r ^ (1 - δ) := Real.rpow_pos_of_pos hr0 _
  apply le_of_forall_pos_le_add
  intro η hη
  set ε := η / (2 * (A * 5 ^ d * r ^ (1 - δ)) + 1) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεle : A * 5 ^ d * ε * r ^ (1 - δ) ≤ η / 2 := by
    have h1 : 0 ≤ A * 5 ^ d * r ^ (1 - δ) := by positivity
    rw [hε]
    rw [show A * 5 ^ d * (η / (2 * (A * 5 ^ d * r ^ (1 - δ)) + 1)) * r ^ (1 - δ) =
      η * (A * 5 ^ d * r ^ (1 - δ)) / (2 * (A * 5 ^ d * r ^ (1 - δ)) + 1) by ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨R₀, hR₀, hR₀b⟩ := hsub ε hε0
  set Q := 2 * (A * 5 ^ d * (B + ε) * r ^ 3) / η + 1 with hQ
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  set R := max (max (2 * X) (2 * r)) (max R₀ Q) with hRdef
  have hR2X : 2 * X ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR2r : 2 * r ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRQ : Q ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have h1 := hmeso R hR2X r hr (by linarith)
  -- the bound of `u` on `B_R`
  have hu : clusterBallVolumeL2 C R u ≤ 5 ^ d * ((B + ε) * R) := by
    apply clusterBallVolumeL2_le_of_abs_le C hR1 (by positivity)
    intro x hx
    have h2 := hR₀b R hRR₀ x hx
    have h3 := abs_componentSlope_le_mul C q hx
    have : |u x| ≤ |u x - componentSlope C q x| + |componentSlope C q x| := by
      have := abs_add_le (u x - componentSlope C q x) (componentSlope C q x)
      rwa [sub_add_cancel] at this
    nlinarith
  have hE : (⨅ w : clusterHarmonicQuadratic C, clusterBallVolumeL2 C R (u - w)) ≤
      clusterBallVolumeL2 C R u := by
    have := iInf_le_of_le (f := fun w : clusterHarmonicQuadratic C =>
      clusterBallVolumeL2 C R (u - w)) (fun _ => Real.sqrt_nonneg _) 0
    simpa using this
  have hrR : 0 ≤ r / R := by positivity
  have h4 : A * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic C,
      clusterBallVolumeL2 C R (u - w)) ≤ A * (r / R) ^ 3 * (5 ^ d * ((B + ε) * R)) :=
    mul_le_mul_of_nonneg_left (hE.trans hu) (by positivity)
  have h5 : A * r ^ (-δ) * (r / R) * clusterBallVolumeL2 C R u ≤
      A * r ^ (-δ) * (r / R) * (5 ^ d * ((B + ε) * R)) :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have e5 : A * r ^ (-δ) * (r / R) * (5 ^ d * ((B + ε) * R)) =
      A * 5 ^ d * B * r ^ (1 - δ) + A * 5 ^ d * ε * r ^ (1 - δ) := by
    have : r ^ (1 - δ) = r * r ^ (-δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]
    rw [this]; field_simp
  have h6 : A * (r / R) ^ 3 * (5 ^ d * ((B + ε) * R)) ≤ η / 2 := by
    have e : A * (r / R) ^ 3 * (5 ^ d * ((B + ε) * R)) = A * 5 ^ d * (B + ε) * r ^ 3 / R ^ 2 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have hQR : 2 * (A * 5 ^ d * (B + ε) * r ^ 3) / η ≤ R := by linarith
    rw [div_le_iff₀ hη] at hQR
    have h7 : R * η ≤ R ^ 2 * η :=
      mul_le_mul_of_nonneg_right (by nlinarith) hη.le
    linarith
  linarith

/-! ### Step B: the telescoping of the near-best harmonic quadratic polynomials -/

/-- The density `κ (2 / (6 √d + 6))^d` of the cluster balls above the cube density scale. -/
noncomputable def ballDensityConst (d : ℕ) (κ : ℝ) : ℝ :=
  κ * (2 / (6 * Real.sqrt d + 6)) ^ d

theorem ballDensityConst_pos {κ : ℝ} (hκ : 0 < κ) : 0 < ballDensityConst d κ := by
  unfold ballDensityConst; positivity

theorem one_le_of_quadLocality_le (hd : 0 < d) {ℓ κ R : ℝ} (hκ : 0 < κ)
    (hR : quadLocality d (capFraction d κ) * max ℓ 1 ≤ R) : 1 ≤ R := by
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hΛ24 := le_quadLocality hd (capFraction_pos hd hκ)
  have h2 : quadLocality d (capFraction d κ) * 1 ≤ quadLocality d (capFraction d κ) * max ℓ 1 :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  linarith

theorem card_ball_ge_of_quadLocality (C : OpenComponent ω) (hd : 0 < d) {ℓ κ R : ℝ}
    (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓ κ)
    (hR : quadLocality d (capFraction d κ) * max ℓ 1 ≤ R) :
    ballDensityConst d κ * R ^ d ≤ (componentEuclideanBall C 0 R).card := by
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hΛ24 := le_quadLocality hd (capFraction_pos hd hκ)
  have hmax : 1 ≤ max ℓ 1 := le_max_right _ _
  have hcube3 := hcube.of_le C 0
    (show 3 * Real.sqrt d + 3 ≤ quadLocality d (capFraction d κ) by linarith)
  have h6 : (6 * Real.sqrt d + 6) * max ℓ 1 ≤ R :=
    (mul_le_mul_of_nonneg_right
      (by linarith : 6 * Real.sqrt d + 6 ≤ quadLocality d (capFraction d κ)) (by linarith)).trans hR
  exact card_ball_ge_of_clusterCubeDensity_pow C hκ.le hcube3 h6

theorem componentBallL2_le_of_quadLocality (C : OpenComponent ω) (hd : 0 < d) {ℓ κ R : ℝ}
    (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓ κ)
    (hR : quadLocality d (capFraction d κ) * max ℓ 1 ≤ R) (f : C → ℝ) :
    componentBallL2 C 0 R f ≤ Real.sqrt (1 / ballDensityConst d κ) * clusterBallVolumeL2 C R f :=
  componentBallL2_le_of_card_pow C (by linarith [one_le_of_quadLocality_le hd hκ hR])
    (ballDensityConst_pos hκ) (card_ball_ge_of_quadLocality C hd hκ hcube hR) f

/-- The bound (7.23) of the coefficients of a quadratic polynomial by its normalized `L²` norm on
the cluster ball. -/
theorem quadSlopeD_mul_le_clusterBallVolumeL2 (C : OpenComponent ω) (hd : 0 < d) {ℓ κ R : ℝ}
    (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓ κ)
    (hR : quadLocality d (capFraction d κ) * max ℓ 1 ≤ R) (a : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) :
    quadSlopeD p M R * R ≤ quadSlopeConstD d κ *
      clusterBallVolumeL2 C R (fun x => latticeQuadFunD a p M x.val - c) := by
  have h1 := quadSlopeD_mul_le_componentBallL2 C hd hκ hcube hR a p M c
  have h2 := componentBallL2_le_of_quadLocality C hd hκ hcube hR
    (fun x => latticeQuadFunD a p M x.val - c)
  have e : quadSlopeConstD d κ =
      quadSlopeBallConst d κ * Real.sqrt (1 / ballDensityConst d κ) := rfl
  rw [e, mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (quadSlopeBallConst_nonneg hd hκ))

theorem abs_latticeQuadFunD_sub_const_le (a : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) {y : Vertex d}
    (hy : ∀ i, |(y i : ℝ)| ≤ ρ) :
    |latticeQuadFunD a p M y - a| ≤ d * ρ * quadSlopeD p M ρ := by
  have h := abs_latticeQuadFunD_sub_le a p M (x := 0) (fun i => by simpa using hρ) hy
  have h0 : latticeQuadFunD a p M 0 = a := by
    simp [latticeQuadFunD, latticeEuclideanEmbedding_zero, quadForm]
  rw [h0] at h
  have hs : ∑ i, |((y i - (0 : Vertex d) i : ℤ) : ℝ)| ≤ d * ρ := by
    have h' : ∀ i ∈ (univ : Finset (Fin d)), |((y i - (0 : Vertex d) i : ℤ) : ℝ)| ≤ ρ :=
      fun i _ => by simpa using hy i
    simpa using sum_le_sum h'
  calc |latticeQuadFunD a p M y - a| ≤ quadSlopeD p M ρ * ∑ i, |((y i - (0 : Vertex d) i : ℤ) : ℝ)| :=
        h
    _ ≤ quadSlopeD p M ρ * (d * ρ) := mul_le_mul_of_nonneg_left hs (quadSlopeD_nonneg p M hρ)
    _ = d * ρ * quadSlopeD p M ρ := by ring

theorem quadSlopeD_add_le (p p' : EuclideanSpace ℝ (Fin d)) (M M' : Matrix (Fin d) (Fin d) ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    quadSlopeD (p + p') (M + M') ρ ≤ quadSlopeD p M ρ + quadSlopeD p' M' ρ := by
  unfold quadSlopeD
  have h1 : ∑ i, |(p + p') i| ≤ ∑ i, |p i| + ∑ i, |p' i| := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun i _ => by rw [PiLp.add_apply]; exact abs_add_le _ _
  have h2 : ∑ i, ∑ j, |symEntry (M + M') i j| ≤
      ∑ i, ∑ j, |symEntry M i j| + ∑ i, ∑ j, |symEntry M' i j| := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    have e : symEntry (M + M') i j = symEntry M i j + symEntry M' i j := by
      simp only [symEntry, Matrix.add_apply]; ring
    rw [e]; exact abs_add_le _ _
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * ρ)
  linarith

theorem quadSlopeD_mono (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    {ρ ρ' : ℝ} (h : ρ ≤ ρ') : quadSlopeD p M ρ ≤ quadSlopeD p M ρ' := by
  unfold quadSlopeD
  have : 0 ≤ ∑ i, ∑ j, |symEntry M i j| := by positivity
  have h2 : 2 * ρ * ∑ i, ∑ j, |symEntry M i j| ≤ 2 * ρ' * ∑ i, ∑ j, |symEntry M i j| :=
    mul_le_mul_of_nonneg_right (by linarith) this
  linarith

theorem latticeQuadFunD_sub (a a' : ℝ) (p p' : EuclideanSpace ℝ (Fin d))
    (M M' : Matrix (Fin d) (Fin d) ℝ) (y : Vertex d) :
    latticeQuadFunD (a - a') (p - p') (M - M') y =
      latticeQuadFunD a p M y - latticeQuadFunD a' p' M' y := by
  simp only [latticeQuadFunD, inner_sub_left, quadForm, Matrix.sub_apply, sub_mul,
    sum_sub_distrib]
  ring

theorem componentSlope_eq_inner (C : OpenComponent ω) (q : Fin d → ℝ) (x : C) :
    componentSlope C q x =
      inner ℝ (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin d)) (latticeEuclideanEmbedding x.val) := by
  simp [componentSlope, latticeEuclideanEmbedding, PiLp.inner_apply, mul_comm]

theorem two_pow_mul_rpow (k : ℕ) {X : ℝ} (hX : 0 < X) (t : ℝ) :
    ((2 : ℝ) ^ k * X) ^ t = X ^ t * ((2 : ℝ) ^ t) ^ k := by
  rw [Real.mul_rpow (by positivity) hX.le, mul_comm]
  congr 1
  have e1 : ((2 : ℝ) ^ k) ^ t = (2 : ℝ) ^ ((k : ℝ) * t) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have e2 : ((2 : ℝ) ^ t) ^ k = (2 : ℝ) ^ ((k : ℝ) * t) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [e1, e2]

theorem rpow_le_two_mul_rpow {δ s t : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hs : 0 < s) (hst : s ≤ t)
    (ht : t ≤ 2 * s) : t ^ (1 - δ) ≤ 2 * s ^ (1 - δ) := by
  have h1 : t ^ (1 - δ) ≤ (2 * s) ^ (1 - δ) :=
    Real.rpow_le_rpow (by linarith) ht (by linarith)
  rw [Real.mul_rpow (by norm_num) hs.le] at h1
  have h2 : (2 : ℝ) ^ (1 - δ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 - δ ≤ 1)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hs.le _))

theorem geom_sum_le_one_div {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (m : ℕ) :
    ∑ i ∈ range m, θ ^ i ≤ 1 / (1 - θ) := by
  have hpos : 0 < 1 - θ := by linarith
  rw [le_div_iff₀ hpos]
  have e : (∑ i ∈ range m, θ ^ i) * (1 - θ) = 1 - θ ^ m := by
    have := geom_sum_mul_neg θ m
    linarith
  rw [e]
  linarith [pow_nonneg h0 m]

/-- The telescoping of a decaying sequence. -/
theorem le_of_telescoping {S s : ℕ → ℝ} {c θ : ℝ} (hc : 0 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hstep : ∀ n, S n ≤ s n + S (n + 1)) (hs : ∀ n, s n ≤ c * θ ^ n)
    (hlim : ∀ η, 0 < η → ∃ n₀, ∀ n, n₀ ≤ n → S n ≤ η) (j : ℕ) :
    S j ≤ c * θ ^ j / (1 - θ) := by
  have htel : ∀ m, S j ≤ ∑ i ∈ range m, c * θ ^ (j + i) + S (j + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      show S j ≤ _ + S (j + m + 1)
      linarith [hstep (j + m), hs (j + m)]
  have hgeo : ∀ m, ∑ i ∈ range m, c * θ ^ (j + i) ≤ c * θ ^ j / (1 - θ) := by
    intro m
    have e : ∑ i ∈ range m, c * θ ^ (j + i) = c * θ ^ j * ∑ i ∈ range m, θ ^ i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [pow_add]; ring
    rw [e]
    calc c * θ ^ j * ∑ i ∈ range m, θ ^ i ≤ c * θ ^ j * (1 / (1 - θ)) :=
          mul_le_mul_of_nonneg_left (geom_sum_le_one_div hθ0 hθ1 m) (by positivity)
      _ = c * θ ^ j / (1 - θ) := by ring
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨n₀, hn₀⟩ := hlim η hη
  linarith [htel n₀, hn₀ (j + n₀) (by omega), hgeo n₀]

/-- The sum of geometrically growing increments. -/
theorem abs_sub_le_of_geometric {a : ℕ → ℝ} {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 1 < ρ)
    (h : ∀ k, |a k - a (k + 1)| ≤ c * ρ ^ k) (j : ℕ) : |a 0 - a j| ≤ c * ρ ^ j / (ρ - 1) := by
  have hρ0 : 0 < ρ - 1 := by linarith
  have key : ∀ j, |a 0 - a j| ≤ c * (ρ ^ j - 1) / (ρ - 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : |a 0 - a (j + 1)| ≤ |a 0 - a j| + |a j - a (j + 1)| := abs_sub_le _ _ _
      have e : c * (ρ ^ (j + 1) - 1) / (ρ - 1) = c * (ρ ^ j - 1) / (ρ - 1) + c * ρ ^ j := by
        field_simp
        ring
      rw [e]; linarith [h j]
  calc |a 0 - a j| ≤ c * (ρ ^ j - 1) / (ρ - 1) := key j
    _ ≤ c * ρ ^ j / (ρ - 1) := by
      rw [div_le_div_iff_of_pos_right hρ0]
      nlinarith

theorem mul_div_two_mul_add_one_le {t η : ℝ} (ht : 0 ≤ t) (hη : 0 < η) :
    t * (η / (2 * (t + 1))) ≤ η / 2 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The constant of (1.18) obtained by the telescoping. -/
noncomputable def sublinearConstD (d : ℕ) (κ δ : ℝ) : ℝ :=
  2 * (Real.sqrt (2 ^ d) +
    5 ^ d * d * (quadSlopeConstD d κ * (1 + 2 * Real.sqrt (2 ^ d)) / (1 - (2 : ℝ) ^ (-δ))) +
    5 ^ d * ((Real.sqrt (1 / ballDensityConst d κ) + d * quadSlopeConstD d κ) *
      (1 + 2 * Real.sqrt (2 ^ d)) / ((2 : ℝ) ^ (1 - δ) - 1)))

/-- **Step B: the telescoping.** If above the radius `X` the excess of `u` over the harmonic
quadratic polynomials on `B_r` is at most `K r^{1-δ}` and `u - q · x` is sublinear, then
`u - q · x` is within `C K r^{1-δ}` of one constant on every `B_r`, `r ≥ X`. -/
theorem exists_const_sublinear_of_excess (C : OpenComponent ω) (hd : 0 < d) {X K δ κ ℓ : ℝ}
    {q : Fin d → ℝ} {u : C → ℝ} (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓ κ)
    (hX : quadLocality d (capFraction d κ) * max ℓ 1 ≤ X) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hK : 0 ≤ K)
    (hexc : ∀ r, X ≤ r → ∃ w ∈ clusterHarmonicQuadratic C,
      clusterBallVolumeL2 C r (u - w) ≤ K * r ^ (1 - δ))
    (hsub : componentSlopeAsymptotics C q u) :
    ∃ c : ℝ, ∀ r, X ≤ r → clusterBallVolumeL2 C r (fun x => u x - componentSlope C q x - c) ≤
      sublinearConstD d κ δ * K * r ^ (1 - δ) := by
  classical
  have hX1 : 1 ≤ X := one_le_of_quadLocality_le hd hκ hX
  have hX0 : 0 < X := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, ∀ k, r k = 2 ^ k * X := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ k, 0 < r k := fun k => by rw [hr]; positivity
  have hrX : ∀ k, X ≤ r k := fun k => by
    rw [hr]; exact le_mul_of_one_le_left hX0.le (one_le_pow₀ (by norm_num))
  have hrs : ∀ k, r (k + 1) = 2 * r k := fun k => by rw [hr, hr, pow_succ]; ring
  have hrle : ∀ k, r k ≤ r (k + 1) := fun k => by rw [hrs]; linarith [hr0 k]
  have hRk : ∀ k, quadLocality d (capFraction d κ) * max ℓ 1 ≤ r k := fun k => hX.trans (hrX k)
  have hr1 : ∀ k, 1 ≤ r k := fun k => hX1.trans (hrX k)
  choose w hwm hw using fun k => hexc (r k) (hrX k)
  have hwm' : ∀ k, ∃ (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ),
      M.trace = 0 ∧ ∀ x, w k x = a + inner ℝ p (latticeEuclideanEmbedding x.val) +
        quadForm M (latticeEuclideanEmbedding x.val) := fun k => hwm k
  choose a p M _hMt hwe using hwm'
  have hwq : ∀ k (x : C), w k x = latticeQuadFunD (a k) (p k) (M k) x.val := fun k x => hwe k x
  -- the constants
  obtain ⟨cS, hcS⟩ : ∃ c, c = quadSlopeConstD d κ := ⟨_, rfl⟩
  have hcS0 : 0 ≤ cS := hcS ▸ quadSlopeConstD_nonneg hd hκ
  obtain ⟨κ₁, hκ₁⟩ : ∃ c, c = ballDensityConst d κ := ⟨_, rfl⟩
  have hκ₁0 : 0 < κ₁ := hκ₁ ▸ ballDensityConst_pos hκ
  have hsq : 0 ≤ Real.sqrt (2 ^ d) := Real.sqrt_nonneg _
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = 1 + 2 * Real.sqrt (2 ^ d) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  obtain ⟨θ, hθ⟩ : ∃ c, c = (2 : ℝ) ^ (-δ) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := hθ ▸ Real.rpow_nonneg (by norm_num) _
  have hθ1 : θ < 1 := hθ ▸ Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨ρ, hρ⟩ : ∃ c, c = (2 : ℝ) ^ (1 - δ) := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := hρ ▸ Real.one_lt_rpow (by norm_num) (by linarith)
  have hpowθ : ∀ k, (r k) ^ (-δ) = X ^ (-δ) * θ ^ k := fun k => by
    rw [hr, hθ]; exact two_pow_mul_rpow k hX0 _
  have hpowρ : ∀ k, (r k) ^ (1 - δ) = X ^ (1 - δ) * ρ ^ k := fun k => by
    rw [hr, hρ]; exact two_pow_mul_rpow k hX0 _
  have hXθ : X ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
  have hrr : ∀ k, (r k) ^ (1 - δ) = (r k) ^ (-δ) * r k := fun k => by
    rw [sub_eq_neg_add, Real.rpow_add (hr0 k), Real.rpow_one]
  -- the differences of consecutive polynomials
  have hD : ∀ k, clusterBallVolumeL2 C (r k)
      (fun x => latticeQuadFunD (a k - a (k + 1)) (p k - p (k + 1)) (M k - M (k + 1)) x.val) ≤
      c₁ * K * (r k) ^ (1 - δ) := by
    intro k
    have e : (fun x : C => latticeQuadFunD (a k - a (k + 1)) (p k - p (k + 1)) (M k - M (k + 1))
        x.val) = (u - w (k + 1)) - (u - w k) := by
      funext x; simp only [Pi.sub_apply, hwq, latticeQuadFunD_sub]; ring
    rw [e]
    have h1 := clusterBallVolumeL2_sub_leD C (hr0 k).le (u - w (k + 1)) (u - w k)
    have h2 := clusterBallVolumeL2_le_sqrt_mul C (hr0 k) (hrle k) (u - w (k + 1))
    have h3 : r (k + 1) / r k = 2 := by rw [hrs, mul_div_assoc, div_self (hr0 k).ne', mul_one]
    rw [h3] at h2
    have h5 : (r (k + 1)) ^ (1 - δ) ≤ 2 * (r k) ^ (1 - δ) :=
      rpow_le_two_mul_rpow hδ0.le hδ1 (hr0 k) (hrle k) (hrs k).le
    have h6 := mul_le_mul_of_nonneg_left
      ((hw (k + 1)).trans (mul_le_mul_of_nonneg_left h5 hK)) hsq
    have h7 := hw k
    rw [hc₁]
    linarith
  -- the slopes of the differences
  have hsD : ∀ k, quadSlopeD (p k - p (k + 1)) (M k - M (k + 1)) (r k) ≤
      cS * c₁ * K * X ^ (-δ) * θ ^ k := by
    intro k
    have h1 := quadSlopeD_mul_le_clusterBallVolumeL2 C hd hκ hcube (hRk k) (a k - a (k + 1))
      (p k - p (k + 1)) (M k - M (k + 1)) 0
    simp only [sub_zero] at h1
    rw [← hcS] at h1
    have h2 := h1.trans (mul_le_mul_of_nonneg_left (hD k) hcS0)
    rw [hrr k, hpowθ k] at h2
    have h3 : quadSlopeD (p k - p (k + 1)) (M k - M (k + 1)) (r k) * r k ≤
        (cS * c₁ * K * X ^ (-δ) * θ ^ k) * r k := h2.trans (le_of_eq (by ring))
    exact le_of_mul_le_mul_right h3 (hr0 k)
  -- the slopes against `q`
  obtain ⟨qE, hqE⟩ : ∃ v : EuclideanSpace ℝ (Fin d), v = WithLp.toLp 2 q := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ n, S n = quadSlopeD (p n - qE) (M n) (r n) :=
    ⟨_, fun _ => rfl⟩
  have hSn : ∀ ε, 0 < ε → ∃ n₂ : ℕ, ∀ n, n₂ ≤ n → S n ≤ cS * K * θ ^ n + cS * 5 ^ d * ε := by
    intro ε hε
    obtain ⟨R₀, -, hR₀⟩ := hsub ε hε
    obtain ⟨n₂, hn₂⟩ := pow_unbounded_of_one_lt R₀ (by norm_num : (1 : ℝ) < 2)
    refine ⟨n₂, fun n hn => ?_⟩
    have hRn : R₀ ≤ r n := by
      have h1 : (2 : ℝ) ^ n₂ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
      have h2 : (2 : ℝ) ^ n ≤ r n := by
        rw [hr]; exact le_mul_of_one_le_right (by positivity) hX1
      linarith
    have h1 := quadSlopeD_mul_le_clusterBallVolumeL2 C hd hκ hcube (hRk n) (a n) (p n - qE)
      (M n) 0
    rw [← hcS] at h1
    have e : (fun x : C => latticeQuadFunD (a n) (p n - qE) (M n) x.val - 0) =
        (u - fun x => componentSlope C q x) - (u - w n) := by
      funext x
      simp only [Pi.sub_apply, hwq, latticeQuadFunD, inner_sub_left, componentSlope_eq_inner, hqE]
      ring
    rw [e] at h1
    have h2 := clusterBallVolumeL2_sub_leD C (hr0 n).le (u - fun x => componentSlope C q x)
      (u - w n)
    have h3 : clusterBallVolumeL2 C (r n) (u - fun x => componentSlope C q x) ≤
        5 ^ d * (ε * r n) :=
      clusterBallVolumeL2_le_of_abs_le C (hr1 n) (by positivity [hr0 n])
        fun x hx => hR₀ (r n) hRn x hx
    have h4 := hw n
    rw [hrr n, hpowθ n] at h4
    have h5 : S n * r n ≤ (cS * K * X ^ (-δ) * θ ^ n + cS * 5 ^ d * ε) * r n := by
      calc S n * r n = quadSlopeD (p n - qE) (M n) (r n) * r n := by rw [hS]
        _ ≤ cS * clusterBallVolumeL2 C (r n)
            ((u - fun x => componentSlope C q x) - (u - w n)) := h1
        _ ≤ cS * (5 ^ d * (ε * r n) + K * (X ^ (-δ) * θ ^ n * r n)) :=
            mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hcS0
        _ = _ := by ring
    have h6 := le_of_mul_le_mul_right h5 (hr0 n)
    have h7 := mul_le_mul_of_nonneg_left hXθ
      (mul_nonneg (mul_nonneg hcS0 hK) (pow_nonneg hθ0 n))
    linarith
  have hlim : ∀ η, 0 < η → ∃ n₀, ∀ n, n₀ ≤ n → S n ≤ η := by
    intro η hη
    have hε : 0 < η / (2 * (cS * 5 ^ d + 1)) := by positivity
    obtain ⟨n₂, hn₂⟩ := hSn _ hε
    obtain ⟨n₁, hn₁⟩ := exists_pow_lt_of_lt_one
      (show 0 < η / (2 * (cS * K + 1)) by positivity) hθ1
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    have h1 := hn₂ n (le_of_max_le_right hn)
    have h2 : θ ^ n ≤ θ ^ n₁ := pow_le_pow_of_le_one hθ0 hθ1.le (le_of_max_le_left hn)
    have h3 := mul_div_two_mul_add_one_le (mul_nonneg hcS0 hK) hη
    have h4 := mul_div_two_mul_add_one_le
      (mul_nonneg hcS0 (by positivity : (0 : ℝ) ≤ 5 ^ d)) hη
    have h5 : cS * K * θ ^ n ≤ cS * K * (η / (2 * (cS * K + 1))) :=
      mul_le_mul_of_nonneg_left (h2.trans hn₁.le) (mul_nonneg hcS0 hK)
    linarith
  have hstep : ∀ n, S n ≤ quadSlopeD (p n - p (n + 1)) (M n - M (n + 1)) (r n) + S (n + 1) := by
    intro n
    have e1 : p n - qE = (p n - p (n + 1)) + (p (n + 1) - qE) := by abel
    have e2 : M n = (M n - M (n + 1)) + M (n + 1) := by abel
    have h1 := quadSlopeD_add_le (p n - p (n + 1)) (p (n + 1) - qE) (M n - M (n + 1))
      (M (n + 1)) (hr0 n).le
    rw [← e1, ← e2] at h1
    rw [hS, hS]
    exact h1.trans (add_le_add le_rfl (quadSlopeD_mono _ _ (hrle n)))
  have hc₂ : 0 ≤ cS * c₁ * K * X ^ (-δ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hcS0 hc₁0) hK) (Real.rpow_nonneg hX0.le _)
  have hSj : ∀ j, S j ≤ cS * c₁ * K * X ^ (-δ) * θ ^ j / (1 - θ) := fun j =>
    le_of_telescoping (s := fun n => quadSlopeD (p n - p (n + 1)) (M n - M (n + 1)) (r n))
      hc₂ hθ0 hθ1 hstep hsD hlim j
  -- the constants of the polynomials
  have hcard : ∀ k, (componentEuclideanBall C 0 (r k)).Nonempty := fun k => by
    have h := card_ball_ge_of_quadLocality C hd hκ hcube (hRk k)
    rw [← hκ₁] at h
    have h' : (0 : ℝ) < (componentEuclideanBall C 0 (r k)).card :=
      lt_of_lt_of_le (mul_pos hκ₁0 (pow_pos (hr0 k) d)) h
    exact Finset.card_pos.1 (by exact_mod_cast h')
  obtain ⟨c₄, hc₄⟩ : ∃ c, c = (Real.sqrt (1 / κ₁) + d * cS) * c₁ := ⟨_, rfl⟩
  have hc₄0 : 0 ≤ c₄ := by rw [hc₄]; positivity
  have ha : ∀ k, |a k - a (k + 1)| ≤ c₄ * K * X ^ (1 - δ) * ρ ^ k := by
    intro k
    obtain ⟨f, hf⟩ : ∃ f : C → ℝ, f = fun x => latticeQuadFunD (a k - a (k + 1))
        (p k - p (k + 1)) (M k - M (k + 1)) x.val := ⟨_, rfl⟩
    have h1 : |a k - a (k + 1)| = componentBallL2 C 0 (r k) (fun _ => a k - a (k + 1)) :=
      (LatticeProb.Percolation.componentBallL2_const C 0 (r k) _ (hcard k)).symm
    have e : (fun _ : C => a k - a (k + 1)) = f + fun x => (a k - a (k + 1)) - f x := by
      funext x; simp
    have h2 := LatticeProb.Percolation.componentBallL2_add_le C 0 (r k) f
      (fun x => (a k - a (k + 1)) - f x)
    have h3 := componentBallL2_le_of_quadLocality C hd hκ hcube (hRk k) f
    rw [← hκ₁] at h3
    have hsk0 := quadSlopeD_nonneg (p k - p (k + 1)) (M k - M (k + 1)) (hr0 k).le
    have h4 : componentBallL2 C 0 (r k) (fun x => (a k - a (k + 1)) - f x) ≤
        d * r k * quadSlopeD (p k - p (k + 1)) (M k - M (k + 1)) (r k) := by
      apply componentBallL2_le_of_abs_le C 0 (r k)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (hr0 k).le) hsk0)
      intro x hx
      rw [abs_sub_comm, hf]
      exact abs_latticeQuadFunD_sub_const_le _ _ _ (hr0 k).le
        (abs_coord_le_of_mem_componentEuclideanBall C hx)
    have h5 := mul_le_mul_of_nonneg_left (hf ▸ hD k) (Real.sqrt_nonneg (1 / κ₁))
    have h6 : d * r k * quadSlopeD (p k - p (k + 1)) (M k - M (k + 1)) (r k) ≤
        d * r k * (cS * c₁ * K * r k ^ (-δ)) :=
      (mul_le_mul_of_nonneg_left (hsD k) (mul_nonneg (Nat.cast_nonneg d) (hr0 k).le)).trans
        (le_of_eq (by rw [hpowθ k]; ring))
    rw [show c₄ * K * X ^ (1 - δ) * ρ ^ k = c₄ * K * (r k ^ (-δ) * r k) by
      rw [← hrr k, hpowρ k]; ring]
    rw [hrr k] at h5
    rw [h1, e]
    have h7 : c₄ * K * (r k ^ (-δ) * r k) = Real.sqrt (1 / κ₁) * (c₁ * K * (r k ^ (-δ) * r k)) +
        d * r k * (cS * c₁ * K * r k ^ (-δ)) := by rw [hc₄]; ring
    linarith
  have hc₅ : 0 ≤ c₄ * K * X ^ (1 - δ) :=
    mul_nonneg (mul_nonneg hc₄0 hK) (Real.rpow_nonneg hX0.le _)
  have haj : ∀ j, |a 0 - a j| ≤ c₄ * K * X ^ (1 - δ) * ρ ^ j / (ρ - 1) :=
    abs_sub_le_of_geometric hc₅ hρ1 ha
  -- every radius
  refine ⟨a 0, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := hX1.trans ht
  have hex : ∃ j, t ≤ r j := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (t / X) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [hr]; rw [div_lt_iff₀ hX0] at hn; linarith
  obtain ⟨j, hjdef⟩ : ∃ j, j = Nat.find hex := ⟨_, rfl⟩
  have hj1 : t ≤ r j := hjdef ▸ Nat.find_spec hex
  have hj2 : r j ≤ 2 * t := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, hr, pow_zero, one_mul]; linarith
    · obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have : ¬ t ≤ r i := Nat.find_min hex (by omega)
      rw [hi, hrs]; linarith
  have e : (fun x => u x - componentSlope C q x - a 0) =
      ((u - w j) + fun x => latticeQuadFunD 0 (p j - qE) (M j) x.val) + fun _ => a j - a 0 := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, hwq, latticeQuadFunD, inner_sub_left,
      componentSlope_eq_inner, hqE]
    ring
  rw [e]
  have h1 := clusterBallVolumeL2_triangle C ht0.le
    ((u - w j) + fun x => latticeQuadFunD 0 (p j - qE) (M j) x.val) (fun _ => a j - a 0)
  have h2 := clusterBallVolumeL2_triangle C ht0.le (u - w j)
    (fun x => latticeQuadFunD 0 (p j - qE) (M j) x.val)
  have hrt : (r j) ^ (1 - δ) ≤ 2 * t ^ (1 - δ) := rpow_le_two_mul_rpow hδ0.le hδ1 ht0 hj1 hj2
  -- the first term
  have h3 := clusterBallVolumeL2_le_sqrt_mul C ht0 hj1 (u - w j)
  have h3' : Real.sqrt ((r j / t) ^ d) ≤ Real.sqrt (2 ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity [hr0 j])
      (by rw [div_le_iff₀ ht0]; linarith) d)
  have hP1 : clusterBallVolumeL2 C t (u - w j) ≤ Real.sqrt (2 ^ d) * (K * (2 * t ^ (1 - δ))) :=
    h3.trans (mul_le_mul h3' ((hw j).trans (mul_le_mul_of_nonneg_left hrt hK))
      (Real.sqrt_nonneg _) hsq)
  -- the second term
  obtain ⟨e₁, he₁⟩ : ∃ c, c = cS * c₁ / (1 - θ) := ⟨_, rfl⟩
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; exact div_nonneg (mul_nonneg hcS0 hc₁0) (by linarith)
  have hSj' : S j ≤ e₁ * K * r j ^ (-δ) := by
    rw [hpowθ j, he₁]
    have := hSj j
    have e' : cS * c₁ * K * X ^ (-δ) * θ ^ j / (1 - θ) =
        cS * c₁ / (1 - θ) * K * (X ^ (-δ) * θ ^ j) := by ring
    linarith
  have hSj0 : 0 ≤ S j := by rw [hS]; exact quadSlopeD_nonneg _ _ (hr0 j).le
  have hP2 : clusterBallVolumeL2 C t (fun x => latticeQuadFunD 0 (p j - qE) (M j) x.val) ≤
      5 ^ d * (d * r j * S j) := by
    apply clusterBallVolumeL2_le_of_abs_le C ht1
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (hr0 j).le) hSj0)
    intro x hx
    have h := abs_latticeQuadFunD_sub_const_le 0 (p j - qE) (M j) (hr0 j).le (y := x.val)
      (fun i => (abs_coord_le_of_mem_componentEuclideanBall C hx i).trans hj1)
    rw [sub_zero] at h
    rw [hS]
    exact h
  have hP2' : 5 ^ d * (d * r j * S j) ≤ 5 ^ d * d * e₁ * K * (2 * t ^ (1 - δ)) := by
    have h5 := mul_le_mul_of_nonneg_left hSj'
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 5 ^ d) (mul_nonneg (Nat.cast_nonneg d) (hr0 j).le))
    have h6 := mul_le_mul_of_nonneg_left hrt
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 5 ^ d)
        (Nat.cast_nonneg d)) he₁0) hK)
    rw [hrr j] at h6
    calc 5 ^ d * (d * r j * S j) ≤ 5 ^ d * (d * r j) * (e₁ * K * r j ^ (-δ)) := by linarith
      _ = 5 ^ d * d * e₁ * K * (r j ^ (-δ) * r j) := by ring
      _ ≤ _ := h6
  -- the third term
  obtain ⟨e₂, he₂⟩ : ∃ c, c = c₄ / (ρ - 1) := ⟨_, rfl⟩
  have he₂0 : 0 ≤ e₂ := by rw [he₂]; exact div_nonneg hc₄0 (by linarith)
  have hP3 : clusterBallVolumeL2 C t (fun _ => a j - a 0) ≤ 5 ^ d * |a j - a 0| :=
    clusterBallVolumeL2_le_of_abs_le C ht1 (abs_nonneg _) fun _ _ => le_rfl
  have hP3' : 5 ^ d * |a j - a 0| ≤ 5 ^ d * e₂ * K * (2 * t ^ (1 - δ)) := by
    have h5 := haj j
    rw [abs_sub_comm] at h5
    have e' : c₄ * K * X ^ (1 - δ) * ρ ^ j / (ρ - 1) = e₂ * K * (X ^ (1 - δ) * ρ ^ j) := by
      rw [he₂]; ring
    rw [e', ← hpowρ j] at h5
    have h6 := mul_le_mul_of_nonneg_left hrt
      (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 5 ^ d) he₂0) hK)
    have h7 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 5 ^ d)
    calc 5 ^ d * |a j - a 0| ≤ 5 ^ d * (e₂ * K * r j ^ (1 - δ)) := h7
      _ = 5 ^ d * e₂ * K * r j ^ (1 - δ) := by ring
      _ ≤ _ := h6
  have hconst : sublinearConstD d κ δ =
      2 * (Real.sqrt (2 ^ d) + 5 ^ d * d * e₁ + 5 ^ d * e₂) := by
    rw [he₁, he₂, hc₄, hc₁, hcS, hκ₁, hθ, hρ, sublinearConstD]
  rw [hconst]
  have hfin : 2 * (Real.sqrt (2 ^ d) + 5 ^ d * d * e₁ + 5 ^ d * e₂) * K * t ^ (1 - δ) =
      Real.sqrt (2 ^ d) * (K * (2 * t ^ (1 - δ))) + 5 ^ d * d * e₁ * K * (2 * t ^ (1 - δ)) +
        5 ^ d * e₂ * K * (2 * t ^ (1 - δ)) := by ring
  linarith

theorem sublinearConstD_nonneg (hd : 0 < d) {κ δ : ℝ} (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ sublinearConstD d κ δ := by
  have h1 : (2 : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h2 : 1 < (2 : ℝ) ^ (1 - δ) := Real.one_lt_rpow (by norm_num) (by linarith)
  have h3 := quadSlopeConstD_nonneg hd hκ
  have h4 : 0 < 1 - (2 : ℝ) ^ (-δ) := by linarith
  have h5 : 0 < (2 : ℝ) ^ (1 - δ) - 1 := by linarith
  unfold sublinearConstD
  positivity

/-! ### Step C: the minimal scale -/

/-- **Armstrong–Dario, (1.18), with a minimal scale of class `O_s`, in every dimension**, from
(7.18) at `k = 2` (`mesoscopicDegreeTwoAt_holds`), the density of the cluster in cubes and the
existence of the corrected planes. -/
theorem correctorSublinearL2At_of_correctedPlanes [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcp : ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin d → ℝ,
      ∀ _ : uniqueInfiniteComponent h, ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u) :
    CorrectorSublinearL2At d p := by
  have hd0 : 0 < d := by omega
  obtain ⟨s₁, C₁, δ₀, hs₁, hC₁, hδ₀, X₁, hX₁m, hX₁0, hX₁os, A₀, hae₁⟩ :=
    mesoscopicDegreeTwoAt_holds hd hpc hp1
  have hθp : 0 < LatticeProb.Percolation.theta d p :=
    Rigidity.Percolation.theta_pos_of_criticalProbability_lt d p hpc
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = LatticeProb.Percolation.theta d p / 2 := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hΛ24 := le_quadLocality hd0 (capFraction_pos hd0 hκ)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd0)
  have hΛ1 : 1 ≤ quadLocality d (capFraction d κ) := by linarith
  obtain ⟨s₂, C₂, hs₂, hC₂, hcube⟩ := exists_clusterCubeDensity_of_concentration hd p
    (cluster_density_concentration d hd p hpc hp1) (quadLocality d (capFraction d κ))
  obtain ⟨M₂, hM₂m, hM₂0, hM₂os, hae₂⟩ := hcube 0
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₀ (1 / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδdef ▸ lt_min hδ₀ (by norm_num)
  have hδ1 : δ < 1 := hδdef ▸ (min_le_right _ _).trans_lt (by norm_num)
  have hδδ₀ : δ ≤ δ₀ := hδdef ▸ min_le_left _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max A₀ 0 := ⟨_, rfl⟩
  have hA : 0 ≤ A := hAdef ▸ le_max_right _ _
  have hAA₀ : A₀ ≤ A := hAdef ▸ le_max_left _ _
  -- the scale
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = min s₁ s₂ := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ lt_min hs₁ hs₂
  have h1os := IsOsBond.mono_exponent hs (hsdef ▸ min_le_left _ _) hX₁m hX₁os
  have h2os := IsOsBond.mono_exponent hs (hsdef ▸ min_le_right _ _) hM₂m hM₂os
  have h3os := isOsBond_const (d := d) (p := p) one_pos hs
  have h23 := IsOsBond.max hs (by positivity) (by positivity) hM₂m measurable_const h2os h3os
  have h123 := IsOsBond.max hs (by positivity) (by positivity) hX₁m
    (hM₂m.max measurable_const) h1os h23
  have hc₀ : 0 < quadLocality d (capFraction d κ) + 1 := by linarith
  have hXos := IsOsBond.const_mul hc₀ h123
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.sqrt (1 / ballDensityConst d κ) * sublinearConstD d κ δ *
      (A * 5 ^ d + 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (sublinearConstD_nonneg hd0 hκ hδ0 hδ1)) (by positivity)
  refine ⟨s, δ, _, K, hs, hδ0, by positivity, hK0,
    fun ω => (quadLocality d (capFraction d κ) + 1) * max (X₁ ω) (max (M₂ ω) 1),
    (hX₁m.max (hM₂m.max measurable_const)).const_mul _, fun ω => ?_, hXos, ?_⟩
  · exact mul_nonneg hc₀.le ((hX₁0 ω).trans (le_max_left _ _))
  filter_upwards [hae₁, hae₂, hcp] with ω h₁ h₂ h₃
  intro h q
  have hc : ClusterCubeDensity (uniqueInfiniteComponent h) 0 (quadLocality d (capFraction d κ))
      (M₂ ω) κ := by
    have h' := h₂ h
    rwa [← hκdef] at h'
  obtain ⟨m, hm⟩ : ∃ m, m = max (X₁ ω) (max (M₂ ω) 1) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := hm ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hmX : X₁ ω ≤ m := hm ▸ le_max_left _ _
  have hmM : max (M₂ ω) 1 ≤ m := hm ▸ le_max_right _ _
  obtain ⟨Xω, hXω⟩ : ∃ x, x = (quadLocality d (capFraction d κ) + 1) * m := ⟨_, rfl⟩
  have hXΛ : quadLocality d (capFraction d κ) * max (M₂ ω) 1 ≤ Xω := by
    rw [hXω]
    have h1 := mul_le_mul_of_nonneg_left hmM (by linarith : 0 ≤ quadLocality d (capFraction d κ))
    nlinarith
  have hXX₁ : X₁ ω ≤ Xω := by rw [hXω]; nlinarith
  have hX1 : 1 ≤ Xω := by rw [hXω]; nlinarith
  have hscale : ∀ r : ℝ, (quadLocality d (capFraction d κ) + 1) *
      max (X₁ ω) (max (M₂ ω) 1) ≤ r → Xω ≤ r := fun r hr => by rw [hXω, hm]; exact hr
  by_cases hq : ∑ i, |q i| = 0
  · refine ⟨0, Submodule.zero_mem _, fun r _ => ?_⟩
    have hq0 : q = 0 := funext fun i => abs_eq_zero.1 (le_antisymm
      ((single_le_sum (fun j _ => abs_nonneg (q j)) (mem_univ i)).trans hq.le) (abs_nonneg _))
    subst hq0
    have e : (fun x : uniqueInfiniteComponent h =>
        (0 : uniqueInfiniteComponent h → ℝ) x - componentSlope (uniqueInfiniteComponent h) 0 x) =
        fun _ => 0 := by
      funext x; simp [componentSlope]
    rw [e, componentBallL2_zero_fun]
    simp
  have hB : 0 < ∑ i, |q i| := lt_of_le_of_ne (sum_nonneg fun _ _ => abs_nonneg _) (Ne.symm hq)
  -- a vertex of the cluster
  have hcard := card_ball_ge_of_quadLocality (uniqueInfiniteComponent h) hd0 hκ hc hXΛ
  have hcard' : (0 : ℝ) < (componentEuclideanBall (uniqueInfiniteComponent h) 0 Xω).card :=
    lt_of_lt_of_le (mul_pos (ballDensityConst_pos hκ) (pow_pos (by linarith) d)) hcard
  obtain ⟨o, -⟩ := Finset.card_pos.1 (by exact_mod_cast hcard')
  obtain ⟨u, hu, hasy⟩ := h₃ h q o
  have hharm : ∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0 := hu.1
  -- (7.18) above `Xω`
  have hmeso : ∀ R, 2 * Xω ≤ R → ∀ r, Xω ≤ r → r ≤ R / 2 →
      (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
          clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) ≤
        A * (r / R) ^ 3 * (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
            clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w)) +
          A * r ^ (-δ) * (r / R) * clusterBallVolumeL2 (uniqueInfiniteComponent h) R u := by
    intro R hR r hr hrR
    have hr1 : 1 ≤ r := hX1.trans hr
    have hh := h₁ h R (by linarith) u (fun z _ _ => hharm z) r (hXX₁.trans hr) hrR
    have hE : 0 ≤ ⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w) :=
      Real.iInf_nonneg fun _ => Real.sqrt_nonneg _
    have hV : 0 ≤ clusterBallVolumeL2 (uniqueInfiniteComponent h) R u := Real.sqrt_nonneg _
    have hrR0 : 0 ≤ r / R := div_nonneg (by linarith) (by linarith)
    have hδr : r ^ (-δ₀) ≤ r ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (neg_le_neg hδδ₀)
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAA₀ (pow_nonneg hrR0 3)) hE
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul hAA₀ hδr (Real.rpow_nonneg (by linarith) _) hA) hrR0) hV
    linarith
  have hexA := excess_two_le_of_slopeAsymptotics (uniqueInfiniteComponent h) hX1 hA hmeso hasy
  have hexc : ∀ r, Xω ≤ r → ∃ w ∈ clusterHarmonicQuadratic (uniqueInfiniteComponent h),
      clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w) ≤
        (A * 5 ^ d + 1) * (∑ i, |q i|) * r ^ (1 - δ) := by
    intro r hr
    have h1 := hexA r hr
    have hr0 : 0 < r ^ (1 - δ) := Real.rpow_pos_of_pos (by linarith) _
    have hlt : (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) <
        (A * 5 ^ d + 1) * (∑ i, |q i|) * r ^ (1 - δ) := by
      have : 0 < (∑ i, |q i|) * r ^ (1 - δ) := mul_pos hB hr0
      nlinarith
    obtain ⟨w, hw⟩ := exists_lt_of_ciInf_lt hlt
    exact ⟨(w : uniqueInfiniteComponent h → ℝ), w.2, hw.le⟩
  obtain ⟨c, hc'⟩ := exists_const_sublinear_of_excess (uniqueInfiniteComponent h) hd0 hκ hc hXΛ
    hδ0 hδ1 (by positivity) hexc hasy
  refine ⟨u - fun _ => c, (harmonicGrowthSpace (uniqueInfiniteComponent h) 1).sub_mem hu
    (const_mem_harmonicGrowthSpace _ 1 c), fun r hr => ?_⟩
  have hr' : Xω ≤ r := hscale r hr
  have h1 := hc' r hr'
  have h2 := componentBallL2_le_of_quadLocality (uniqueInfiniteComponent h) hd0 hκ hc
    (hXΛ.trans hr') (fun x => u x - componentSlope (uniqueInfiniteComponent h) q x - c)
  have e : (fun x : uniqueInfiniteComponent h =>
      (u - (fun _ => c : uniqueInfiniteComponent h → ℝ)) x -
        componentSlope (uniqueInfiniteComponent h) q x) =
      fun x => u x - componentSlope (uniqueInfiniteComponent h) q x - c := by
    funext x; simp only [Pi.sub_apply]; ring
  rw [e]
  calc _ ≤ _ := h2
    _ ≤ Real.sqrt (1 / ballDensityConst d κ) * (sublinearConstD d κ δ *
          ((A * 5 ^ d + 1) * ∑ i, |q i|) * r ^ (1 - δ)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = K * (∑ i, |q i|) * r ^ (1 - δ) := by rw [hK]; ring

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in every dimension**, from the
existence of the corrected planes alone: (7.18) at `k = 2` and the density of the cluster are
proved, and they make the sublinearity of the corrected planes quantitative. -/
theorem armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput
    (hqual : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ArmstrongDarioOrderOneOrigin :=
  armstrongDarioOrderOneOrigin_of_correctorSublinear fun d _ hd p hpc hp1 =>
    correctorSublinearL2At_of_correctedPlanes hd hpc hp1 (by
      filter_upwards [hqual d hd p hpc hp1] with ω hω h q o
      exact ((hω h).1 q o).exists.imp fun _ hu => hu.1)

end Rigidity.Proofs.Regularity
