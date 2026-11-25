import PercolationClusterHomogenization.Proofs.Regularity.OrderOneOriginSublinear

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

theorem abs_componentSlope_le (C : OpenComponent ω) (q : Fin d → ℝ) {r : ℝ} {x : C}
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
    have h3 := abs_componentSlope_le C q hx
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

end Rigidity.Proofs.Regularity
