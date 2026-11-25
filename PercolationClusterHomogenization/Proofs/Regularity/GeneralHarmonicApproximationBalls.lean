import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicApproximation
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationBalls

/-!
# Armstrong–Dario, Lemma 7.1, in every dimension: from triadic cubes to balls

Armstrong and Dario (arXiv:1609.09431v2) prove Lemma 7.1 on the triadic cubes `□_m` and use it on
balls at the start of the proof of Lemma 7.3. On `ℤᵈ`, for a function `f` (the coarsening
`[u]_𝒫`) and nonnegative quantities `Γ_j` (the oscillation of `u` on the cluster of `□_j`), the
proof of Lemma 7.1 gives, for `3^j` above a scale `X₀` and `□_{j + 3}` inside the domain,

* (7.7) `inf_{w ∈ Ā(□_m)} ‖f - w‖_{L̲²(□_m)} ≤ C₁ 3^{-m α} Γ_{m + 3}`;
* the inequality of Step 4, `Γ_j ≤ inf_a ‖f - a‖_{L̲²(□_j)} + K 3^{-j} Γ_{j + 3}`;
* and, on the whole domain `B_R`, `Γ_j ≤ (R / 3^j) B`.

The iteration of Step 4 (`le_sum_squareIterCoeff`) and the comparison of the norms on cubes and
balls give the harmonic approximation hypothesis of Lemma 7.2 on the balls of the lattice with
`E = B / R` (`harmonicApproximation_of_cubes`). This is the argument of
`harmonicApproximation_of_squares` in dimension two; in dimension `d` the ball `B_r`,
`2 r ≤ 3^m < 6 r`, lies in `□_m` and contains `□_{m - d - 2}`, so that the factor between the
norms on `B_r` and on `□_m` is `(3^{d + 2})^{d/2}`, and the oscillation of `f` on `□_i` is
compared with the excess on the ball of radius `max(A r, √d 3^i)`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ} [NeZero d]

/-- **A ball inside a cube**, for the distance to the lattice harmonic functions: if
`B_r ⊆ □_m` and `□_j ⊆ B_r`, the distance on `B_r` is at most `(3^m / 3^j)^{d/2}` times the one
on `□_m`. -/
theorem ballDist_le_cubeHarmonicDist {r : ℝ} {m j : ℕ}
    (hsub : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r →
        y ∈ triadicCubeFinset d m 0)
    (hj : ∀ y ∈ triadicCubeFinset d j 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r)
    (f : Vertex d → ℝ) :
    ballDist (componentBallSeminorm (latticeComponent d) 0) (latticeHarmonicClass 0 r) r
        (fun x : latticeComponent d => f x.val) ≤
      Real.sqrt (((3 : ℝ) ^ m / 3 ^ j) ^ d) * cubeHarmonicDist d m f := by
  haveI : Nonempty (cubeLatticeHarmonic d m) := ⟨⟨0, zero_mem_cubeLatticeHarmonic m⟩⟩
  rw [cubeHarmonicDist, Real.mul_iInf_of_nonneg (Real.sqrt_nonneg _)]
  refine le_ciInf fun F => ?_
  have hv : (fun x : latticeComponent d => F.1 x.val) ∈ latticeHarmonicClass 0 r :=
    ⟨F.1, fun _ => rfl, fun y hy => F.2 y (hsub y hy)⟩
  have hbdd : BddBelow (Set.range fun v : latticeHarmonicClass (0 : Vertex d) r =>
      componentBallSeminorm (latticeComponent d) 0 r
        ((fun x : latticeComponent d => f x.val) - (v : latticeComponent d → ℝ))) :=
    ⟨0, by rintro _ ⟨v, rfl⟩; exact apply_nonneg _ _⟩
  calc ballDist (componentBallSeminorm (latticeComponent d) 0) (latticeHarmonicClass 0 r) r
        (fun x : latticeComponent d => f x.val)
      ≤ componentBallSeminorm (latticeComponent d) 0 r
          ((fun x : latticeComponent d => f x.val) - fun x : latticeComponent d => F.1 x.val) :=
        ciInf_le hbdd ⟨_, hv⟩
    _ = componentBallL2 (latticeComponent d) 0 r
          (fun x : latticeComponent d => (f - F.1) x.val) := rfl
    _ ≤ Real.sqrt (((3 : ℝ) ^ m / 3 ^ j) ^ d) * cubeL2 d m (f - F.1) :=
        componentBallL2_le_cubeL2 hsub hj _

/-- **A cube inside a ball**, for the oscillation: if `□_j ⊆ B_s`, the oscillation on `□_j` is at
most `((2 s + 3) / 3^j)^{d/2}` times the excess over the constants on the lattice ball `B_s`. -/
theorem cubeOsc_le_ballExcess {s : ℝ} {j : ℕ} (hs : 0 ≤ s)
    (hj : ∀ y ∈ triadicCubeFinset d j 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < s)
    (f : Vertex d → ℝ) :
    cubeOsc d j f ≤ Real.sqrt (((2 * s + 3) / 3 ^ j) ^ d) *
      ballExcess (componentBallSeminorm (latticeComponent d) 0)
        (clusterConstants (latticeComponent d)) s (fun x : latticeComponent d => f x.val) := by
  rw [ballExcess, Real.mul_iInf_of_nonneg (Real.sqrt_nonneg _)]
  refine le_ciInf fun w => ?_
  obtain ⟨c, hc⟩ := w.2
  calc cubeOsc d j f ≤ cubeL2 d j (fun y => f y - c) := cubeOsc_le j f c
    _ ≤ Real.sqrt (((2 * s + 3) / 3 ^ j) ^ d) * componentBallL2 (latticeComponent d) 0 s
          (fun x : latticeComponent d => (fun y => f y - c) x.val) :=
        cubeL2_le_componentBallL2 hs hj _
    _ = Real.sqrt (((2 * s + 3) / 3 ^ j) ^ d) * componentBallSeminorm (latticeComponent d) 0 s
          ((fun x : latticeComponent d => f x.val) - (w : latticeComponent d → ℝ)) := by
        rw [componentBallSeminorm_apply]
        congr 2
        funext x
        simp [hc x]

/-- The constant of `cubeOsc_le_of_slope`. -/
noncomputable def cubeSlopeConst (d : ℕ) (A : ℝ) : ℝ :=
  Real.sqrt ((A + 2 * Real.sqrt d + 3) ^ d) * (A / 2 + Real.sqrt d)

theorem cubeSlopeConst_nonneg (d : ℕ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ cubeSlopeConst d A := by
  unfold cubeSlopeConst; positivity

omit [NeZero d] in
/-- The cube `□_i` lies in the ball `B_s` when `√d 3^i ≤ s`. -/
theorem dist_lt_of_mem_cubeFinset_of_le (hd : 0 < d) {i : ℕ} {s : ℝ}
    (hs : Real.sqrt d * 3 ^ i ≤ s) :
    ∀ y ∈ triadicCubeFinset d i 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < s := by
  intro y hy
  have h1 := dist_le_of_mem_cubeFinset hy
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have h3 : (0 : ℝ) < 3 ^ i := by positivity
  have : Real.sqrt d * (3 ^ i / 2) < Real.sqrt d * 3 ^ i := by
    apply mul_lt_mul_of_pos_left _ hsd; linarith
  linarith

/-- The oscillation of `f` on `□_i` against the slopes `ballExcess s / s ≤ S` over the radii
`s ∈ [A r, R]`, for `2 r ≤ 3^i` and `√d 3^i ≤ R`. -/
theorem cubeOsc_le_of_slope {f : Vertex d → ℝ} {A r R S : ℝ} {i : ℕ} (hA : 0 < A) (hr : 0 < r)
    (h2r : 2 * r ≤ 3 ^ i) (hAr : A * r ≤ R) (h3iR : Real.sqrt d * 3 ^ i ≤ R) (hS0 : 0 ≤ S)
    (hS : ∀ s : ℝ, A * r ≤ s → s ≤ R →
      ballExcess (componentBallSeminorm (latticeComponent d) 0)
        (clusterConstants (latticeComponent d)) s (fun x : latticeComponent d => f x.val) ≤
          s * S) :
    cubeOsc d i f ≤ cubeSlopeConst d A * 3 ^ i * S := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h3i : (0 : ℝ) < 3 ^ i := by positivity
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set s := max (A * r) (Real.sqrt d * 3 ^ i) with hsdef
  have hs3 : Real.sqrt d * 3 ^ i ≤ s := le_max_right _ _
  have hs0 : 0 ≤ s := (mul_nonneg hsd h3i.le).trans hs3
  have h1 := cubeOsc_le_ballExcess hs0 (dist_lt_of_mem_cubeFinset_of_le hd hs3) f
  have h2 := hS s (le_max_left _ _) (max_le hAr h3iR)
  have hAr' : A * r ≤ A / 2 * 3 ^ i := by
    have := mul_le_mul_of_nonneg_left h2r hA.le
    linarith
  have hsle : s ≤ (A / 2 + Real.sqrt d) * 3 ^ i := by
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  have h2s : (2 * s + 3) / 3 ^ i ≤ A + 2 * Real.sqrt d + 3 := by
    rw [div_le_iff₀ h3i]
    have h31 : (1 : ℝ) ≤ 3 ^ i := one_le_pow₀ (by norm_num)
    nlinarith
  have hfac : Real.sqrt (((2 * s + 3) / 3 ^ i) ^ d) ≤ Real.sqrt ((A + 2 * Real.sqrt d + 3) ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) h2s d)
  calc cubeOsc d i f
      ≤ Real.sqrt (((2 * s + 3) / 3 ^ i) ^ d) *
          ballExcess (componentBallSeminorm (latticeComponent d) 0)
            (clusterConstants (latticeComponent d)) s
            (fun x : latticeComponent d => f x.val) := h1
    _ ≤ Real.sqrt ((A + 2 * Real.sqrt d + 3) ^ d) * (s * S) :=
        mul_le_mul hfac h2 (ballExcess_nonneg _ _ _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt ((A + 2 * Real.sqrt d + 3) ^ d) * ((A / 2 + Real.sqrt d) * 3 ^ i * S) := by
        gcongr
    _ = cubeSlopeConst d A * 3 ^ i * S := by unfold cubeSlopeConst; ring

omit [NeZero d] in
/-- The sum of the iteration over the cubes `□_{m + 3 + 3 k}`, `k < n`, for terms bounded by
`Q 3^{m + 3 + 3 k} S`. -/
theorem sum_squareIterCoeff_le_of_bound {D : ℕ → ℝ} {Q K S : ℝ} {m n : ℕ} (hK : 0 ≤ K)
    (hS0 : 0 ≤ S) (hQ : 0 ≤ Q) (hKm : 2 * K ≤ 3 ^ m) (hD0 : ∀ k, 0 ≤ D (m + 3 + 3 * k))
    (hD : ∀ k < n, D (m + 3 + 3 * k) ≤ Q * 3 ^ (m + 3 + 3 * k) * S) :
    ∑ k ∈ range n, squareIterCoeff K (m + 3) k * D (m + 3 + 3 * k) ≤
      2 * Q * 3 ^ (m + 3) * S := by
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hq0 : 0 ≤ K / 3 ^ m := by positivity
  have hq : K / 3 ^ m ≤ 1 / 2 := by rw [div_le_iff₀ h3m]; linarith
  have h27 : ∀ k : ℕ, (3 : ℝ) ^ (3 * k) = 27 ^ k := fun k => by rw [pow_mul]; norm_num
  calc ∑ k ∈ range n, squareIterCoeff K (m + 3) k * D (m + 3 + 3 * k)
      ≤ ∑ k ∈ range n, (K / 3 ^ (m + 3)) ^ k * (Q * 3 ^ (m + 3 + 3 * k) * S) :=
        sum_le_sum fun k hk => mul_le_mul (squareIterCoeff_le hK _ _)
          (hD k (mem_range.1 hk)) (hD0 k) (by positivity)
    _ = Q * 3 ^ (m + 3) * S * ∑ k ∈ range n, (K / 3 ^ m) ^ k := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        have e1 : (3 : ℝ) ^ (m + 3 + 3 * k) = 3 ^ (m + 3) * 27 ^ k := by rw [pow_add, h27]
        have e2 : (K / 3 ^ (m + 3)) ^ k = (K / 3 ^ m) ^ k / 27 ^ k := by
          rw [← div_pow]; congr 1; rw [pow_add]; ring
        have h27k : (27 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [e1, e2, show (K / 3 ^ m) ^ k / 27 ^ k * (Q * (3 ^ (m + 3) * 27 ^ k) * S) =
          Q * 3 ^ (m + 3) * S * (K / 3 ^ m) ^ k * (27 ^ k / 27 ^ k) by ring,
          div_self h27k, mul_one]
    _ ≤ Q * 3 ^ (m + 3) * S * 2 :=
        mul_le_mul_of_nonneg_left (sum_pow_le_two hq0 hq n) (by positivity)
    _ = 2 * Q * 3 ^ (m + 3) * S := by ring

/-- The factor `(3^{d + 2})^{d/2}` between the norms on a ball and on a cube containing it. -/
noncomputable def ballCubeFactor (d : ℕ) : ℝ := Real.sqrt (((3 : ℝ) ^ (d + 2)) ^ d)

theorem ballCubeFactor_nonneg (d : ℕ) : 0 ≤ ballCubeFactor d := Real.sqrt_nonneg _

/-- The scale above which `harmonicApproximation_of_cubes` holds. -/
noncomputable def cubeScale (d : ℕ) (A L C₁ K α : ℝ) : ℝ :=
  max K (max (max 1 (Real.sqrt d))
    ((ballCubeFactor d * C₁ * max (324 * cubeSlopeConst d A) (19683 * K * L ^ 2)) ^ (2 / α)))

omit [NeZero d] in
/-- The final bound of `harmonicApproximation_of_cubes`: for `r ≥ 1` above
`(F C₁ max(M₁, M₂))^{2/α}`, `F C₁ r^{-α} (M₁ r S + M₂ E r) ≤ r^{1 - α/2} (S + E)`. -/
theorem factor_mul_le_rpow {F C₁ α r S E M₁ M₂ : ℝ} (hF : 0 ≤ F) (hα : 0 < α) (hC₁ : 0 ≤ C₁)
    (hr : 1 ≤ r) (hS : 0 ≤ S) (hE : 0 ≤ E) (hM₁ : 0 ≤ M₁)
    (hX : (F * C₁ * max M₁ M₂) ^ (2 / α) ≤ r) :
    F * (C₁ / r ^ α * (M₁ * r * S + M₂ * (E * r))) ≤ r ^ (1 - α / 2) * (S + E) := by
  have hr0 : 0 < r := by linarith
  set Cs := F * C₁ * max M₁ M₂ with hCsdef
  have hCs0 : 0 ≤ Cs := mul_nonneg (mul_nonneg hF hC₁) (hM₁.trans (le_max_left _ _))
  have hCsr : Cs ≤ r ^ (α / 2) := by
    have h1 : (Cs ^ (2 / α)) ^ (α / 2) = Cs := by
      rw [← Real.rpow_mul hCs0, show 2 / α * (α / 2) = (1 : ℝ) by field_simp, Real.rpow_one]
    calc Cs = (Cs ^ (2 / α)) ^ (α / 2) := h1.symm
      _ ≤ r ^ (α / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hCs0 _) hX (by positivity)
  have hpow : r ^ (1 - α / 2) = r ^ (α / 2) * (r / r ^ α) := by
    rw [show (1 - α / 2) = α / 2 + (1 - α) by ring, Real.rpow_add hr0, Real.rpow_sub hr0,
      Real.rpow_one]
  have hrr : 0 ≤ r / r ^ α := by positivity
  have hmax : M₁ * S + M₂ * E ≤ max M₁ M₂ * (S + E) := by
    have h1 := mul_le_mul_of_nonneg_right (le_max_left M₁ M₂) hS
    have h2 := mul_le_mul_of_nonneg_right (le_max_right M₁ M₂) hE
    linarith
  calc F * (C₁ / r ^ α * (M₁ * r * S + M₂ * (E * r)))
      = F * C₁ * (r / r ^ α) * (M₁ * S + M₂ * E) := by ring
    _ ≤ F * C₁ * (r / r ^ α) * (max M₁ M₂ * (S + E)) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = Cs * (r / r ^ α) * (S + E) := by rw [hCsdef]; ring
    _ ≤ r ^ (α / 2) * (r / r ^ α) * (S + E) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsr hrr) (by positivity)
    _ = r ^ (1 - α / 2) * (S + E) := by rw [hpow]

omit [NeZero d] in
/-- For `2 r ≤ 3^m < 6 r` and `r ≥ √d`, the cube `□_{m - (d + 2)}` lies in the ball `B_r`. -/
theorem dist_lt_of_mem_cubeFinset_sub {r : ℝ} {m : ℕ} (hr0 : 0 < r) (hrd : Real.sqrt d ≤ r)
    (hm2 : (3 : ℝ) ^ m < 6 * r) :
    ∀ y ∈ triadicCubeFinset d (m - (d + 2)) 0,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r := by
  intro y hy
  have h1 := dist_le_of_mem_cubeFinset hy
  have hsd := sqrt_le_three_pow d
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  rcases Nat.lt_or_ge m (d + 2) with h | h
  · have e : m - (d + 2) = 0 := by omega
    rw [e, pow_zero] at h1
    linarith
  · have e : (3 : ℝ) ^ m = 3 ^ d * 9 * 3 ^ (m - (d + 2)) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_add, ← pow_add]; congr 1; omega
    rw [e] at hm2
    have h3 : (0 : ℝ) < 3 ^ (m - (d + 2)) := by positivity
    have h4 : Real.sqrt d * (3 ^ (m - (d + 2)) / 2) ≤ 3 ^ d * (3 ^ (m - (d + 2)) / 2) :=
      mul_le_mul_of_nonneg_right hsd (by positivity)
    have h5 : (0 : ℝ) < 3 ^ d := by positivity
    nlinarith

omit [NeZero d] in
/-- `(3^m / 3^{m - (d + 2)})^{d/2} ≤ (3^{d + 2})^{d/2}`. -/
theorem sqrt_ratio_le_ballCubeFactor (m : ℕ) :
    Real.sqrt (((3 : ℝ) ^ m / 3 ^ (m - (d + 2))) ^ d) ≤ ballCubeFactor d := by
  apply Real.sqrt_le_sqrt
  apply pow_le_pow_left₀ (by positivity)
  rw [div_le_iff₀ (by positivity), ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- **From cubes to balls** (Armstrong–Dario, proof of Lemma 7.1, Step 4, and the start of the
proof of Lemma 7.3, in dimension `d`). Let `f` be a function on `ℤᵈ` and `Γ_j ≥ 0` real numbers
such that, for `3^j ≥ X₀` and `L 3^{j + 3} ≤ R`,
`inf_{w ∈ Ā(□_j)} ‖f - w‖_{L̲²(□_j)} ≤ C₁ 3^{-j α} Γ_{j + 3}` and
`Γ_j ≤ inf_a ‖f - a‖_{L̲²(□_j)} + K 3^{-j} Γ_{j + 3}`, and `Γ_j ≤ (R / 3^j) B` for `3^j ≥ X₀`
and `L 3^j ≤ R`. Then, for `L ≥ max(1, √d)`, `A ≥ 4374 L` and `X` above `X₀` and `cubeScale`,
`f` satisfies the harmonic approximation hypothesis of Lemma 7.2 on the balls of `ℤᵈ`, with the
lattice harmonic functions, the exponent `α / 2` and `E = B / R`. -/
theorem harmonicApproximation_of_cubes {A L C₁ K α X₀ X R B : ℝ} {f : Vertex d → ℝ}
    {Γ : ℕ → ℝ} (hΓ0 : ∀ j, 0 ≤ Γ j) (hL : 1 ≤ L) (hLd : Real.sqrt d ≤ L) (hA : 4374 * L ≤ A)
    (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hα : 0 < α) (hX₀ : X₀ ≤ X) (hX : cubeScale d A L C₁ K α ≤ X)
    (hB : 0 ≤ B)
    (H1 : ∀ m : ℕ, X₀ ≤ 3 ^ m → L * 3 ^ (m + 3) ≤ R →
      cubeHarmonicDist d m f ≤ C₁ / ((3 : ℝ) ^ m) ^ α * Γ (m + 3))
    (H2 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
      Γ j ≤ cubeOsc d j f + K / 3 ^ j * Γ (j + 3))
    (H3 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ j ≤ R → Γ j ≤ R / 3 ^ j * B) :
    HarmonicApproximation (componentBallSeminorm (latticeComponent d) 0)
      (latticeHarmonicClass 0) (clusterConstants (latticeComponent d)) A (α / 2) X R (B / R)
      (fun x : latticeComponent d => f x.val) := by
  classical
  intro r hXr hrA
  have hXK : K ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 ≤ X :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hX
  have hXd : Real.sqrt d ≤ X :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hX
  have hXC : (ballCubeFactor d * C₁ * max (324 * cubeSlopeConst d A) (19683 * K * L ^ 2)) ^ (2 / α)
      ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hr1 : 1 ≤ r := hX1.trans hXr
  have hr0 : 0 < r := by linarith
  have hL0 : 0 < L := by linarith
  have hA0 : 0 < A := by linarith
  have hRA : A * r ≤ R := by
    rw [le_div_iff₀ hA0] at hrA; linarith
  have hR0 : 0 < R := lt_of_lt_of_le (mul_pos hA0 hr0) hRA
  have h27 : ∀ k : ℕ, (3 : ℝ) ^ (3 * k) = 27 ^ k := fun k => by rw [pow_mul]; norm_num
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near hr1
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  -- the ball `B_r` lies in `□_m` and contains `□_{m - (d + 2)}`
  have hsub : ∀ y : Vertex d,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) < r →
        y ∈ triadicCubeFinset d m 0 := fun y hy => mem_cubeFinset_of_dist_lt (by linarith)
  have hj := dist_lt_of_mem_cubeFinset_sub hr0 (hXd.trans hXr) hm2
  have hdist0 := (ballDist_le_cubeHarmonicDist hsub hj f).trans
    (mul_le_mul_of_nonneg_right (sqrt_ratio_le_ballCubeFactor m) (cubeHarmonicDist_nonneg _ _))
  have hX₀m : X₀ ≤ 3 ^ m := by linarith
  have hKm : 2 * K ≤ 3 ^ m := by linarith
  -- the domain contains `□_{m + 6}`
  have hdom6 : L * 3 ^ (m + 6) ≤ R := by
    have e : (3 : ℝ) ^ (m + 6) = 729 * 3 ^ m := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 729 * L)
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    linarith
  -- the number of steps of the iteration
  have hexn : ∃ n : ℕ, R < L * 3 ^ (m + 3 + 3 * (n + 1)) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / L / 3 ^ (m + 3)) (by norm_num : (1 : ℝ) < 27)
    refine ⟨n, ?_⟩
    have e : (3 : ℝ) ^ (m + 3 + 3 * (n + 1)) = 3 ^ (m + 3) * 27 ^ (n + 1) := by
      rw [pow_add, h27]
    rw [e]
    have h27n : (27 : ℝ) ^ n ≤ 27 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_div, div_lt_iff₀ (by positivity)] at hn
    have := mul_le_mul_of_nonneg_right h27n (by positivity : (0 : ℝ) ≤ L * 3 ^ (m + 3))
    linarith
  obtain ⟨n, hnspec, hnmin⟩ : ∃ n : ℕ, R < L * 3 ^ (m + 3 + 3 * (n + 1)) ∧
      ∀ k < n, ¬ R < L * 3 ^ (m + 3 + 3 * (k + 1)) :=
    ⟨Nat.find hexn, Nat.find_spec hexn, fun k hk => Nat.find_min hexn hk⟩
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    have h0 : n = 0 := by omega
    rw [h0, show m + 3 + 3 * (0 + 1) = m + 6 by ring] at hnspec
    linarith
  have hndom : L * 3 ^ (m + 3 + 3 * n) ≤ R := by
    have h := hnmin (n - 1) (by omega)
    push Not at h
    rwa [show n - 1 + 1 = n by omega] at h
  -- the iteration of Step 4 from `m + 3`
  have hPmono : ∀ i i', i ≤ i' → L * 3 ^ i' ≤ R → L * 3 ^ i ≤ R := fun i i' h hP' =>
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) hL0.le) hP'
  have hiter := le_sum_squareIterCoeff (Γ := Γ) (D := fun i => cubeOsc d i f) hK
    (P := fun i => L * 3 ^ i ≤ R) (m + 3) hPmono (fun i hi hPi => H2 i (hX₀m.trans
      (pow_le_pow_right₀ (by norm_num) (by omega))) hPi) n hndom
  -- the supremum of the slopes
  have hS := bddAbove_ballExcess_div (latticeComponent d) (clusterConstants (latticeComponent d))
    (fun x : latticeComponent d => f x.val) (a := A * r) (R := R) (mul_pos hA0 hr0)
  obtain ⟨S, hSdef⟩ : ∃ S, S = ⨆ s : Set.Icc (A * r) R,
      ballExcess (componentBallSeminorm (latticeComponent d) 0)
        (clusterConstants (latticeComponent d)) s (fun x : latticeComponent d => f x.val) / s :=
    ⟨_, rfl⟩
  have hSs : ∀ s : ℝ, A * r ≤ s → s ≤ R →
      ballExcess (componentBallSeminorm (latticeComponent d) 0)
        (clusterConstants (latticeComponent d)) s (fun x : latticeComponent d => f x.val) ≤
          s * S := by
    intro s hsA hsR
    have hspos : 0 < s := lt_of_lt_of_le (mul_pos hA0 hr0) hsA
    have h := le_ciSup hS ⟨s, hsA, hsR⟩
    rw [← hSdef] at h
    have h' : ballExcess (componentBallSeminorm (latticeComponent d) 0)
        (clusterConstants (latticeComponent d)) s (fun x : latticeComponent d => f x.val) / s ≤
          S := h
    rw [div_le_iff₀ hspos] at h'
    linarith
  have hS0 : 0 ≤ S := by
    have h := le_ciSup hS ⟨A * r, le_rfl, hRA⟩
    rw [← hSdef] at h
    exact (div_nonneg (ballExcess_nonneg _ _ _ _) (mul_pos hA0 hr0).le).trans h
  have hD : ∀ k < n, cubeOsc d (m + 3 + 3 * k) f ≤
      cubeSlopeConst d A * 3 ^ (m + 3 + 3 * k) * S := by
    intro k hk
    have hiR := hPmono (m + 3 + 3 * k) _ (by omega) hndom
    have h3i : (3 : ℝ) ^ m ≤ 3 ^ (m + 3 + 3 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3iR : Real.sqrt d * 3 ^ (m + 3 + 3 * k) ≤ R :=
      (mul_le_mul_of_nonneg_right hLd (by positivity)).trans hiR
    exact cubeOsc_le_of_slope hA0 hr0 (hm1.trans h3i) hRA h3iR hS0 hSs
  have hT1 := sum_squareIterCoeff_le_of_bound (D := fun i => cubeOsc d i f) hK hS0 (cubeSlopeConst_nonneg d hA0.le) hKm
    (fun k => cubeOsc_nonneg _ _) hD
  have hG := H3 (m + 3 + 3 * n) (hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))) hndom
  have hT2 := squareIterCoeff_mul_top_le hK hL0 hB hR0 hn1 hKm hnspec hG
  -- assembling
  have hH1 := H1 m hX₀m (hPmono _ _ (by omega) hndom)
  have hΓ : Γ (m + 3) ≤ 2 * cubeSlopeConst d A * 3 ^ (m + 3) * S + 19683 * K * L ^ 2 * (B / R) := by
    have h := hiter
    linarith
  have h3m3 : (3 : ℝ) ^ (m + 3) ≤ 162 * r := by
    have e : (3 : ℝ) ^ (m + 3) = 27 * 3 ^ m := by ring
    rw [e]; linarith
  have hrα : r ^ α ≤ ((3 : ℝ) ^ m) ^ α := Real.rpow_le_rpow hr0.le (by linarith) hα.le
  have hrαpos : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  have hE0 : 0 ≤ B / R / r := by positivity
  have hcoef : C₁ / ((3 : ℝ) ^ m) ^ α ≤ C₁ / r ^ α := div_le_div_of_nonneg_left hC₁ hrαpos hrα
  have hBR : B / R = B / R / r * r := by
    rw [div_mul_cancel₀ _ hr0.ne']
  have hQ0 := cubeSlopeConst_nonneg d hA0.le
  have hΓ' : Γ (m + 3) ≤ 324 * cubeSlopeConst d A * r * S +
      19683 * K * L ^ 2 * (B / R / r * r) := by
    have : 2 * cubeSlopeConst d A * 3 ^ (m + 3) * S ≤ 2 * cubeSlopeConst d A * (162 * r) * S := by
      gcongr
    rw [← hBR]
    linarith
  have hfin := factor_mul_le_rpow (M₁ := 324 * cubeSlopeConst d A) (M₂ := 19683 * K * L ^ 2)
    (ballCubeFactor_nonneg d) hα hC₁ hr1 hS0 hE0 (by positivity) (hXC.trans hXr)
  rw [hSdef] at hfin
  calc ballDist (componentBallSeminorm (latticeComponent d) 0) (latticeHarmonicClass 0 r) r
        (fun x : latticeComponent d => f x.val)
      ≤ ballCubeFactor d * cubeHarmonicDist d m f := hdist0
    _ ≤ ballCubeFactor d * (C₁ / ((3 : ℝ) ^ m) ^ α * Γ (m + 3)) :=
        mul_le_mul_of_nonneg_left hH1 (ballCubeFactor_nonneg d)
    _ ≤ ballCubeFactor d * (C₁ / r ^ α * (324 * cubeSlopeConst d A * r * S +
          19683 * K * L ^ 2 * (B / R / r * r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hcoef hΓ' (hΓ0 _) (by positivity))
          (ballCubeFactor_nonneg d)
    _ = ballCubeFactor d * (C₁ / r ^ α * (324 * cubeSlopeConst d A * r * (⨆ s : Set.Icc (A * r) R,
          ballExcess (componentBallSeminorm (latticeComponent d) 0)
            (clusterConstants (latticeComponent d)) s (fun x : latticeComponent d => f x.val) / s) +
          19683 * K * L ^ 2 * (B / R / r * r))) := by rw [hSdef]
    _ ≤ _ := hfin

end Rigidity.Proofs.Regularity
