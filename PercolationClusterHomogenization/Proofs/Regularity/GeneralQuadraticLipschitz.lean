import PercolationClusterHomogenization.Proofs.Regularity.GeneralCoarseTransfer
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroInput
import PercolationClusterHomogenization.Proofs.Regularity.PlanarQuadraticLipschitz
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicTwoSteps

/-!
# The slope of a quadratic polynomial on the balls of a cluster of `ℤᵈ`

For `W(y) = a + ⟪p, y⟫ + q_M(y)` on `ℤᵈ` and `|xᵢ|, |yᵢ| ≤ ρ`,
`|W(y) - W(x)| ≤ Λ ∑ᵢ |yᵢ - xᵢ|` with `Λ = ∑ᵢ |pᵢ| + 2 ρ ∑ᵢ ∑ⱼ |(Mᵢⱼ + Mⱼᵢ) / 2|`
(`abs_latticeQuadFunD_sub_le`, `quadSlopeD`). Under the density of the cluster in cubes, the
cluster ball of radius `R` controls these coefficients:
`Λ R ≤ C (inf_c ‖u - c‖_R + ‖u - W‖_R)` for every function `u` on the cluster
(`quadSlopeD_le_of_clusterCubeDensity`), with `‖·‖_R = R^{-d/2} ‖·‖_{ℓ²(C ∩ B_R)}`: the bound
(7.23) of the proof of Lemma 7.3 of Armstrong and Dario (arXiv:1609.09431v2) for the harmonic
quadratic polynomials, from the lower bounds of the excess of quadratic functions over affine
functions (`le_ballExcess_clusterQuadratic`) and of affine functions
(`le_componentBallL2_affine`) on the cluster balls.

The lattice harmonic quadratic functions restrict to the harmonic quadratic polynomials of the
cluster (`mem_clusterHarmonicQuadratic_of_mem_latticeHarmonicQuadraticD`), and the harmonic
quadratic polynomials of the cluster extend to lattice harmonic quadratic functions
(`mem_latticeHarmonicQuadratic_of_trace_eq_zeroD`). These are the planar statements of
`PlanarQuadraticLipschitz` in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- The quadratic polynomial `a + ⟪p, y⟫ + q_M(y)` on `ℤᵈ`. -/
noncomputable def latticeQuadFunD (a : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) (y : Vertex d) : ℝ :=
  a + inner ℝ p (latticeEuclideanEmbedding y) + quadForm M (latticeEuclideanEmbedding y)

theorem latticeLaplacian_latticeQuadFunD (a : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) (y : Vertex d) :
    latticeLaplacian (latticeQuadFunD a p M) y = 2 * M.trace := by
  simp only [latticeLaplacian, latticeQuadFunD, latticeEuclideanEmbedding_add,
    latticeEuclideanEmbedding_sub_unit, latticeEuclideanEmbedding_unit, inner_add_right,
    inner_sub_right]
  have h : ∀ i : Fin d, quadForm M (latticeEuclideanEmbedding y + EuclideanSpace.single i 1) +
      quadForm M (latticeEuclideanEmbedding y - EuclideanSpace.single i 1) -
        2 * quadForm M (latticeEuclideanEmbedding y) = 2 * M i i := fun i => by
    rw [quadForm_add_add_sub, quadForm_single]
  rw [Matrix.trace, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have := h i
  simp only [Matrix.diag]
  linarith

/-- A harmonic quadratic polynomial of the cluster extends to a lattice harmonic quadratic
function. -/
theorem mem_latticeHarmonicQuadratic_of_trace_eq_zeroD [NeZero d] (a : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.trace = 0) :
    (fun x : latticeComponent d => latticeQuadFunD a p M x.val) ∈ latticeHarmonicQuadratic d :=
  ⟨⟨a, p, M, fun _ => rfl⟩, fun y => by
    show latticeLaplacian (latticeQuadFunD a p M) y = 0
    rw [latticeLaplacian_latticeQuadFunD, hM, mul_zero]⟩

/-- A lattice harmonic quadratic function restricts to a harmonic quadratic polynomial of the
cluster. -/
theorem mem_clusterHarmonicQuadratic_of_mem_latticeHarmonicQuadraticD [NeZero d]
    (C : OpenComponent ω) {w : latticeComponent d → ℝ} (hw : w ∈ latticeHarmonicQuadratic d) :
    ∃ (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ),
      (∀ x, w x = latticeQuadFunD a p M x.val) ∧
      (fun x : C => latticeQuadFunD a p M x.val) ∈ clusterHarmonicQuadratic C := by
  obtain ⟨⟨a, p, M, hw'⟩, hΔ⟩ := hw
  have hext : latticeExt w = latticeQuadFunD a p M := by
    funext y; exact hw' _
  have htr : M.trace = 0 := by
    have := hΔ 0
    rw [hext, latticeLaplacian_latticeQuadFunD] at this
    linarith
  exact ⟨a, p, M, fun x => hw' x, ⟨a, p, M, htr, fun _ => rfl⟩⟩

/-- The slope `∑ᵢ |pᵢ| + 2 ρ ∑ᵢ ∑ⱼ |(Mᵢⱼ + Mⱼᵢ) / 2|` of `a + ⟪p, y⟫ + q_M(y)` on the box of
side `ρ`. -/
noncomputable def quadSlopeD (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (ρ : ℝ) : ℝ :=
  ∑ i, |p i| + 2 * ρ * ∑ i, ∑ j, |symEntry M i j|

theorem quadSlopeD_nonneg (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ quadSlopeD p M ρ := by
  unfold quadSlopeD; positivity

theorem quadSlopeD_zero (ρ : ℝ) :
    quadSlopeD (0 : EuclideanSpace ℝ (Fin d)) (0 : Matrix (Fin d) (Fin d) ℝ) ρ = 0 := by
  simp [quadSlopeD, symEntry]

/-- **The slope of a quadratic polynomial on a box.** -/
theorem abs_latticeQuadFunD_sub_le (a : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) {ρ : ℝ} {x y : Vertex d}
    (hx : ∀ i, |(x i : ℝ)| ≤ ρ) (hy : ∀ i, |(y i : ℝ)| ≤ ρ) :
    |latticeQuadFunD a p M y - latticeQuadFunD a p M x| ≤
      quadSlopeD p M ρ * ∑ i, |((y i - x i : ℤ) : ℝ)| := by
  set Δ : Fin d → ℝ := fun i => ((y i - x i : ℤ) : ℝ) with hΔ
  have hΔi : ∀ i, Δ i = (y i : ℝ) - x i := fun i => by simp [hΔ]
  set T := ∑ i, |Δ i| with hT
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ => abs_nonneg _
  have hΔT : ∀ i, |Δ i| ≤ T := fun i =>
    single_le_sum (f := fun i => |Δ i|) (fun _ _ => abs_nonneg _) (mem_univ i)
  have hρ0 : ∀ i : Fin d, 0 ≤ ρ := fun i => (abs_nonneg _).trans (hx i)
  have hemb : ∀ (v : Vertex d) (i : Fin d), (latticeEuclideanEmbedding v) i = (v i : ℝ) :=
    fun v i => rfl
  have e : latticeQuadFunD a p M y - latticeQuadFunD a p M x =
      ∑ i, p i * Δ i + ∑ i, ∑ j, symEntry M i j * (Δ i * (y j : ℝ) + (x i : ℝ) * Δ j) := by
    simp only [latticeQuadFunD, inner_eq_sum, quadForm_eq_symEntry, hemb]
    simp only [hΔi]
    have : ∀ i, ∑ j, symEntry M i j * (y i : ℝ) * y j - ∑ j, symEntry M i j * (x i : ℝ) * x j =
        ∑ j, symEntry M i j * (((y i : ℝ) - x i) * y j + x i * ((y j : ℝ) - x j)) := fun i => by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
    have hlin : ∑ i, p i * (y i : ℝ) - ∑ i, p i * (x i : ℝ) = ∑ i, p i * ((y i : ℝ) - x i) := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
    have hquad : ∑ i, ∑ j, symEntry M i j * (y i : ℝ) * y j -
        ∑ i, ∑ j, symEntry M i j * (x i : ℝ) * x j =
        ∑ i, ∑ j, symEntry M i j * (((y i : ℝ) - x i) * y j + x i * ((y j : ℝ) - x j)) := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun i _ => this i
    linarith
  rw [e]
  have h1 : |∑ i, p i * Δ i| ≤ (∑ i, |p i|) * T := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hΔT i) (abs_nonneg _)
  have h2 : |∑ i, ∑ j, symEntry M i j * (Δ i * (y j : ℝ) + (x i : ℝ) * Δ j)| ≤
      2 * ρ * (∑ i, ∑ j, |symEntry M i j|) * T := by
    have hb : ∀ i j, |symEntry M i j * (Δ i * (y j : ℝ) + (x i : ℝ) * Δ j)| ≤
        2 * ρ * |symEntry M i j| * T := by
      intro i j
      rw [abs_mul]
      have hb : |Δ i * (y j : ℝ) + (x i : ℝ) * Δ j| ≤ 2 * ρ * T := by
        have h3 : |Δ i * (y j : ℝ)| ≤ T * ρ := by
          rw [abs_mul]; exact mul_le_mul (hΔT i) (hy j) (abs_nonneg _) hT0
        have h4 : |(x i : ℝ) * Δ j| ≤ ρ * T := by
          rw [abs_mul]; exact mul_le_mul (hx i) (hΔT j) (abs_nonneg _) (hρ0 i)
        calc _ ≤ |Δ i * (y j : ℝ)| + |(x i : ℝ) * Δ j| := abs_add_le _ _
          _ ≤ T * ρ + ρ * T := add_le_add h3 h4
          _ = 2 * ρ * T := by ring
      calc |symEntry M i j| * |Δ i * (y j : ℝ) + (x i : ℝ) * Δ j|
          ≤ |symEntry M i j| * (2 * ρ * T) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = 2 * ρ * |symEntry M i j| * T := by ring
    calc |∑ i, ∑ j, symEntry M i j * (Δ i * (y j : ℝ) + (x i : ℝ) * Δ j)|
        ≤ ∑ i, |∑ j, symEntry M i j * (Δ i * (y j : ℝ) + (x i : ℝ) * Δ j)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, 2 * ρ * |symEntry M i j| * T :=
          sum_le_sum fun i _ => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => hb i j)
      _ = 2 * ρ * (∑ i, ∑ j, |symEntry M i j|) * T := by simp only [mul_sum, sum_mul]
  calc |∑ i, p i * Δ i + ∑ i, ∑ j, symEntry M i j * (Δ i * (y j : ℝ) + (x i : ℝ) * Δ j)|
      ≤ |∑ i, p i * Δ i| + |∑ i, ∑ j, symEntry M i j * (Δ i * (y j : ℝ) + (x i : ℝ) * Δ j)| :=
        abs_add_le _ _
    _ ≤ (∑ i, |p i|) * T + 2 * ρ * (∑ i, ∑ j, |symEntry M i j|) * T := add_le_add h1 h2
    _ = quadSlopeD p M ρ * T := by rw [quadSlopeD]; ring

/-- The constant of the bound of the slope by the oscillation on the cluster ball. -/
noncomputable def quadSlopeConstD (d : ℕ) (κ : ℝ) : ℝ :=
  (2 * d / Real.sqrt (capFraction d κ) * (1 + d ^ 2 / quadLowerConst d κ (capFraction d κ)) +
      2 * d ^ 2 / quadLowerConst d κ (capFraction d κ)) *
    Real.sqrt (1 / (κ * (2 / (6 * Real.sqrt d + 6)) ^ d))

theorem quadSlopeConstD_nonneg (hd : 0 < d) {κ : ℝ} (hκ : 0 < κ) : 0 ≤ quadSlopeConstD d κ := by
  have hδ : 0 < capFraction d κ := capFraction_pos hd hκ
  have hq : 0 < quadLowerConst d κ (capFraction d κ) := quadLowerConst_pos hd hκ hδ
  unfold quadSlopeConstD; positivity

theorem clusterBallVolumeL2_sub_leD (C : OpenComponent ω) {r : ℝ} (hr : 0 ≤ r) (f g : C → ℝ) :
    clusterBallVolumeL2 C r (f - g) ≤ clusterBallVolumeL2 C r f + clusterBallVolumeL2 C r g := by
  have h := clusterBallVolumeL2_triangle C hr f (-g)
  have e : clusterBallVolumeL2 C r (-g) = clusterBallVolumeL2 C r g := by
    simp [clusterBallVolumeL2]
  rw [sub_eq_add_neg]
  linarith

/-- The constant `2 d / √δ (1 + d² / q) + 2 d² / q` of the slope bound on one cluster ball. -/
noncomputable def quadSlopeBallConst (d : ℕ) (κ : ℝ) : ℝ :=
  2 * d / Real.sqrt (capFraction d κ) * (1 + d ^ 2 / quadLowerConst d κ (capFraction d κ)) +
    2 * d ^ 2 / quadLowerConst d κ (capFraction d κ)

theorem quadSlopeBallConst_nonneg (hd : 0 < d) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ quadSlopeBallConst d κ := by
  have hδ : 0 < capFraction d κ := capFraction_pos hd hκ
  have hq : 0 < quadLowerConst d κ (capFraction d κ) := quadLowerConst_pos hd hκ hδ
  unfold quadSlopeBallConst; positivity

/-- **The coefficients of a quadratic polynomial are bounded by its oscillation on the cluster
ball**, against one constant `c`. -/
theorem quadSlopeD_mul_le_componentBallL2 (C : OpenComponent ω) (hd : 0 < d) {ℓ κ R : ℝ}
    (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓ κ)
    (hR : quadLocality d (capFraction d κ) * max ℓ 1 ≤ R) (a : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) :
    quadSlopeD p M R * R ≤ quadSlopeBallConst d κ *
      componentBallL2 C 0 R (fun x => latticeQuadFunD a p M x.val - c) := by
  classical
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  set δ := capFraction d κ with hδdef
  have hδ : 0 < δ := capFraction_pos hd hκ
  set q := quadLowerConst d κ δ with hqdef
  have hq : 0 < q := quadLowerConst_pos hd hκ hδ
  have hΛ24 := le_quadLocality hd hδ
  have hmax : 1 ≤ max ℓ 1 := le_max_right _ _
  have h24 : 24 * Real.sqrt d * max ℓ 1 ≤ R :=
    (mul_le_mul_of_nonneg_right hΛ24 (by linarith)).trans hR
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) h24
  have hcap : ClusterBallCapDensity C 0 (24 * Real.sqrt d * max ℓ 1) R δ :=
    clusterBallCapDensity_of_clusterCubeDensity C 0 R hd hκ (hcube.of_le C 0 hΛ24)
  have h0 : latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
    ext i
    change (((0 : Vertex d) i : ℤ) : ℝ) = (0 : EuclideanSpace ℝ (Fin d)) i
    simp
  set N := componentBallL2 C 0 R (fun x => latticeQuadFunD a p M x.val - c) with hN
  have hN0 : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  -- the maximal symmetric entry
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  obtain ⟨⟨i₀, j₀⟩, -, hmax'⟩ := Finset.exists_max_image Finset.univ
    (fun ij : Fin d × Fin d => |symEntry M ij.1 ij.2|) hne
  set m := |symEntry M i₀ j₀| with hmdef
  have hm : ∀ i j, |symEntry M i j| ≤ m := fun i j => hmax' (i, j) (Finset.mem_univ _)
  have hm0 : 0 ≤ m := abs_nonneg _
  have hsym : ∑ i, ∑ j, |symEntry M i j| ≤ d ^ 2 * m := by
    calc _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, m := sum_le_sum fun i _ => sum_le_sum fun j _ => hm i j
      _ = d ^ 2 * m := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- the quadratic part
  have hexcess := le_ballExcess_clusterQuadratic C 0 hd hκ hcube hR
    (w := fun x => latticeQuadFunD a p M x.val - c) (a := a - c) (p := p) (M := M)
    (fun x => by simp only [latticeQuadFunD]; ring) hm hmdef.symm
  have hexN : ballExcess (componentBallSeminorm C 0) (clusterAffine C) R
      (fun x => latticeQuadFunD a p M x.val - c) ≤ N := by
    have := ballExcess_le (componentBallSeminorm C 0) (clusterAffine C) (s := R)
      (u := fun x => latticeQuadFunD a p M x.val - c) (clusterAffine C).zero_mem
    rw [sub_zero, componentBallSeminorm_apply] at this
    exact this
  have hmN : m * R ^ 2 ≤ N / q := by
    rw [le_div_iff₀ hq]
    have := hexcess.trans hexN
    have e : q * m * R ^ 2 = m * R ^ 2 * q := by ring
    linarith
  -- the affine part
  have haff := le_componentBallL2_affine C 0 hδ hcap h24 le_rfl hR0 (a - c) p
  simp only [h0, sub_zero] at haff
  have hquad_sup : componentBallL2 C 0 R
      (fun x => quadForm M (latticeEuclideanEmbedding x.val)) ≤ d ^ 2 * m * R ^ 2 := by
    apply componentBallL2_le_of_abs_le _ _ _ (by positivity)
    intro x hx
    rw [quadForm_eq_symEntry]
    have hdx := (mem_componentEuclideanBall _ _ _ _).1 hx
    have hc : ∀ i, |(latticeEuclideanEmbedding x.val) i| ≤ R := fun i => by
      have := (abs_sub_le_dist_latticeEuclideanEmbedding x.val 0 i).trans hdx.le
      simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at this
      exact this
    calc |∑ i, ∑ j, symEntry M i j * (latticeEuclideanEmbedding x.val) i *
          (latticeEuclideanEmbedding x.val) j|
        ≤ ∑ i, ∑ j, |symEntry M i j| * (R * R) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ =>
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_))
          rw [abs_mul, abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hc i) (hc j) (abs_nonneg _) hR0.le)
            (abs_nonneg _)
      _ = (∑ i, ∑ j, |symEntry M i j|) * R ^ 2 := by simp only [sum_mul, sq]
      _ ≤ d ^ 2 * m * R ^ 2 := mul_le_mul_of_nonneg_right hsym (sq_nonneg _)
  have htri : componentBallL2 C 0 R
      (fun x => a - c + inner ℝ p (latticeEuclideanEmbedding x.val)) ≤ N + d ^ 2 * m * R ^ 2 := by
    have e : (fun x : C => a - c + inner ℝ p (latticeEuclideanEmbedding x.val)) =
        (fun x => latticeQuadFunD a p M x.val - c) -
          fun x => quadForm M (latticeEuclideanEmbedding x.val) := by
      funext x; simp only [Pi.sub_apply, latticeQuadFunD]; ring
    have h := map_sub_le_add (componentBallSeminorm C 0 R)
      (fun x => latticeQuadFunD a p M x.val - c)
      (fun x => quadForm M (latticeEuclideanEmbedding x.val))
    rw [← e, componentBallSeminorm_apply, componentBallSeminorm_apply,
      componentBallSeminorm_apply] at h
    linarith
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hp : ‖p‖ * R ≤ 2 / Real.sqrt δ * (N + d ^ 2 * m * R ^ 2) := by
    have h := haff.trans htri
    have e1 : Real.sqrt δ * ((|a - c| + ‖p‖ * R) / 2) =
        (Real.sqrt δ * |a - c| + Real.sqrt δ * (‖p‖ * R)) / 2 := by ring
    rw [e1] at h
    have h1 : 0 ≤ Real.sqrt δ * |a - c| := mul_nonneg hsδ.le (abs_nonneg _)
    have h2 : Real.sqrt δ * (‖p‖ * R) ≤ 2 * (N + d ^ 2 * m * R ^ 2) := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hsδ]
    have e2 : ‖p‖ * R * Real.sqrt δ = Real.sqrt δ * (‖p‖ * R) := by ring
    rw [e2]
    exact h2
  have hpsum : ∑ i, |p i| ≤ d * ‖p‖ := by
    calc ∑ i, |p i| ≤ ∑ _i : Fin d, ‖p‖ := sum_le_sum fun i _ => by
          have := PiLp.norm_apply_le p i
          rwa [Real.norm_eq_abs] at this
      _ = d * ‖p‖ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : quadSlopeD p M R * R =
      (∑ i, |p i|) * R + 2 * (R ^ 2 * ∑ i, ∑ j, |symEntry M i j|) := by
    rw [quadSlopeD]; ring
  have h3 : (∑ i, |p i|) * R ≤ d * (‖p‖ * R) := by
    have := mul_le_mul_of_nonneg_right hpsum hR0.le
    have e : d * ‖p‖ * R = d * (‖p‖ * R) := by ring
    linarith
  have h4 : R ^ 2 * ∑ i, ∑ j, |symEntry M i j| ≤ d ^ 2 * (N / q) := by
    have := mul_le_mul_of_nonneg_left hsym (sq_nonneg R)
    have h5 := mul_le_mul_of_nonneg_left hmN (by positivity : (0 : ℝ) ≤ d ^ 2)
    have e : R ^ 2 * (d ^ 2 * m) = d ^ 2 * (m * R ^ 2) := by ring
    linarith
  have h6 : d * (‖p‖ * R) ≤ d * (2 / Real.sqrt δ * (N + d ^ 2 * (N / q))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine hp.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h5 := mul_le_mul_of_nonneg_left hmN (by positivity : (0 : ℝ) ≤ d ^ 2)
    have e : d ^ 2 * m * R ^ 2 = d ^ 2 * (m * R ^ 2) := by ring
    linarith
  have e2 : quadSlopeBallConst d κ * N =
      d * (2 / Real.sqrt δ * (N + d ^ 2 * (N / q))) + 2 * (d ^ 2 * (N / q)) := by
    rw [quadSlopeBallConst, ← hδdef, ← hqdef]; ring
  rw [e1, e2]
  linarith

/-- **The slope at the top scale**: the bound (7.23) of the coefficients of a quadratic polynomial
by its oscillation on the cluster ball, under the density of the cluster in cubes. -/
theorem quadSlopeD_le_of_clusterCubeDensity (C : OpenComponent ω) (hd : 0 < d) {ℓ κ R : ℝ}
    (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓ κ)
    (hR : quadLocality d (capFraction d κ) * max ℓ 1 ≤ R) (a : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) (u : C → ℝ) :
    quadSlopeD p M R * R ≤ quadSlopeConstD d κ *
      ((⨅ c : ℝ, clusterBallVolumeL2 C R (u - fun _ => c)) +
        clusterBallVolumeL2 C R (u - fun x => latticeQuadFunD a p M x.val)) := by
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hδ : 0 < capFraction d κ := capFraction_pos hd hκ
  have hΛ24 := le_quadLocality hd hδ
  have hmax : 1 ≤ max ℓ 1 := le_max_right _ _
  have h24 : 24 * Real.sqrt d * max ℓ 1 ≤ R :=
    (mul_le_mul_of_nonneg_right hΛ24 (by linarith)).trans hR
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) h24
  have hcube3 := hcube.of_le C 0
    (show 3 * Real.sqrt d + 3 ≤ quadLocality d (capFraction d κ) by linarith)
  have h6 : (6 * Real.sqrt d + 6) * max ℓ 1 ≤ R :=
    (mul_le_mul_of_nonneg_right
      (by linarith : 6 * Real.sqrt d + 6 ≤ quadLocality d (capFraction d κ)) (by linarith)).trans hR
  have hcard := card_ball_ge_of_clusterCubeDensity_pow C hκ.le hcube3 h6
  set κ' := κ * (2 / (6 * Real.sqrt d + 6)) ^ d with hκ'
  have hκ'0 : 0 < κ' := by positivity
  have hN2 := componentBallL2_le_of_card_pow C hR0 hκ'0 hcard
  set Kq := quadSlopeBallConst d κ with hKq
  have hKq0 : 0 ≤ Kq := quadSlopeBallConst_nonneg hd hκ
  set W : C → ℝ := fun x => latticeQuadFunD a p M x.val with hW
  set E := clusterBallVolumeL2 C R (u - W) with hE
  have hs0 : 0 ≤ Real.sqrt (1 / κ') := Real.sqrt_nonneg _
  have key : ∀ c : ℝ, quadSlopeD p M R * R ≤ Kq * Real.sqrt (1 / κ') * E +
      Kq * Real.sqrt (1 / κ') * clusterBallVolumeL2 C R (u - fun _ => c) := by
    intro c
    have h1 := quadSlopeD_mul_le_componentBallL2 C hd hκ hcube hR a p M c
    have hN' := hN2 (fun x => W x - c)
    have e2 : (fun x : C => W x - c) = (u - fun _ => c) - (u - W) := by
      funext x; simp only [Pi.sub_apply]; ring
    have h3 := clusterBallVolumeL2_sub_leD C hR0.le (u - fun _ => c) (u - W)
    rw [← e2] at h3
    calc quadSlopeD p M R * R ≤ Kq * componentBallL2 C 0 R (fun x => W x - c) := h1
      _ ≤ Kq * (Real.sqrt (1 / κ') * (clusterBallVolumeL2 C R (u - fun _ => c) + E)) :=
          mul_le_mul_of_nonneg_left (hN'.trans (mul_le_mul_of_nonneg_left h3 hs0)) hKq0
      _ = _ := by ring
  have := le_add_mul_iInf (by positivity : (0 : ℝ) ≤ Kq * Real.sqrt (1 / κ')) key
  calc _ ≤ Kq * Real.sqrt (1 / κ') * E + Kq * Real.sqrt (1 / κ') *
        ⨅ c : ℝ, clusterBallVolumeL2 C R (u - fun _ => c) := this
    _ = quadSlopeConstD d κ * ((⨅ c : ℝ, clusterBallVolumeL2 C R (u - fun _ => c)) + E) := by
        rw [quadSlopeConstD, ← quadSlopeBallConst, ← hKq, ← hκ']; ring

end Rigidity.Proofs.Regularity
