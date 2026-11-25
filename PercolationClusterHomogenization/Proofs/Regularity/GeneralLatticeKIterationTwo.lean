import PercolationClusterHomogenization.Proofs.Regularity.GeneralLatticeCubicComparison
import PercolationClusterHomogenization.Proofs.Regularity.LatticeKIterationTwo

/-!
# Armstrong–Dario, Lemma 7.2 at `k = 2`, for lattice harmonic functions on the balls of `ℤᵈ`

Lemma 7.2 of Armstrong and Dario (arXiv:1609.09431v2), `armstrongDario_lemma_7_2` at `k = 2`, in
the normalized `ℓ²` norms on the balls of `ℤᵈ` (`componentBallSeminorm (latticeComponent d) z`),
with `Ā(B_r)` the lattice harmonic functions on `B_r(z)`, `Ā_2` the lattice harmonic quadratic
functions and `Ā_3` the lattice harmonic cubic polynomials (`latticeHarmonicCubicPoly d`): the
volume comparison and the cap density of the balls of the lattice give the radius monotonicity and
the comparison of affine functions with constants, `polynomialComparison_latticeHarmonicCubicPoly`
the comparison of `Ā_3` with `Ā_2`, and the excess decay of orders one and three of lattice
harmonic functions is proved, so that only the harmonic approximation hypothesis remains
(`armstrongDario_lemma_7_2_two_latticeHarmonicD`). With `R E ≤ ‖u‖_{L̲²(B_R)}` the error term
takes the form of Lemma 7.3 (`armstrongDario_lemma_7_3_two_latticeHarmonicD`). This is
`armstrongDario_lemma_7_2_two_latticeHarmonic` of the plane in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The lower radius of Lemma 7.2 at `k = 2` on the balls of `ℤᵈ`. -/
noncomputable def latticeLemmaScaleCubic (d : ℕ) : ℝ :=
  max (latticeHRScale d) (max (latticeHRScaleCubic d) (max 1 (24 * Real.sqrt d)))

theorem one_le_latticeLemmaScaleCubic (d : ℕ) : 1 ≤ latticeLemmaScaleCubic d :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **Armstrong–Dario, Lemma 7.2 (`k = 2`), for lattice harmonic functions on the balls of
`ℤᵈ`**: only the harmonic approximation hypothesis remains. -/
theorem armstrongDario_lemma_7_2_two_latticeHarmonicD (d : ℕ) [NeZero d] {A α : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vertex d) (R X E : ℝ) (u : latticeComponent d → ℝ),
      latticeLemmaScaleCubic d ≤ X → X ≤ R / A → 0 ≤ E →
      HarmonicApproximation (componentBallSeminorm (latticeComponent d) z)
        (latticeHarmonicClass z) (clusterConstants (latticeComponent d)) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicQuadratic d)
            r u ≤
          C * (r / R) ^ 3 * ballExcess (componentBallSeminorm (latticeComponent d) z)
            (latticeHarmonicQuadratic d) R u +
          C * r ^ (1 - α) * (ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) R u / R + E / r) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  set δ : ℝ := 1 / (5 * (24 * Real.sqrt d)) ^ d with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set K : ℝ := (5 * (6 * Real.sqrt d)) ^ d / 1 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set CP := max (2 / Real.sqrt δ) (cubicCompConst d) with hCP
  set CH := max (latticeHRConst d) (latticeHRConstCubic d) with hCH
  have hCH0 : 0 ≤ CH := (latticeHRConst_nonneg d).trans (le_max_left _ _)
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2.{0} 2 hA hα (γ := (d : ℝ) / 2)
    (CV := Real.sqrt K) (CP := CP) (CH := CH) (by positivity) (Real.sqrt_nonneg K)
    ((by positivity : (0 : ℝ) ≤ 2 / Real.sqrt δ).trans (le_max_left _ _)) hCH0
  refine ⟨C, hC, fun z R X E u hXs hXR hE happ r hr hrR => ?_⟩
  have hX1 : 1 ≤ X := (one_le_latticeLemmaScaleCubic d).trans hXs
  have hX0 : 0 < X := by linarith
  have hXa : latticeHRScale d ≤ X := (le_max_left _ _).trans hXs
  have hXb : latticeHRScaleCubic d ≤ X :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hXs
  have hX24 : 24 * Real.sqrt d ≤ X :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hXs
  have hX8 : 8 * Real.sqrt d ≤ X := by linarith
  have hcube := clusterCubeDensity_latticeComponent z (24 * Real.sqrt d) 1
  have h24 : 24 * Real.sqrt d * max 1 1 ≤ X := by rw [max_self, mul_one]; exact hX24
  have h6 : 6 * Real.sqrt d * max 1 1 ≤ X := by
    rw [max_self, mul_one]; linarith
  have hvol := (clusterBallVolumeComparison_of_clusterCubeDensity (latticeComponent d) z R
    hd one_pos hcube).of_le h6
  have hcap := (clusterBallCapDensity_of_clusterCubeDensity (latticeComponent d) z R
    hd one_pos hcube).of_le h24
  have hmono := radiusMonotone_componentBallSeminorm (latticeComponent d) z hX0 hK0 hvol
  have hpc₁ : PolynomialComparison (componentBallSeminorm (latticeComponent d) z)
      (clusterConstants (latticeComponent d)) (clusterAffine (latticeComponent d)) 1 X R CP :=
    (polynomialComparison_componentBallSeminorm (latticeComponent d) z hX0 hδ0
      hcap).mono_const _ hX0.le (le_max_left _ _)
  have hpc₂ : PolynomialComparison (componentBallSeminorm (latticeComponent d) z)
      (latticeHarmonicQuadratic d) (latticeHarmonicCubicPoly d) (2 + 1) X R CP :=
    ((polynomialComparison_latticeHarmonicCubicPoly z R).of_le _ hX8).mono_const _ hX0.le
      (le_max_right _ _)
  have hreg₁ : HarmonicRegularity (componentBallSeminorm (latticeComponent d) z)
      (latticeHarmonicClass z) (clusterAffine (latticeComponent d)) 1 X R CH :=
    ((harmonicRegularity_latticeHarmonicClass z R).of_le _ hXa).mono_const (le_max_left _ _) hX0
  have hreg₂ : HarmonicRegularity (componentBallSeminorm (latticeComponent d) z)
      (latticeHarmonicClass z) (latticeHarmonicCubicPoly d) (2 + 1) X R CH :=
    ((harmonicRegularity_cubicPoly_latticeHarmonicClass z R).of_le _ hXb).mono_const
      (le_max_right _ _) hX0
  exact h (componentBallSeminorm (latticeComponent d) z) (clusterConstants (latticeComponent d))
    (clusterAffine (latticeComponent d)) (latticeHarmonicQuadratic d) (latticeHarmonicCubicPoly d)
    (latticeHarmonicClass z) R X E u (clusterConstants_le_clusterAffine _)
    latticeHarmonicQuadratic_le_latticeHarmonicCubicPoly hX1 hXR hE hmono hpc₁ hpc₂ hreg₁ hreg₂
    (fun r _ _ => ⟨0, zero_mem_latticeHarmonicClass z r⟩) happ r hr hrR

/-- **Armstrong–Dario, Lemma 7.3 (`k = 2`), for lattice harmonic functions on the balls of
`ℤᵈ`**, in the form `D_2(r) ≤ C (r / R)³ D_2(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}`, under the
harmonic approximation hypothesis with `R E ≤ ‖u‖_{L̲²(B_R)}`. -/
theorem armstrongDario_lemma_7_3_two_latticeHarmonicD (d : ℕ) [NeZero d] {A α : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vertex d) (R X E : ℝ) (u : latticeComponent d → ℝ),
      latticeLemmaScaleCubic d ≤ X → X ≤ R / A → 0 ≤ E →
      R * E ≤ componentBallL2 (latticeComponent d) z R u →
      HarmonicApproximation (componentBallSeminorm (latticeComponent d) z)
        (latticeHarmonicClass z) (clusterConstants (latticeComponent d)) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicQuadratic d)
            r u ≤
          C * (r / R) ^ 3 * ballExcess (componentBallSeminorm (latticeComponent d) z)
            (latticeHarmonicQuadratic d) R u +
          2 * C * r ^ (-α) * (r / R) * componentBallL2 (latticeComponent d) z R u := by
  obtain ⟨C, hC, hlem⟩ := armstrongDario_lemma_7_2_two_latticeHarmonicD d hA hα
  refine ⟨C, hC, fun z R X E u hXs hXR hE hRE happ r hr hrR => ?_⟩
  have h1 := hlem z R X E u hXs hXR hE happ r hr hrR
  have hr1 : 1 ≤ r :=
    ((one_le_latticeLemmaScaleCubic d).trans hXs).trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_componentBallL2 _ z (clusterConstants _) R u) hRE
  linarith

end Rigidity.Proofs.Regularity
