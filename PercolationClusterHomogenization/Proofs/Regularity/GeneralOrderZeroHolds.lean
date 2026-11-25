import PercolationClusterHomogenization.Proofs.Regularity.GeneralHarmonicDistAS
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroInput

/-!
# Lemma 7.1 and Theorem 2 (iii) at `k = 0` of Armstrong and Dario in every dimension

For `d ≥ 2` and `p_c(d) < p < 1`, with no further hypothesis: the estimates on triadic cubes of
the proof of Lemma 7.1 (`cubeEstimatesAS_holds`: (7.7) from Theorem 1, the comparison (7.8) and
the bound of Step 2), Lemma 7.1 of Armstrong and Dario (arXiv:1609.09431v2) in dimension `d`
(`cubeHarmonicApproximation_holds`), and the order-zero regularity, Theorem 2 (iii) at `k = 0`,
in the form of the input `LatticeProb.External.ArmstrongDarioOrderZero`
(`armstrongDarioOrderZero_holds`). The planar forms are `planarHarmonicApproximationTwo_holds`
and `armstrongDarioOrderZeroTwo_holds`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

variable {d : ℕ}

/-- **The estimates on cubes of the proof of Lemma 7.1** in dimension `d ≥ 2`, for
`p_c(d) < p < 1`, with `L = 3 √d`. -/
theorem cubeEstimatesAS_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : CubeEstimatesAS d p := by
  have hd0 : 0 < d := by omega
  obtain ⟨s₁, θ₁, C₁, α, hs₁, hθ₁, hC₁, hα, X₁, hX₁m, hX₁0, hX₁os, hae₁⟩ :=
    cubeHarmonicDistAS_holds hd hpc hp1
  obtain ⟨s₂, θ₂, K₂, hs₂, hθ₂, hK₂, X₂, hX₂m, hX₂0, hX₂os, hae₂⟩ :=
    cubeCoarseComparisonAS_holds hd hpc hp1
  obtain ⟨s₃, θ₃, K₃, hs₃, hθ₃, hK₃, X₃, hX₃m, hX₃0, hX₃os, hae₃⟩ :=
    cubeCoarseBoundAS_holds hd hpc hp1
  obtain ⟨θ₁₂, hθ₁₂, h12⟩ := Rigidity.Dirichlet.IsOsBond.exists_max hs₁ hs₂ hθ₁ hθ₂ hX₁m hX₂m
    hX₁os hX₂os
  obtain ⟨θX, hθX, hXos⟩ := Rigidity.Dirichlet.IsOsBond.exists_max (lt_min hs₁ hs₂) hs₃ hθ₁₂ hθ₃
    (hX₁m.max hX₂m) hX₃m h12 hX₃os
  have hsd1 : 1 ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by norm_num) (by positivity), one_pow]; exact_mod_cast hd0
  refine ⟨_, θX, 3 * Real.sqrt d, C₁, K₂, K₃, α, lt_min (lt_min hs₁ hs₂) hs₃, hθX,
    by linarith, by linarith, hC₁, hK₂, hK₃, hα, _, (hX₁m.max hX₂m).max hX₃m,
    fun ω => (hX₁0 ω).trans ((le_max_left _ _).trans (le_max_left _ _)), hXos, ?_⟩
  filter_upwards [hae₁, hae₂, hae₃] with ω hω₁ hω₂ hω₃ h R u hu j hj hjR
  have hj1 : X₁ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_left _ _)).trans hj
  have hj2 : X₂ ω ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_left _ _)).trans hj
  have hj3 : X₃ ω ≤ 3 ^ j := (le_max_right _ _).trans hj
  have h3j : (0 : ℝ) ≤ 3 ^ (j + 3) := by positivity
  have hjR1 : Real.sqrt d * 3 ^ (j + 3) ≤ R := by
    have := mul_nonneg (Real.sqrt_nonneg (d : ℝ)) h3j
    linarith
  have hjR4 : Real.sqrt d * 3 ^ (j + 4) ≤ R := by
    rw [pow_succ]; linarith
  exact ⟨hω₁ h R u hu j hj1 hjR4, hω₂ h R u hu j hj2 hjR1, hω₃ h R u hu j hj3 hjR1⟩

/-- **Armstrong–Dario, Lemma 7.1, in dimension `d ≥ 2`**, with no hypothesis. -/
theorem cubeHarmonicApproximation_holds [NeZero d] (hd : 2 ≤ d) :
    CubeHarmonicApproximation d :=
  cubeHarmonicApproximation_of_cubeEstimates hd (fun _ hpc hp1 => cubeEstimatesAS_holds hd hpc hp1)
    fun _ hpc _ => cubePartitionSizeScale_holds hd hpc

/-- **Armstrong–Dario, Theorem 2 (iii) for `k = 0`, in every dimension `d ≥ 2`**: the order-zero
regularity input `LatticeProb.External.ArmstrongDarioOrderZero`, with no hypothesis. -/
theorem armstrongDarioOrderZero_holds : LatticeProb.External.ArmstrongDarioOrderZero :=
  armstrongDarioOrderZero_of_cubeHarmonicApproximation fun _ _ hd =>
    cubeHarmonicApproximation_holds hd

end Rigidity.Proofs.Regularity
