import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderZeroInput
import LatticeProb.External.GreenColumnExistence
import LatticeProb.External.GreenQuantitative
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.External.SupercriticalBondUniquenessInput
import LatticeProb.Prob.Percolation.ContinuumGreen
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.GreenColumnEvent
import LatticeProb.Prob.Percolation.LSSThinIsIncreasing
import LatticeProb.Prob.Percolation.LatticeBondErgodicity
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.LatticeClusterL2
import LatticeProb.Prob.Percolation.LatticeOrderZeroApproximation
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import LatticeProb.Prob.Percolation.LatticeUniqueClusterEvent
import LatticeProb.Prob.Percolation.OpenGraphTranslation
import LatticeProb.Prob.Strassen.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Connected.Basic
import PercolationClusterHomogenization.Proofs.Lattice.ConfigurationExtension
import PercolationClusterHomogenization.Proofs.Planar.WindingNumber
import PercolationClusterHomogenization.External.CorrectorQuantitative
import PercolationClusterHomogenization.External.PlanarInputs

/-!
# Corrected planes and the dimension of `𝒜₁` in dimension two

The statements `PlanarCorrectedPlaneExistenceTwo` (Armstrong and Dario, Theorem 2 (ii) at `k = 1`)
and `PlanarOrderOneDimensionTwo` (Theorem 2 (i) at `k = 1`, `dim 𝒜₁ ≤ 3`) for the planar infinite
cluster, and the fact that a function on a cluster whose balls have the cap density determines its
slope (`eq_zero_of_slopeAsymptotics_zero`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

/-- Every slope has a corrected plane on the planar infinite cluster (Armstrong–Dario, Theorem 2
(ii) for `k = 1`, with the sublinearity in the uniform norm of Remark 1.1 and (1.22)). -/
def PlanarCorrectedPlaneExistenceTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin 2 → ℝ,
      ∃ u : uniqueInfiniteComponent h → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u

/-- The space `𝒜_1` of the planar infinite cluster has dimension at most three
(Armstrong–Dario, Theorem 2 (i) for `k = 1`). -/
def PlanarOrderOneDimensionTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      FiniteDimensional ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) ∧
        Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) ≤ 3

/-- **A function determines its slope** on a cluster whose balls have the cap density: if the
zero function has slope asymptotics of slope `v`, then `v = 0`. -/
theorem eq_zero_of_slopeAsymptotics_zero {ω : Configuration 2} (C : OpenComponent ω) {X δ : ℝ}
    (hδ : 0 < δ) (hcap : ∀ R : ℝ, ClusterBallCapDensity C 0 X R δ)
    {v : Fin 2 → ℝ} (h : componentSlopeAsymptotics C v (fun _ => (0 : ℝ))) : v = 0 := by
  set p : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 v with hpdef
  have hw : ∀ x : C, componentSlope C v x = 0 + inner ℝ p (latticeEuclideanEmbedding x.val) := by
    intro x
    simp [componentSlope, hpdef, latticeEuclideanEmbedding, PiLp.inner_apply, mul_comm]
  by_contra hv
  have hp : p ≠ 0 := fun h0 => hv (by
    have := congrArg WithLp.ofLp h0
    simpa [hpdef] using this)
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hδs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  obtain ⟨R₀, hR₀, hR⟩ := h (Real.sqrt δ * ‖p‖ / 8) (by positivity)
  set ρ := max R₀ (max X 1) with hρdef
  have hR₀ρ : R₀ ≤ ρ := le_max_left _ _
  have hXρ : X ≤ ρ := (le_max_left _ _).trans (le_max_right _ _)
  have h1ρ : 1 ≤ ρ := (le_max_right _ _).trans (le_max_right _ _)
  have hρ0 : 0 < ρ := by linarith
  have hball : componentBallL2 C 0 ρ (fun x => componentSlope C v x) ≤
      Real.sqrt δ * ‖p‖ / 8 * ρ := by
    refine componentBallL2_le_of_abs_le C 0 ρ (by positivity) fun x hx => ?_
    have := hR ρ hR₀ρ x hx
    simpa using this
  have hexc := le_ballExcess_clusterAffine C 0 hδ.le (hcap ρ) hXρ le_rfl hρ0.le hw
  have hle := ballExcess_le_self (componentBallSeminorm C 0) (clusterConstants C) ρ
    (fun x => componentSlope C v x)
  rw [componentBallSeminorm_apply] at hle
  have hpos : 0 < Real.sqrt δ * ‖p‖ * ρ := by positivity
  nlinarith

end Rigidity.Proofs.Regularity
