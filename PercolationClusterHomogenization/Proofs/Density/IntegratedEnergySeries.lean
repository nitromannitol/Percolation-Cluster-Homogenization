import LatticeProb.Prob.StochasticO
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import PercolationClusterHomogenization.Proofs.Density.ConditionalEnergyMoments
import PercolationClusterHomogenization.Proofs.Density.ConditionalProductIntegral
import PercolationClusterHomogenization.Proofs.Density.NormalizedInfluenceEnergyMoments
import PercolationClusterHomogenization.Proofs.Density.NonnegativeIntegralSeries
import PercolationClusterHomogenization.Proofs.Density.NormalizedInfluenceEnergy

/-!
# The integrated resampling energy of the planar density

The individual bond influences of the planar cluster density are integrable in the independent copy,
and their integrals sum to the averaged resampling energy.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Individual bond influences are integrable in the independent copy, and their integrals
sum to the averaged resampling energy almost surely. -/
theorem planar_integrated_density_energy_series (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (m : ℕ) (k : Vertex 2) :
    ∀ᵐ ω ∂(latticeBondLaw 2 p),
      (∀ e : Bond 2, Integrable (fun η : Configuration 2 =>
        |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2) (latticeBondLaw 2 p)) ∧
      Summable (fun e : Bond 2 => ∫ η : Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p)) ∧
      (∫ η, planarDensityResamplingEnergy m k (ω, η) ∂(latticeBondLaw 2 p)) =
        ∑' e : Bond 2, ∫ η : Configuration 2,
          |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p) := by
  let μ := latticeBondLaw 2 p
  let F (e : Bond 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ)| ^ 2
  let G (q : Configuration 2 × Configuration 2) : ℝ≥0∞ := ∑' e, ENNReal.ofReal (F e q)
  have hFm (e : Bond 2) : Measurable (F e) := by
    dsimp only [F]
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    exact (((hF.comp measurable_fst).div_const _).sub
      ((hF.comp hRes).div_const _)).abs.pow_const 2
  have hGm : Measurable G := Measurable.tsum fun e => (hFm e).ennreal_ofReal
  obtain ⟨C, hC, hmean⟩ := planar_normalized_density_resampling_energy_mean p hp
  have hfinite : (∫⁻ q, G q ∂(μ.prod μ)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hmean m k).1)
  have hslice : (∫⁻ ω, ∫⁻ η, G (ω, η) ∂μ ∂μ) ≠ ∞ := by
    rw [← lintegral_prod G hGm.aemeasurable]
    exact hfinite
  filter_upwards [ae_lt_top (hGm.lintegral_prod_right') hslice] with ω hω
  have hseries := integral_tsum_nonnegative μ (fun e η => F e (ω, η))
    (fun e => (hFm e).comp (measurable_const.prodMk measurable_id))
    (fun e η => sq_nonneg _) hω
  simpa only [F, G, planarDensityResamplingEnergy] using hseries

end Rigidity.Proofs.S2

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

end Rigidity.Proofs.S2
